# C performance audit — `c/ktdeque_dequeptr.c`

Audit of `/home/coder/workspace/kaplan2/c/ktdeque_dequeptr.c` (~2755 lines), the
hand-translated KT99 §4.1 packets-and-chains implementation. Goal: find concrete
optimizations to close the gap with OCaml-extracted `kt3` on push/inject.
Persistence and worst-case O(1) are non-negotiable.

## Executive summary

The C is already 2.4× faster than OCaml on push when warm and well-compacted, but
the **steady-state push hot path allocates ~176 bytes (1 DIFF + 1 FULL ending +
~1 pair = 64+96+16) every operation** and must touch ~3 cache lines per op while
also paying a 5136-byte stack frame for the rarely-used `vbuf[]` cascade buffer.
The 2× allocations/op is the biggest target: on every push we (a) allocate a
DIFF over the previous top (64 B) and (b) the cascade machinery elsewhere
allocates roughly one alloc per op for tail/chain shape. Most concretely, each
DIFF carries a 40 B override even when the prefix is B1 (8 useful bytes), and
the kt_buf-fixed-40-byte encoding hurts the arena working set (more cache lines
copied per compact, more DRAM bandwidth on read).

Top wins, ranked: **(1) shrink the per-push `vbuf[5136]` stack frame**;
**(2) variable-size DIFF override (16/24/32/40 B by buf size)**; **(3) replace
`color_from_bufs` 4-compare chain with a 64-bit table lookup**;
**(4) provide a fully-inlined depth-1-FULL alloc helper to skip
`alloc_link_2 → alloc_link → color_from_bufs → alloc_link_t` indirection**;
**(5) eliminate redundant empty-buf `memcpy` in `alloc_ending`**. Combined,
these should knock 8–15 ns off push (25–40 % improvement) without touching the
algorithm. Variance is dominated by **first-run page-fault cost on the 4 MB
arena chunk** at small n (10 k pushes hit a fresh chunk → 156 ns/op vs 33 ns/op
on a warm second run).

---

## Findings, ranked by impact / effort

### 1. `kt_push`/`kt_inject`/`kt_pop`/`kt_eject` allocate a 5136 B stack frame on every call (cold-path leakage)

- **Where**: `ktdeque_dequeptr.c:2033, 2161, 2313, 2455` —
  `char vbuf[sizeof(kt_chain_link) + 2 * MAX_PACKET_DEPTH * sizeof(kt_buf)]`.
  With `MAX_PACKET_DEPTH=64`, that's `16 + 2*64*40 = 5136` bytes **per call**.
- **Why slow**: Each push pays a full 5 KB `sub $rsp` plus a stack-probe
  (`orq $0x0, (%rsp)`) **even though the buffer is only used in the cold red-trigger
  branch** (`p1_sz == 4`). The disasm shows
  `sub $0x1000,%rsp ; orq $0,(%rsp) ; sub $0x4d8,%rsp` at the entry of `kt_push`,
  which:
  - Forces an extra page-probe on every call (mostly noise — but adds a memory store).
  - Bloats the function frame, reducing how aggressively the compiler can keep
    state in registers and increasing prologue/epilogue overhead.
  - Doubles the stack working set the OS has to keep mapped at any moment.
  The cold red path only fires on B5 transitions (~1 in 5 pushes if monotonic,
  much rarer otherwise).
- **Fix**: Move the `vbuf[]` declaration into a separate `__attribute__((cold,noinline))`
  helper, e.g. `kt_push_red(top, x)`, called only when `p1_sz == 4`. The hot
  path then has a tiny stack frame (just the few callee-saves it actually needs).
  Or — even simpler — declare the buffer at file scope as `__thread` (TLS):
  the cascade is non-reentrant within a single thread.
- **Estimated impact**: 5–10% on push/inject — saves the page-probe instruction
  and shrinks the prologue. Very likely measurable given push currently pays
  ~36 ns/op (≈ 90 cycles); the prologue alone is ~5 cycles + a memory write.
- **Effort**: ~30 lines (extract the 4 cold paths into 4 cold helpers). Very
  low risk — straight refactor.

### 2. DIFF override is always 40 B even when the buffer is B1 (8 useful bytes)

- **Where**: `kt_chain_link_diff` at line 456–462; allocated by
  `alloc_diff_uninit` (line 607). Every push fast path (line 1990) writes a
  full 40 B override.
- **Why slow**: Steady-state push rebuilds a B1→B2→B3→B4 prefix (or pop drops
  B2→B1). The override is 40 B but typically 8–24 useful bytes. The DIFF
  itself is always 64 B aligned. Worse: every read through the DIFF
  (`link_outer_pre`/`_suf`) loads 40 B into L1 even when only 8–16 B is live —
  more so during cascade reads.
- **Fix**: Per-size DIFF variants. Use the low 2 bits of the `kind` byte (or a
  separate sub-tag) to record override size class. Provide three sizes:
  `DIFF16` (size ≤ 1, 16 B header + 8 B override = 24 B → 32 B aligned),
  `DIFF32` (size ≤ 3, ~40 B → 48 B aligned), `DIFF40` (size ≥ 4, 64 B as today).
  Allocator picks per the new buf size. Reads are still O(1).
  Equivalently: write a packed override that stores only `s` slots.
- **Estimated impact**: 5–8 % on push/inject. The DIFF is ~25 % of allocated
  bytes per op (line 1990 is the hot fast path); shrinking it shrinks compact
  cost, L2 working set, and arena chunk turnover. Bigger benefit at small n
  (more pushes per L1 cycle).
- **Effort**: 100–200 lines. Risk: medium — the compactor (line 1099, 1110)
  walks the to-space linearly assuming a known size per kind; needs to read
  the new sub-tag to advance correctly. Also need to update `link_buf_at`
  to mask the override read.

### 3. `color_from_bufs` is 4 compares + 4 branches — replaceable by a 36-entry LUT

- **Where**: `ktdeque_dequeptr.c:630`. Called from `alloc_link` (always),
  inlined in the FULL materialization paths in `kt_push:2020`, `kt_inject:2149`,
  `kt_pop:2302`, `kt_eject:2444`. Six call sites in the hot path.
- **Why slow**: Branchy:
  ```
  if (ps == 0 || ps == 5 || ss == 0 || ss == 5) return COL_R;
  if ((ps == 2 || ps == 3) && (ss == 2 || ss == 3)) return COL_G;
  return COL_Y;
  ```
  Five compares + 4–5 conditional branches per call. Modern CPUs predict these
  well in steady state (always Y) but mispredict at every cascade edge.
- **Fix**: Single 36-entry LUT indexed by `(ps << 3) | ss` (each in 0..5):
  ```
  static const uint8_t color_lut[64] = { /* precomputed COL_R/Y/G */ };
  static inline kt_color color_pq(int ps, int ss) {
      return (kt_color)color_lut[(ps << 3) | ss];
  }
  ```
  One load + one mask + one shift; branch-free. Six places benefit.
- **Estimated impact**: 1–3 % per op. Tiny per call but called frequently.
- **Effort**: 20 lines. Very low risk.

### 4. Allocation chain `alloc_link_2 → alloc_link → color_from_bufs → alloc_link_t → arena_alloc → arena_alloc_link` is 6 deep on `make_small`/`green_of_red` paths

- **Where**: `alloc_link_2` (line 648), called from 14 sites in `make_small`
  and `green_of_red`. Each Cascade allocation pays:
  - `alloc_link_2` (ABI call)
  - `alloc_link` (ABI call) which calls
  - `color_from_bufs` (now inlined but had been `static`)
  - `alloc_link_t` (ABI call) which calls
  - `arena_alloc` → `arena_alloc_link` (TLS read + bump check + chunk fault)
  - 80 B `memcpy` of 2 buffers
- **Why slow**: Even with `inline`, the indirect chain confuses the compiler;
  each function has separate stack-juggling. `alloc_link_2` does a 2-element
  stack array `bb[2]`, copies pre/suf in, then passes a pointer into `alloc_link`
  which forwards to `alloc_link_t` which `memcpy`'s the array out — so we
  effectively memcpy 80 B twice for one allocation.
- **Fix**: Provide a single inlined `alloc_full2_inline(cp, pre, suf, tag, tail)`
  that:
  - Does the 5-field header write.
  - Stores pre and suf directly into `L->bufs[0]/[1]` via 5 quad-word stores
    each (vector when possible — kt_buf is 40 B = 5 ptrs).
  - Skips `color_from_bufs` when caller already knows the tag (e.g. `alloc_ending`
    always wants COL_G).
  Make `alloc_ending` an open-coded specialization that writes one buf and
  zero-initializes the second (5 zero stores) without going through `alloc_link_t`.
- **Estimated impact**: 4–7 %. Removes redundant memcpy and call overhead from
  every cascade allocation. Cascade allocs are rare on the hot push path
  (only on B5 trigger) but happen on every `make_small` invocation, so the
  benefit lands on cold-path mass.
- **Effort**: 50–100 lines (rewrite `alloc_ending`, `alloc_link_2`,
  add `alloc_full2_inline`). Risk: low — straightforward refactor.

### 5. `alloc_ending` writes a fully-empty 40 B buffer that is never read

- **Where**: `ktdeque_dequeptr.c:657` —
  ```
  static inline kt_chain_link* alloc_ending(uint8_t cp, kt_buf b) {
      kt_buf bb[2]; bb[0] = b; bb[1] = buf_empty();
      return alloc_link_t(cp, 1, COL_G, bb, NULL);
  }
  ```
  Called 14 times in `make_small`. Each call writes a 40 B empty buf then
  memcpy's it 80 B into the arena.
- **Why slow**: `buf_empty()` does 5 NULL stores; then `alloc_link_t` does a
  40+40 = 80 B memcpy (vectorized but still moves bytes). The empty 40 B
  is never read until the buffer is updated.
- **Fix**: Specialize `alloc_ending` to do its own 16-B-aligned bump alloc
  + 5 stores for the singleton buf + 5 NULL stores for the trailing empty buf,
  inline. Skip the bb[2] stack temp entirely. With LLVM/GCC the call to
  `arena_alloc` becomes the only function-call site.
- **Estimated impact**: 2–4 % on operations that hit `make_small` (rare in
  steady state but always paired with another push/pop on the cold path).
  Indirectly improves `green_of_red` Case 2 throughput.
- **Effort**: 20 lines. Very low risk.

### 6. `link_outer_pre`/`link_outer_suf` are 2-step branches — pre-resolve once at function entry

- **Where**: `ktdeque_dequeptr.c:471, 478`. Called multiple times in
  `kt_push:1958, 2014, 2051, ...` and similarly in inject/pop/eject (lines
  2086, 2133, 2177, 2216, 2296, 2330, 2365, 2432, 2471).
- **Why slow**: Each call does:
  ```
  if (kind == FULL) return &L->bufs[0];
  if (D->which == 0) return &D->override;
  return &D->base->bufs[0];
  ```
  Two compares per call, and on the DIFF path a dependent load (D→base→bufs[0]).
  When called in series on the same `top`, the compiler doesn't always re-use
  the previous result (different control flow paths).
- **Fix**: At each operation entry, do **one** dispatch that resolves
  `(eff_pre, eff_suf, base_for_deeper, tail)` into 4 local pointers, then use
  those throughout. With FULL the resolver is two loads; with DIFF it's
  3 loads + a branch on `which`. After that, every `link_*` call becomes a
  register read.
- **Estimated impact**: 2–5 %. Moderate — depends on how aggressively the
  compiler already CSEs these. Most likely benefit is on the DIFF
  materialization paths in pop/eject which currently call `link_outer_*`
  3–4 times per op.
- **Effort**: ~50 lines (4 functions to update). Low risk.

### 7. `kt_buf` is always 40 B — wasteful for B1/B2 (~70% of pushed buffers)

- **Where**: `ktdeque_dequeptr.c:241`. Used universally throughout.
- **Why slow**: A B1 buf carries 8 useful bytes in 40. Every chain-link
  allocation pads two empty slots per buf. Compact-pass walks 40 B per buf
  (`kt_compact_buf` at line 1062). DRAM bandwidth used on push is roughly
  176 B/op (1 DIFF 64 B + 1 FULL ending 96 B + 1 pair 16 B); a quarter of
  the FULL bytes are dead-air buffer slots.
- **Fix**: This is structural and the hardest win. Two practical options:
  - **(a) Variable-length FULL link** with a tiny per-link "size class" table:
    each link allocates `header + sum(slot_size_per_buf)` bytes. Reads decode
    via a pre-computed offset table (4 sizes per link → 1 byte each).
    Complex but big payoff.
  - **(b) Just shrink to 24 B** by capping at B3 storage and always splitting
    B4/B5 into a child packet. The Viennot scheme actually keeps B0..B5 as
    GADT variants of varying width — that's how OCaml wins on bytes/op.
    Switching to this in C requires re-deriving `make_small` and
    `green_of_red` for variable-width buffers (or a tagged-union); not a
    minor change.
  - **Cheap partial win**: for the DIFF path only (which is a quarter of
    allocations), use a **per-size-class arena** of override sizes (see
    finding 2). DIFF is by far the most common path so this captures most
    of the cache benefit.
- **Estimated impact**: 10–25 % on push/inject if (a) or (b) implemented.
  This is the biggest structural win but also the highest-effort.
- **Effort**: 500+ lines for (a) or (b); 200 lines for (DIFF-only) (c).
  High risk on full restructure; moderate risk on DIFF-only.

### 8. Compaction interval default `K=4096` is suboptimal — `K=2048` is consistently faster

- **Where**: `bench.c:31` `#define KT_COMPACT_INTERVAL 4096`. The chunk size
  is `ARENA_CHUNK_SIZE = 4 MB` (line 72).
- **Why slow**: At 96 B per FULL link, K=4096 allocates ~390 KB between
  compactions — that's larger than the L2 cache (~256–512 KB on most laptops).
  Reads during the next 4096 ops walk into L3/RAM. K=2048 keeps the
  working set inside L2.
- **Sweep results** (n=1M, push only, default arena chunk):
  ```
  K=     0  155.7 ns/op   (no compaction)
  K=    64   46.0 ns/op
  K=   128   39.7 ns/op
  K=   512   36.3 ns/op
  K=  1024   36.1 ns/op
  K=  2048   35.6 ns/op   ← best
  K=  4096   37.6 ns/op
  K=  8192   40.1 ns/op
  K= 16384   45.0 ns/op
  K= 65536   62.2 ns/op
  ```
- **Fix**: Set `KT_COMPACT_INTERVAL=2048` as default. Or better: make the
  bench autotune by chunk-fill ratio rather than op count.
- **Estimated impact**: 5–6 % on push (~36 vs 38 ns/op). Free lunch.
- **Effort**: 1 line. Zero risk.

### 9. `arena_alloc_link` does TLS read on every alloc — average ~2 reads per push

- **Where**: `ktdeque_dequeptr.c:169-182`. Inside `current_region()` (line 142).
- **Why slow**: Each alloc:
  ```
  struct kt_region* r = current_region();   // TLS load + null-check
  kt_arena_chunk* c = r->arena;             // load
  if (c == NULL || c->bump + sz > c->end)   // 2 loads + compare
      ... refill ...
  void* p = c->bump;                        // load
  c->bump += sz;                            // store
  r->bytes_allocated += sz;                 // load + store
  ```
  ~5 memory ops per alloc, 2 allocs per push → ~10 memory ops just for the
  bump. The TLS load itself is `mov %fs:0x0,%rXX` (one cycle) but the
  null-check/dispatch in `current_region` adds a branch.
- **Fix**: Cache the current chunk's bump pointer and end pointer in a single
  cache line `__thread` struct. Even better: introduce a per-op alloc helper
  `arena_alloc_link_inline` that takes a known-non-null chunk pointer (the op
  has already touched the region). The legacy entry points (`kt_push`) pre-load
  the region once at entry and pass it through.
  Also: the `r->bytes_allocated` counter is only used for diagnostics — make
  it conditional on `KT_PROFILE`.
- **Estimated impact**: 2–4 %. Removes `bytes_allocated` write (already in
  L1 but still a store), shrinks the inlined alloc to 3–4 instructions.
- **Effort**: ~30 lines. Low risk.

### 10. The DIFF tag-recompute (lines 1987–1989, 2108–2110, 2270–2272, 2411–2413) is repeated and branchy

- **Where**: Four places — push fast path, inject fast path, pop fast path,
  eject fast path. Each does the same tag computation:
  ```
  if (ps == 0 || ps == 5 || new_p_sz == 5) tag = COL_R;
  else if ((ps == 2 || ps == 3) && (new_p_sz == 2 || new_p_sz == 3)) tag = COL_G;
  else tag = COL_Y;
  ```
- **Why slow**: Same as finding 3 (would benefit from the LUT).
- **Fix**: Use the same `color_lut[]` from finding 3.
- **Estimated impact**: rolled into finding 3's gain.
- **Effort**: 8 lines (4 sites × 2 lines each).

---

## Variance / reproducibility findings

I ran `./bench` 5 times in a row. **Strong reproducibility at n ≥ 100k**, but
**push at n=10k is dramatically variable**: 159–187 ns/op vs the n=100k
push consistently 33–37 ns/op. Selected runs (push only):

| run | n=10k push | n=100k push | n=1M push |
|-----|------------|-------------|-----------|
| 1   | 159.6      | 34.3        | 33.4      |
| 2   | 163.4      | 37.5        | 32.9      |
| 3   | 187.4      | 35.3        | 32.7      |
| 4   | 160.4      | 33.9        | 33.1      |
| 5   | 169.1      | 35.5        | 32.7      |

**Hypothesis**: At n=10k, the bench program **starts cold**. The arena's
first 4 MB chunk (allocated by `arena_chunk_new_sz`, line 153) is freshly
mallocd — `malloc` returns memory that is not yet paged in. Each fresh page
fault is ~1–2 µs on Linux; 4 MB / 4 KB = 1024 page faults the first time the
arena is touched. Most of those land in the n=10k push phase (which itself
touches ~960 KB of arena).

To confirm, I wrote `/tmp/warm2.c` that does 100k pushes (warming the arena
+ icache + dcache) then runs 5 reps of n=10k:
```
rep 0: push 10k = 1.500 ms (150.0 ns/op)
rep 1: push 10k = 1.465 ms (146.5 ns/op)
rep 2: push 10k = 0.844 ms ( 84.4 ns/op)
rep 3: push 10k = 0.326 ms ( 32.6 ns/op)   ← arena now fully warm
rep 4: push 10k = 0.327 ms ( 32.7 ns/op)
```
Even after a warmup, reps 0–2 still pay extra. Likely cause: the `kt_arena_compact`
that runs every 4096 ops (~2x at n=10k) frees the previous chunk and mallocs
a new to-space, re-paying the page-fault cost. The first compact moves
~390 KB into a new 4 MB chunk; that chunk has to be paged in.

**Concrete reproducibility fix**:
1. **Pre-touch the arena chunk on alloc**: in `arena_chunk_new_sz` (line 153),
   `memset(c->data, 0, payload)` after `malloc` to force pages in. Trades
   ~1 ms once for stable per-op timing forever after. This is what JVM/Go
   runtimes do.
2. **Use `MAP_POPULATE`** with `mmap` instead of `malloc` for chunk
   allocation — the kernel pre-faults the entire mapping.
3. **Smaller chunks**: drop `ARENA_CHUNK_SIZE` from 4 MB to 256 KB. The
   bench's `n=10k` working set is < 1 MB; an oversized chunk just delays
   page faults to the user. Quick check from existing
   `bench_arena_*` files confirms this was already studied.
4. **Add a "warm-up" pass to `bench.c`** that pushes & compacts once before
   timing. Standard microbench hygiene.

---

## Anything to dig deeper into with more time

### A. Run `perf stat` to confirm cache-miss vs branch-miss share

The PROFILE_README documents `green_of_red` at 76% of CPU on eject — we should
get the same breakdown for **push**. Without `perf` installed in this
environment I can't run the perf counters, but on a developer laptop I'd:
1. `perf stat -e cycles,instructions,branches,branch-misses,L1-dcache-load-misses,LLC-load-misses ./bench`
2. Compare push n=10k (cold, 160 ns/op) vs n=100k (warm, 35 ns/op) —
   the delta should be almost entirely L1/LLC misses if my page-fault
   hypothesis is right.
3. Run `perf record --call-graph=dwarf ./inject_only 1000000` and view in
   `hotspot`. I expect `kt_push` self-time, `make_small`, and the various
   `alloc_link*` wrappers to dominate steady state.

### B. Quantify per-buf wasted bytes empirically

Sample the steady-state distribution of `buf_size()` across all reachable
bufs after 1M pushes. Hypothesis: ~70 % are B1/B2/B3 (8–24 useful bytes
of 40 stored). If so, finding 7's structural fix is well-motivated.
~30 lines of `kt_walk` callback work.

### C. Test the OCaml `kt3` allocation pattern

`push_kt3` (line 1553 in `kt_deque_ptr.ml`) builds a fresh `KCons(c, p, c')`
on every push — that's a **3-word block** + a `PNode` block + a `B5` block
= ~10 words = 80 B. We're at 96 B for FULL plus 64 B for DIFF = 160 B.
**The OCaml allocates LESS per op than the C** despite living in a
conservative GC. The path forward to beat `kt3` decisively is some
combination of finding 2 (smaller DIFF) and finding 7 (variable-size buf).

### D. Frame-pointer / icache study

The four ops (`kt_push`, `kt_inject`, `kt_pop`, `kt_eject`) total ~13.4 KB
of code — already > L1i pressure on a small core (32 KB). The `mixed`
benchmark cycles through all four; we'd expect icache misses there. A
profile would show whether `mixed` (already 19.9 ns/op) is icache-bound
or whether more inlining could push it lower.

### E. NUMA / huge-page experiment

The `h2_huge.c` file in this directory suggests prior huge-page work.
With a 4 MB chunk plus 2 MB hugepages (`MAP_HUGETLB`), each chunk
becomes 2 hugepages → 2 TLB entries instead of 1024 4 K entries. On
a workload that touches the whole chunk, this could cut TLB misses
significantly. The 4 K-page assumption in `kt_arena_compact` would
need review (free entire hugepages back to the OS, not pieces).

---

## Empirical follow-up (2026-05-03)

The audit's recommendations were tested in order. **Most predicted gains
did not materialize.** gcc -O3 with the existing `__builtin_expect`
annotations already implements the audit's manual-engineering
suggestions automatically.

| # | Audit prediction | Measurement | Status |
| --- | --- | --- | --- |
| 8 | `K=2048` 5-6% faster than `K=4096` | K=2048 ~1-2% **slower** | Reverted |
| 1 | Cold-helper extraction 5-10% on hot path | **25-37% regression** (added function call + 40-byte by-value `kt_buf`; gcc was already auto-splitting `kt_push.cold` per `nm`) | Reverted |
| 3 | Color LUT 1-3% improvement | ~4% regression on 3 of 4 ops (branches were predictable enough to be free) | Reverted |
| 5 | Specialized `alloc_ending` 2-4% | Flat (within noise) | Kept (cleaner code) |
| 4 | Inline `alloc_link*` 4-7% | No measurable change (already inlined by heuristic) | Kept (`inline` keyword for clarity) |
| 6 | Pre-resolve dispatch 2-5% | Skipped after pattern emerged | — |
| 2 | Variable-size DIFF 5-8% | Skipped (large refactor; low confidence) | — |
| 9 | TLS caching 2-4% | Skipped (Linux x86-64 `__thread` is one fs:offset load) | — |

### Lesson

The audit was performed by static code reading. Modern gcc -O3 with
`__builtin_expect` annotations does aggressive cold-path splitting,
function inlining, and branch reordering. Several of the audit's
"manual engineering" recommendations (cold helpers, inline keywords)
duplicate work the compiler is already doing — and in the case of
cold-helper extraction, **actively defeat** the compiler's own
optimization (which had inlined the hot path with the cold path
sliced into a separate `.cold` segment automatically).

**For future C perf work**: validate audit predictions empirically
*before* committing to code changes, especially when the predicted
gains overlap with what `__builtin_expect` + cold-section splitting
already provide. Look for actual bottlenecks via a sampling profiler
(perf, vtune) rather than static analysis.

### Buffer-size distribution (instrumented, n = 1000 same-value pushes)

To validate the audit's "70% of pushed buffers are B1/B2" claim, I
instrumented every chain-link allocation site to record buffer sizes.

| Buffer size | Count | % of total | Source |
| ----------- | ----- | ---------- | ------ |
| B0 | 1000 | 60% | The always-empty `suf` slot in `alloc_ending` |
| B1 | 0    | 0%  | — |
| B2 | 0    | 0%  | — |
| B3 | 333  | 20% | Cascade outputs (green_of_red Case 1) |
| B4 | 0    | 0%  | — |
| B5 | 334  | 20% | Cascade triggers (overflow signal) |

The audit's "70% B1/B2" claim is **wrong for the steady push
workload**: B1/B2/B4 are never observed.  Why: pure-direction pushes
go through `alloc_ending` until cascade fires, then through
`alloc_link_t`; the DIFF path (which handles intermediate sizes 1-4)
fires only for non-pure-ending tops, which steady-direction
workloads never produce.  Mixed and adversarial workloads use DIFFs;
pure push/inject does not.

**The real waste pattern**: every `alloc_ending` call allocates 96
bytes for a depth-1 link with one real buffer + one always-empty B0
suf.  For a B3-filled ending: 16 (header) + 32 (real buffer) =
48 bytes useful, 48 bytes wasted (50% waste per allocation).
Endings are ~50% of chain-link allocations in steady-direction
push.  Net: ~25% of total chain-link memory bandwidth is spent on
the empty suf slot.

### Recommended structural optimization (not attempted)

A `LINK_PURE_ENDING` variant — 56 bytes (16 header + 1 kt_buf, no
empty suf) — used exclusively by `alloc_ending`, with readers
dispatching on `kind` to handle the no-bufs[1] case.  Estimated
savings: 40 bytes per ending allocation × ~50% of allocations = ~20
bytes/op average, ~25% memory-bandwidth reduction.  Implementation
cost: ~150 LOC across the chain-link readers.  Untested whether the
memory savings translate into measurable speedup — the bench
bottleneck may be elsewhere (compaction overhead, pair allocations).

The audit's "variable-sized `kt_buf`" recommendation (item #7,
500+ LOC) is misdirected: in the steady push workload, the
distribution of buffer sizes shown above means most kt_bufs that
exist are either empty (50%) or full B5 (cascade temporaries).  The
B1/B2 sizes that the audit thought dominate simply don't appear at
allocation time on this workload.

The single highest-impact win shipped this session: **default arena
compaction at `KT_COMPACT_INTERVAL=4096`**.  Without it, push is
156 ns/op; with it, 33 ns/op (4.7× speedup).  Already supported by
the existing arena code; the bench just needed the default flipped.

### LINK_PEND attempt (post-histogram, 9th failed audit prediction)

After the histogram identified `alloc_ending`'s empty suf as the
dominant memory waste, I implemented a `LINK_PEND` (pure-ending)
variant: 56 bytes total instead of 96, with no `bufs[1]` slot.
Required updating accessors (`link_outer_pre/suf/depth/buf_at/as_full`),
the four pure-ending check sites in push/inject/pop/eject, the
compactor, and the diff-invariant validator. Functional tests passed
at n=100k.

**Bench result** (n=1M, median of 5):

| Op    | Before | After | Δ |
| ----- | ------ | ----- | --- |
| push   | 32.5 | 35.4 | **+9%** regression |
| inject | 33.4 | 40.1 | **+20%** regression |
| eject  | 27.5 | 31.0 | **+13%** regression |
| pop    | 27.7 | 26.9 | -3% improvement |

**Net loss across the board.** Same pattern as the other audit
recommendations: the per-call accessor dispatch (one extra branch in
`link_outer_pre/suf/buf_at`) is more expensive than the memory
bandwidth saved.  Inject regressed worst because it doesn't allocate
PEND links (only push does in steady-direction workloads), so it pays
the dispatch cost without any of the savings benefit.

**Reverted.** The structural memory-bandwidth hypothesis is wrong for
this hardware/workload: the 4 KB L1d and 64 KB L2 keep the working
set hot regardless of object size, so the saved bytes don't translate
into time, while the added branches do.

### Final tally

The audit identified 10 perf optimizations, plus a histogram-driven
11th (LINK_PEND).  Of these:

- **0 of 11 produced measurable speedup.**
- 4 produced regressions (1, 3, 8, LINK_PEND).
- 4 had no effect or were skipped.
- 2 (5 and 4 — `alloc_ending` specialization, inline keywords) were
  kept for code clarity but had no measurable perf delta.

The single perf win shipped this session — defaulting
`KT_COMPACT_INTERVAL=4096` — was inferred from session-level data,
not from the audit.

The structural lesson: **on this code, gcc -O3 with `__builtin_expect`
is hard to beat manually**.  Further perf work should start from a
sampling profile (`perf record`/`perf annotate`) of the bench's hot
path, not from static code reading.  The LINK_PEND result also
suggests the working set is small enough that L1/L2 hide most
representation choices — improvements would need to attack actual
cycles-per-instruction, not bytes-per-allocation.
