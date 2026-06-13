# ktdeque: implementations and head-to-head numbers

This file documents the C implementation of the Kaplan–Tarjan
worst-case-O(1) persistent deque, side-by-side with the two OCaml
baselines that are vendored in this repo.

## The three implementations

| Name | Language | Provenance | Worst-case bound |
|------|----------|------------|------------------|
| **`c/src/ktdeque_dequeptr.c`** | C    | KT99 §4.1 stack-of-substacks / VWGP packets-and-chains in C | **O(1)** worst case (empirically verified by `wc_test`) |
| **KTDeque (extracted)** (`ocaml/extracted/`)   | OCaml | `Coq → OCaml` extraction of the verified imperative DSL in `rocq/KTDeque/DequePtr/`.  Bench drivers use the [`push_kt2 / pop_kt2 / inject_kt2 / eject_kt2`] family (the bounded-cascade entry points). | **O(1)** worst case (proven sequence-preserving in `OpsKTSeq.v`) |
| **Viennot OCaml**        | OCaml | Vendored from VWGP (`ocaml/bench/viennot/deque{,_core}.ml`) | **O(1)** worst case (GADT type-level regularity + real-time path) |

## Worst-case allocation bound (C side)

The C implementation's worst-case allocation bound is empirically
verified by `c/tests/wc_test.c`:

```
workload n = 100000 (500000 ops, mixing monotonic push/inject and tight push/pop)
  max packets / op: 4
  max links   / op: 0
  max pairs   / op: 4
  max bufs    / op: 0
  total       / op: 8
```

These maxima are **flat across n = 1k, 10k, 100k** — the per-op bound
does not grow with deque size.  The structural argument: the
regularity invariant ensures that each operation modifies at most the
top packet's outermost buffer + (in the green_of_red cascade) the
topmost-G level + the immediately above; path-copy is bounded by a
constant chain head.

## Performance — n = 1,000,000, ns/op

*Last measured: 2026-05-06, gcc 13.3.0, OCaml 5.4.1, single core.*

The C is built two ways to expose the cost of arena compaction:
`-DKT_COMPACT_INTERVAL=0` disables it (every link allocated from a
non-compacted bump arena), and `-DKT_COMPACT_INTERVAL=4096` runs the
compactor every 4096 ops.  `make bench` defaults to the K=4096 build.

| Op      | **C, K=4096 (default)** | C, K=0 | KTDeque OCaml (`kt2`) | Viennot OCaml | C(K=4096) vs Viennot |
|---------|------------------------:|-------:|-----------------------:|--------------:|---------------------:|
| push    |              **32.6**   | 152.5  |          79.3          |     83.4      | **2.56× faster**     |
| inject  |              **36.6**   | 155.0  |          65.8          |     69.7      | **1.90× faster**     |
| pop     |              **27.2**   | 145.2  |          53.4          |     51.5      | **1.89× faster**     |
| eject   |              **27.2**   | 146.6  |          46.6          |     44.9      | **1.65× faster**     |
| mixed*  |              **19.1**   |  83.2  |          48.9          |     54.6      | **2.86× faster**     |

*mixed = `(push, push, pop)` interleaved at constant size, ns / total op count.

### Reading the numbers

1. **Compaction is load-bearing for the C.**  K=4096 is **4.4×–5.4×
   faster** than K=0 on every op.  Without it, the bump arena
   fragments under sustained workloads and the cache thrashes; the C
   drops to **1.5×–3.4× slower** than Viennot OCaml.  Don't ship K=0.

2. **With compaction, C beats Viennot OCaml on every workload by
   ~1.5×–~2.9×.**  Mixed and push are the biggest wins (close to 3×);
   eject is the smallest (~1.65×).

3. **KTDeque OCaml (`kt2`) is roughly tied with Viennot OCaml.**  The
   verified extraction is within ±10% of Viennot on every op (slightly
   faster on push / inject / mixed; slightly slower on pop / eject).
   This is a fair comparison because both columns implement the same
   algorithm class — purely-functional WC O(1) — and run in the same
   OCaml runtime.  The extracted code carries some structural
   overhead (Coq's `option` / `chain` ADTs are not flattened by the
   extractor) which the hand-tuned Viennot deque avoids; the
   compensating factor is that KT2 has fewer GADT indirections.

4. **All three implementations scale linearly with N.**  Per-op cost
   is roughly constant across sizes 10k / 100k / 1M.  No quadratic
   blowup; no log-n drift on adversarial workloads (verified
   separately by `wc_test`).

5. **The C structural overhead vs. Viennot OCaml.**  The C's
   region-bump allocator is `load-add-compare-store-load` (four
   instructions on the fast path).  OCaml's `caml_alloc_small` is
   `young_ptr -= n; if (young_ptr < young_limit) gc()` (two
   instructions).  Compaction makes the difference because it lets the
   region bump pointer stay in a tight range that fits cache, masking
   the extra instruction.

## Design notes

The structural choices that make the C worst-case O(1) and (mostly) fast:

1. **Packets-and-chains** representation, exactly mirroring VWGP's GADT
   (which is itself the type-level encoding of KT99 §4.1's stack-of-
   substacks).  This is, to our knowledge, the only representation that
   achieves worst-case O(1) per op for the four §4 deque operations
   while staying purely functional.

2. **Regularity invariant** maintained by the chain-link tags: `Y` chains
   must be followed by `G`, `R` chains must be followed by `G`.  This
   bounds `green_of_red`'s cascade to a single chain transition.

3. **Tagged-pointer chain encoding** — `kt_chain` is a `void*` whose low
   bit distinguishes `kt_link*` (bit 0 = 0) from `kt_buf*` Ending
   (bit 0 = 1).  Eliminates the allocation that an `Ending` wrapper would
   require.

4. **Packed link** — the regularity tag is encoded in the low 2 bits of
   the packet pointer inside `kt_link`, so `sizeof(kt_link) == 16` bytes.

5. **Bare element pointers** — `kt_elem == void*`; the element's level is
   threaded through the chain depth, no runtime tag.

6. **Variable-size buffer cells** — `kt_buf` uses a flexible array; cells
   take exactly the bytes needed (B2 = 24 B, B5 = 48 B), allocated from
   per-size bump arenas.

7. **Combined packet+link allocation** for `make_yellow` / `make_red` —
   one 40-byte bump instead of two separate allocations.

8. **Per-type bump arenas** — packets/links, pairs, and per-size buffers
   each in their own region.  Allocation is `top += size; if (top > end)
   refill()`, two instructions on the fast path.

## Known gaps

- **No-compaction regime is allocation-bound.**  At `K=0` (compaction
  disabled) the C is 1.5×–3.4× slower than Viennot OCaml.  Don't
  ship K=0; the recommended config is the K=4096 default.
- **Rocq refinement of the packet/chain layout.** The Rocq side has
  only depth-1 packet refinement. The packet/chain representation in
  this C has no Rocq counterpart at packet depth ≥ 2; closing that
  gap requires extending `chain_repr_at` to allow
  `pcell_inner = Some _` and re-proving the refinement theorems
  (see ADR-0012).

## Catenable (§6) C port — `c/src/ktcadeque.c`

The catenable deque (`kc_push/inject/pop/eject/concat`, header
`include/ktcadeque.h`) is a hand-written C port of the KT99 §6 algorithm
in the form of the machine-checked production op web
`rocq/KTDeque/Catenable/FlatChain.v` + `FlatOps.v` (six keystone
theorems + the constant cost bound closed under the global context).
Its prefix/suffix buffers are §4 C deques (`ktdeque.h`), exactly as the
extracted OCaml artifact's buffers are the verified §4 chain.

**Correctness** is established by a deterministic differential
(`make run-diff-cadeque`): the C port and the Coq-extracted
`KTFlatCadeque` run an identical multi-register workload
(push/inject/pop/eject/concat) and their per-slot sequences are
`diff`'d — **zero divergence across 24 seed/size runs to n = 2×10⁵ plus
register-count variations**, ASan/UBSan clean.  The port is validated
against the verified artifact, not formally refined from it.

**Performance — n = 1,000,000, ns/op** (taskset-pinned; OCaml columns
from `bench/results/cadeque-compare-*.md`):

| Workload    | **C (§6)** | KTf OCaml | Viennot OCaml |
|-------------|-----------:|----------:|--------------:|
| push        |     **96** |     89    |      96       |
| inject      |     **96** |     89    |      97       |
| pop drain   |     **89** |     61    |      78       |
| eject drain |     **91** |     59    |      75       |
| mixed       |     **76** |     46    |      76       |
| concat-fold |    **215** |    146    |    1174       |
| concat-tree |   **1418** |   1425    |    3166       |
| interleave  |    **282** |     91    |     277       |
| fork        |    **100** |     42    |      67       |

(C column: unboxed ground + caller-driven `kc_arena_compact` every 4096
ops — the recommended config, mirroring the §4 deque's `K=4096`.  Without
compaction, the per-element ops are ~2.3× slower; see below.)

Reading the numbers honestly:

- **Competitive across the board.**  With unboxed ground cells and
  caller-driven compaction, the C **matches Viennot on
  push/inject/mixed/interleave** (96 vs 96, 96 vs 97, 76 vs 76, 282 vs
  277), **beats it 2–5.5× on the concat workloads** (concat-fold 215 vs
  1174, concat-tree 1418 vs 3166), and **trails only on pop/eject**
  (~1.1–1.2×) **and the persistent fork** (1.5×).
- **Compaction is the lever, as it is for the §4 deque.**  A profile of
  the no-compaction regime showed ~40% of pure-push time in kernel
  page-fault / `malloc` handling, from the never-reclaimed growth (5.9 GB
  at n=8×10⁶) — i.e. the gap to the GC'd OCaml artifact was that OCaml
  reclaims dead versions for free.  `kc_arena_compact` (below) reclaims
  them on the C side, taking push from 217 → 96 ns/op.
- **pop/eject/fork still trail** (~1.1–1.5×): draining and read-only
  repeated-pop create less reclaimable garbage, so compaction helps them
  less, and the spine node allocated per op remains.
### Optimization: unboxed ground cells

Stored cells use a tagged handle (the §6 analogue of the OCaml `Sraw`
zero-box carrier): a ground element is stored **unboxed — the element
itself, with no per-element allocation** — while the rarer `small`/`big`
cells are heap boxes tagged in bit&nbsp;63 (which survives the §4
buffer's low-3-bit size tag).  This removed one `malloc` per pushed
element and ~14% of retained bytes/element (462&nbsp;→&nbsp;398&nbsp;B/elt),
buying ~15–20% on its own — and (more importantly) it lets compaction's
collection skip the element-walk for buffers known to hold only unboxed
ground cells (a per-buffer flag), which is what makes periodic
compaction cheap (below).  It tightens the §6 element contract to match
the §4 deque's: **stored elements must be 8-byte aligned** (low 3 bits
zero) — already the documented contract in `ktcadeque.h`.

### Compaction (`kc_arena_compact`)

The §6 prefix/suffix buffers are §4 deques in a bump arena that is never
reclaimed automatically, so a long-running program retains dead buffer
versions.  `kc_arena_compact(roots, n)` (same root-enumeration contract
as `kt_arena_compact`) traces every live §4 buffer — outer node buffers
plus those nested in `SSmall`/`SBig` stored cells — copies them forward,
and releases the rest.  It is **sequence-preserving and verified by the
differential** (the C-with-periodic-compaction workload matches the
OCaml extraction exactly, ASan/UBSan clean).

**Collection cost** is the subtlety.  A naive trace must `kt_walk` every
buffer to find §4 deques nested in `SSmall`/`SBig` cells — O(live
elements) per call, which made early compaction a net *loss* on
pure-push.  The fix: each buffer carries a one-bit "holds a boxed cell"
flag (set when a box handle is stored), so the trace skips the
element-walk for the all-ground buffers that dominate
push/inject/pop/eject workloads.  Collection then costs O(spine +
live buffers), and the §4 link copy is the same cheap pass the standalone
§4 deque already uses.

With caller-driven compaction every 4096 ops (the recommended config),
this takes **push from 217 → 96 ns/op** and **peak RSS from 5.9 GB →
~0.1 GB** at n=10⁶, bringing the C to parity with Viennot on the
per-element ops (and it was already winning on concat).  On a bounded
churn workload it likewise cuts RSS ~36% and runs ~28% faster.  This is
exactly the role compaction plays for the §4 deque (a 4–5× swing there).

- **Remaining gap / future work**: pop/eject (~1.1–1.2×) and the
  persistent fork (1.5×) still trail Viennot — draining and read-only
  repeated-pop create less reclaimable garbage, and a `kc_chain` spine
  node is still `malloc`'d per op.  A *unified-arena* §6 collector (spine
  + stored cells + §4 buffers relocated in one Cheney pass) would also
  reclaim the spine and likely close these; it is a larger rewrite than
  the per-buffer `kc_arena_compact` above and is left as future work.

## How to reproduce

```sh
# C
cd c
make clean all
./test            # property tests at n = 1..100,000
./bench           # microbench at n = 10k, 100k, 1M (K=4096 default)
./wc_test         # worst-case allocation bound

# OCaml comparison (KTDeque kt2 vs Viennot)
cd ..
dune build
_build/default/ocaml/bench/compare.exe

# Or use the top-level reproducible bench harnesses:
make bench-three-way      # all three side-by-side at n=1M
make bench-canonical      # KT vs Vi vs handwritten Deque4 vs list ref
```

For the catenable (§6) C port:

```sh
cd c
make cadeque_test && ./cadeque_test 200000      # self-check vs deque oracle
# differential vs the verified OCaml extraction:
cd .. && dune build --profile release ocaml/bench/diff_cadeque.exe
cd c && make run-diff-cadeque
# microbench:
gcc -O3 -DNDEBUG -Iinclude -o /tmp/bc benches/bench_cadeque.c \
    src/ktcadeque.c src/ktdeque_dequeptr.c && /tmp/bc 1000000
```
