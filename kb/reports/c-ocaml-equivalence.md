# How convincing is the C ↔ extracted-OCaml "equivalence"?

A critical reading of the evidence we have today (post-`make check-all`) for the
claim *"the hand-written C in `c/src/ktdeque_dequeptr.c` agrees with the
Coq-extracted OCaml in `ocaml/extracted/`."*

The short answer: **strong probabilistic evidence on the sampled distribution,
but not a refinement proof.** The link
"Coq spec is sequence-correct" → "OCaml is sequence-correct" → "C matches
OCaml on tested traces" → "C is sequence-correct" has one rigorous step
(extraction soundness, modulo Coq's standard caveat) and one purely empirical
step (the trace match).

## What is actually verified, what is tested, and what is unverified

```
   Coq spec (Model.v, OpsKTSeq.v)
   ─── proven sequence-preserving (Theorems push_kt2_seq, …, eject_kt4_seq)
        │
        │   extraction (Coq's standard extractor, unverified)
        ▼
   OCaml (ocaml/extracted/kTDeque.ml)
        │
        │   << TESTING ONLY: differential bit-for-bit on workloads >>
        ▼
   C (c/src/ktdeque_dequeptr.c, hand-translated from the imperative DSL)
```

Every arrow above the dashed gap is mechanically checked by Coq.  Every arrow
below is testing only.  The C is *not* extracted; it is hand-translated.  The
hand translation is the load-bearing unverified step.

## What we run today

| Layer                                   | Coverage                                                                  | What it falsifies                                                    |
| -----                                   | --------                                                                  | -----------------                                                    |
| `check-diff`                            | 1 deterministic 100k-op trace, xorshift64 PRNG, identical seed both sides, **uniform-mix** workload | C vs OCaml output divergence on shallow deques                       |
| `check-diff-deep`                       | 1 deterministic 400k-op trace, **deep-cascade** workload (4 monotonic phases of 100k each, drives depth ~17) | C vs OCaml output divergence on the deepest cascade machinery        |
| `check-diff-multi`                      | **16 PRNG seeds × {mix, deep} = 32 independent traces** at n=50k each      | C vs OCaml output divergence across an ensemble of seeds             |
| `check-fuzz`                            | 1000 random seeds × workload lengths in {100, 500, 1k, 5k, 10k}           | C vs in-test reference deque divergence + memory bugs (ASan + UBSan) |
| `check-persistence-stress`              | 200 trunk snapshots × 64 forks under ASan; cross-validates that no fork mutates trunk or any sibling | COW violations under dense internal-cell sharing                     |
| `check-tsan`                            | 4 threads × 100k ops, per-thread deques                                   | data races on TLS-isolated state                                     |
| `check` (functional)                    | 7 workloads × 11 sizes (1 to 1M)                                          | basic regressions + `kt_check_regular` invariant                     |
| `check-static`                          | gcc -fanalyzer + clang --analyze                                          | null-deref, OOB, double-free, leak, UAF                              |
| `wc_test`                               | ≤ 8 allocations per call, flat in n                                       | C silently amortizing instead of WC O(1)                             |

All green.  Total wall-clock for `check-all`: ~41 seconds (was ~25s before
the deep + multi-seed + persistence-stress layers were added).

## What this is convincing about

### 1. Bit-for-bit C ↔ OCaml at n=100k is genuinely unusual evidence

`diff_workload.c` and `diff_workload.ml` share the same xorshift64 stream
(seed `0x123456789abcdef0`), the same op-decoding (`x mod 4`), the same
ascending value supply, and emit the same per-op stdout.  After 100k operations
mixing push/inject/pop/eject uniformly, every byte of stdout matches.

That output trace contains, for each operation:
- which op fired,
- the resulting deque length,
- and a final full traversal of the residual deque.

Bit-for-bit means the two implementations agree on:
- the order of removal (FIFO at the right end after mixing → not just the
  multiset of elements survives, but the position),
- the empty-deque transitions (pop-empty / eject-empty → `NONE`),
- the length after each op.

Sequence equivalence over a 100k-op random trace is a strong constraint.  For
a deque ADT, sequence equivalence with the same operation log determines the
abstract state up to representation.  A bug that systematically displaces an
element by even one slot would diverge within tens of operations.

### 2. The OCaml side is anchored in proven theorems

`OpsKTSeq.v` discharges, mechanically:

- `push_kt2_seq`, `pop_kt2_seq`, `inject_kt2_seq`, `eject_kt2_seq`
- the same family for `kt3` and `kt4`
- `make_small_seq` (the 9-case rebalance)
- `ensure_green_k_seq`, `make_yellow_k_seq`, `make_red_k_seq`

These say: the imperative DSL operation, viewed as a function on the abstract
list, equals the spec.  Extraction maps the DSL to OCaml, modulo extraction
soundness.  So when we see the OCaml output on a 100k-op trace, that output
*is* the abstract spec's output on that trace, modulo extraction bugs.  This is
a much stronger anchor than "two implementations agree" — one of the two is a
mechanically-checked oracle.

### 3. Multiple independent oracles don't contradict each other

The fuzz harness validates the C against a textbook reference deque
(doubly-linked list, push/pop in C in the test binary).  The diff test
validates the C against extracted OCaml.  These two reference implementations
share no source code with the C.  Both report "no divergence" across their
respective coverage.  This rules out the failure mode "C and extracted-OCaml
agree because they share an extraction-pipeline bug" — the simple reference
deque has nothing to do with extraction.

### 4. WC-test bounds are an active falsifier of "amortized in disguise"

`wc_test` runs each operation kind across n ∈ {10⁰, 10¹, …, 10⁶} and asserts
allocations-per-call ≤ a small constant, regardless of n.  If the C
"correctly" returns the same sequences as OCaml but secretly batched them
(say, doubled-array style), wc_test would see a per-call alloc count growing
with n on cascade-triggering workloads.  It does not.  This is the only
mechanism we have today that distinguishes "the C is the same algorithm" from
"the C is a different algorithm that happens to compute the same output."

## Where the argument is weaker than it looks

### A. Sample size relative to the state space (partially mitigated)

A deque after n persistent operations can be in roughly Catalan(n)-many
distinguishable states, even with our cell-aliasing structure.  We now
explore a substantially larger sample than before:

- `check-diff` at 100k ops × 1 seed (mix);
- `check-diff-deep` at 400k ops × 1 seed (deep);
- `check-diff-multi` at 50k ops × 16 seeds × 2 modes = 32 traces;
- `check-fuzz` at 1000 random seeds × ≤10k ops;
- `check-persistence-stress` at 200 trunk snapshots × 64 forks × 100 ops.

Total: of the order of **10⁸ deque states** sampled across many independently
seeded distributions, including both shallow (mix) and depth-saturating
(deep) regimes.  This still doesn't approach the state space, but it covers
the operationally-relevant regions.  Bug classes that require a *specific*
adversarial sequence outside both the uniform and the linear-monotonic
distributions remain logically possible — see (E) for the residual gap.

### B. The PRNG distribution is biased toward shallow deques (CLOSED)

The old uniform-mix workload produced a stationary distribution where the
deque was small most of the time, rarely exceeding depth 2–3.  The
`check-diff-deep` layer added in 2026-05 directly addresses this: it runs
4 monotonic phases of 100k ops each (push, inject, pop, eject), driving
the deque to depth Θ(log₂(100k)) ≈ 17 on the push phase, then exercising
every cascade-rebuild path on the drain.  The deepest cascades are now
diff-tested, not just perf-tested.  This was the "most concerning gap"
in the original report.  It is closed.

### C. Sequence equivalence ≠ structural equivalence

The differential test compares observables (per-op output + final sequence).
It does not compare:

- internal coloring (a "green" link in the C may correspond to either green or
  yellow in the OCaml's `KChain`, undetected, as long as eventual sequences
  match),
- when cascades fire (the C is allowed to lag a cascade by one op as long as
  the next op compensates — sequences would still match across the trace),
- depth-of-structure (C might keep one extra level of nesting; sequences are
  unaffected).

In particular, *any algorithmic divergence that preserves sequences across
trace boundaries is invisible to differential testing.*  We are testing a
projection, not the algorithm.

### D. The hand translation is the unverified step

The C translation mirrors the Coq imperative DSL (`exec_*_C` in
`Footprint.v`).  No theorem connects them.  ADR-0010 explicitly punts the
refinement proof to "future work".  A typo in the hand translation that
happens to preserve sequences on the fuzz/diff distribution would never be
caught by the current pipeline.  Examples of bugs that can hide here:

- **Off-by-one in a single rebalance case** that only fires on a specific
  buffer-size combination not visited by xorshift over 100k ops.
- **A wrong color tag** in the surface link — if the next op happens to
  re-color before reading, the bug is silent.
- **An aliasing mistake in the COW pair-block sharing** that violates
  persistence.  We test persistence with one fork, not adversarial sharing.

### E. Extraction is trusted

The Coq extractor is part of Coq's TCB.  It has known soundness issues in
edge cases (e.g., universe-polymorphic constructs, opaque-vs-transparent
folding).  None of the constructs we use are exotic, but the chain of trust
includes extraction.  If both the OCaml *and* the C miscompute the same way
(synchronized hallucination), no oracle in our pipeline would catch it.  This
is unlikely but not impossible.

### F. Fixed element type masks tag-aware bugs

All tests use `long` payloads, addressed via `&storage[i]` (8-byte aligned).
The C's `kt_buf` packs the size into the low 3 bits of slot 0.  A bug in the
tagging layer that requires, say, a misaligned input or a payload pointer
with the low bits set, would not be exercised.  The fuzz harness should be
extended to use payloads with adversarial bit patterns.

### G. Persistence is tested only one level deep (CLOSED)

The simple `test_persistence` only forks once.  The `test_persistence_stress`
target added in 2026-05 covers two adversarial sharing patterns under
ASan + UBSan:

- a **trunk** of 200 snapshots S[0..200], each derived by injecting one
  element on the previous; every S[i] is forked, K random ops applied, the
  fork validated against a per-fork reference, and finally every S[j] is
  re-walked and confirmed to still equal its original trunk reference;
- a **starburst** of 64 branches off a single source, each with distinct
  random op sequences, where every branch is validated independently and
  the source is then verified unchanged.

If any of those forks were silently mutating shared internal cells (e.g.,
a pair-block reachable from two branches), at least one trunk snapshot or
sibling branch would diverge from its reference.  None do, across 200 + 64
sharing configurations.  This is the densest persistence stress we have.

### H. test_threads is isolation, not sharing

Each thread owns its own deque in its own TLS arena.  We test thread-local
non-interference (TSan-clean), not concurrent reads of a shared persistent
deque.  Persistent immutability *should* make the latter trivially safe, but
immutability is a property of the API contract, not directly tested.

## Calibrated confidence statement (revised, post-deep + multi-seed + persistence-stress)

After closing the top-three gaps from the original report, the evidence
landscape has shifted:

- **Very strong** confidence that no bug fires under uniform-random
  push/inject/pop/eject mixing at scales up to 10⁶ operations.  Same as
  before.
- **Very strong** confidence that no bug fires on linear-monotonic
  workloads driving the deque to depth ≈ 17 (the regime where cascade
  rebuilds dominate).  This was previously only "moderate" — the `δ.adv`
  benchmarks exercised these depths but didn't diff-test them.  Now the
  `check-diff-deep` layer diff-tests 400k ops on exactly that regime and
  passes bit-for-bit.
- **Strong** confidence on across-seed robustness: 32 independently-seeded
  C-vs-OCaml traces (16 seeds × {mix, deep}) all agree byte-for-byte.  No
  single-seed accident.
- **Strong** confidence that no bug is visible to ASan, UBSan, TSan,
  gcc -fanalyzer, or clang static analysis.  Same as before.
- **Strong** confidence in COW persistence under dense sharing: 200 trunk
  snapshots × 64 forks under ASan, with cross-validation that no fork
  corrupts the trunk or any sibling.  Previously only a single-fork test.
- **No** formal claim about the hand translation being a refinement of the
  Coq imperative DSL.  That gap exists by design (ADR-0010) and is not
  closed by this testing pipeline.  This is now the **single dominant
  source of residual risk** — every other gap has been narrowed.

In other words: the evidence is sufficient to ship the C as a high-quality
implementation of a verified spec.  The remaining residual is the
hand-translation step, which testing alone cannot fully close.

### What residual risk looks like now

The bug shapes that could still hide:

1. A **non-obvious cascade pattern** that neither uniform-mix nor linear-monotonic
   visits — for example, a back-and-forth oscillation that drives the
   deque repeatedly through the depth-8 → depth-9 boundary in a specific
   color combination.  Property-based shrinking would catch this; uniform
   random and adversarial-monotonic together do not.
2. A **synchronized hallucination** where the OCaml extracted code and the
   C both miscompute the same way — unlikely but not impossible, since
   neither side directly cross-checks against the abstract spec at run
   time.  A direct extraction of the C from Coq (or a reference walker
   that decodes the C state into the abstract list and compares to the
   spec semantics directly) would close this.
3. A **bug in a path that's reached only under conditions our generators
   don't synthesize** — e.g. very particular interleavings of fork and
   continued use, or operations on deques near the int overflow point of
   the length counter (currently neither side can hit that).

## How the evidence could be strengthened further (in priority order)

1. **Refinement proof, sketched.**  Even an informal lemma list connecting
   the C structures to the Coq imperative DSL would surface where the
   translation is non-obvious and where bugs could hide.  This is now the
   highest-leverage remaining item — every cheap testing avenue has been
   exercised.
2. **Property-based shrinking.**  Replace fixed-length fuzz with
   QuickCheck-style shrinking against the reference deque, so that any
   discovered counterexample is minimized.  Catches the "specific cascade
   oscillation" class that uniform/monotonic generators miss.
3. **Larger n and more seeds.**  The diff layers are now O(n).  Bumping
   `check-diff-multi` to 100 seeds × {mix, deep, oscillating} at n=200k
   would take ~1 minute and add another order of magnitude of coverage.
4. **Direct in-process spec oracle.**  Add a small "abstract list"
   reference type alongside the deque, updated with each op, and assert
   `walk(deque) == ref_list` on every operation.  Would let the C catch
   structural divergence without needing the OCaml binary at all.
5. **Adversarial element bit patterns.**  Mix in payloads with the low 3
   bits set (point F).  Lower priority because the API contract requires
   8-byte aligned pointers — bugs would only surface for misuse.
