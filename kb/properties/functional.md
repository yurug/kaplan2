---
id: functional-properties
domain: properties
last-updated: 2026-05-03
ids-defined: [P1, P2, P3, P4, P5, P6, P7, P8]
---

# Functional properties

## One-liner

The numerically-anchored invariants and laws that the implementation
must enforce, with violation example, rationale, and test strategy.

## Conventions

- **ID**: `P<N>`. Stable; never renumbered.
- **Statement**: math or pseudocode.
- **Violation**: smallest concrete input that reveals a bug.
- **Why**: why the property matters.
- **Test strategy**: which lemma / property-based test exercises it.

## Index

| ID  | Topic                                                           |
| --- | --------------------------------------------------------------- |
| P1  | Sequence law for `push`                                          |
| P2  | Sequence law for `pop`                                           |
| P3  | Sequence law for `inject`                                        |
| P4  | Sequence law for `eject`                                         |
| P5  | Persistence (operations don't mutate observable state)           |
| P6  | Memory safety (read/alloc preconditions hold)                    |
| P7  | Regularity preserved by every public op                          |
| P8  | Cost bound: every op runs in worst-case O(1) operations          |

---

## P1 — Sequence law for `push`

**Statement**: `∀ x q, ⟦push x q⟧ = x :: ⟦q⟧`.

**Violation example**: `push 1 (push 2 empty)` returns a deque whose
`to_list` is `[2;1]` instead of `[1;2]` — pre/suf swap bug.

**Why**: without it the public type does not represent a sequence.

**Test strategy**:
- Rocq theorem: `push_kt2_seq`, `push_kt3_seq`, `push_kt4_seq` in
  `rocq/KTDeque/DequePtr/OpsKTSeq.v`.
- Differential fuzz: OCaml extracted vs Viennot reference on the same
  push workload.

## P2 — Sequence law for `pop`

**Statement**: `pop q = None ↔ ⟦q⟧ = []`;
`pop q = Some (x, q') → ⟦q⟧ = x :: ⟦q'⟧`.

**Test strategy**:
- Rocq theorem: `pop_kt2_seq`, `pop_kt3_seq`, `pop_kt4_seq`.
- Differential fuzz: push then pop random sequences; outputs must match.

## P3 — Sequence law for `inject`

**Statement**: `⟦inject q x⟧ = ⟦q⟧ ++ [x]`.

**Test strategy**:
- Rocq theorem: `inject_kt2_seq`, `inject_kt3_seq`, `inject_kt4_seq`.
- Differential fuzz.

## P4 — Sequence law for `eject`

**Statement**: `eject q = None ↔ ⟦q⟧ = []`;
`eject q = Some (q', x) → ⟦q⟧ = ⟦q'⟧ ++ [x]`.

**Test strategy**:
- Rocq theorem: `eject_kt2_seq`, `eject_kt3_seq`, `eject_kt4_seq`.
- Differential fuzz.

## P5 — Persistence

**Statement**: every operation is purely functional. Forking the deque
(holding two references and operating on each independently) yields
two independent sequences with no observable cross-contamination.

**Violation**: an operation that reuses old cells with mutated fields.

**Why**: the data structure is *persistent* — all four operations
preserve the input.

**Test strategy**:
- Rocq: every op signature returns a new value; the input is
  immutable by construction.
- Runtime fork-stress test: snapshot, push 16 elements onto one branch,
  pop 16 from the other; both branches yield the expected sequences.

## P6 — Memory safety

**Statement**: in the imperative DSL, every `read` is preceded by a
`freeze` and every `alloc` returns a fresh location.

**Why**: the cost-tracked monad relies on the heap discipline; without
it the proofs do not apply.

**Test strategy**:
- Rocq theorems in `rocq/KTDeque/DequePtr/Footprint.v` track allocations
  and reads symbolically; the cost bound is by structural inspection.

## P7 — Regularity preserved by every public op

**Statement**: `regular q → regular (op q)` for
`op ∈ {push, pop, inject, eject}`.

**Why**: required for the worst-case O(1) bound. Without preservation,
a long sequence of operations can degrade the chain into a state
where the next op needs unbounded work.

**Test strategy**:
- Rocq invariant: `regular_kt` defined in
  `rocq/KTDeque/DequePtr/OpsKTRegular.v`; preservation theorems are
  the long-term proof target.
- Runtime witness: in debug builds the C runs `assert()`s that fire
  if regularity is violated. The test harness exercises 100k op
  sequences with debug builds, so a regression triggers at runtime.

## P8 — Cost bound

**Statement**: every operation completes in a constant number of heap
ops, independent of the deque size.

**Why**: this is the whole point of Kaplan-Tarjan — purely-functional
worst-case O(1).

**Test strategy**:
- Rocq: cost-tracked monad in `rocq/KTDeque/Common/CostMonad.v`,
  bound proven by structural inversion (no recursion on chain depth)
  in `rocq/KTDeque/DequePtr/Footprint.v`.
- Empirical: bench harness in `ocaml/bench/` measures nanoseconds per
  op across deque sizes from 10 to 10⁷; the timing is **flat** across
  sizes (the headline observable for worst-case O(1)).

## Agent notes

> When adding a property, give it the next free `P<N>` and a row in
> the table. Never reuse a number.
> Every Rocq lemma name in `rocq/KTDeque/` proving one of these
> properties should mention it (e.g., `Lemma push_kt2_seq` is the
> proof of P1 for the kt2 variant). This makes coverage analysis
> grep-able.

## Related files

- [`non-functional.md`](non-functional.md) — performance / memory.
- [`edge-cases.md`](edge-cases.md) — concrete inputs at boundaries.
- [`../spec/data-model.md`](../spec/data-model.md) — the types
  referenced by P-statements.
- [`../conventions/testing-strategy.md`](../conventions/testing-strategy.md) —
  naming and counting rules.
