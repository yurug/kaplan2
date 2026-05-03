---
id: error-taxonomy
domain: spec
related: [data-model, algorithms, api-contracts]
---

# Error Taxonomy

## One-liner
Every situation in which a function returns "no result" or fails, what causes it, and how the caller observes it.

## Scope
Covers: every named partial / fallible operation in the public surface and key internal helpers. Does NOT cover: low-level Rocq tactic failures (those are not user-observable).

## Conventions
- We do **not** model exceptions; failure on empty containers is `option`-typed.
- Internal helpers either are total (no failure mode) or have a *precondition* enforced by the caller; in the heap monad they may return `None` to signal a violated invariant. **A `None` from a helper that should be reachable only on bad input is a bug, not an error.**
- Memory exhaustion is not modeled: `alloc` always succeeds in `M`. The bounded footprint theorem is the only memory-correctness guarantee.

## Error classes

| Class | When it occurs                                                                                  | How observed                              |
|-------|--------------------------------------------------------------------------------------------------|-------------------------------------------|
| `EmptyDeque`     | `pop`, `eject` called on a deque whose model sequence is `[]`.                    | Public: `None`. Internal: same.            |
| `EmptyBuffer`    | `buf_pop`, `buf_eject`, etc. called on an undersized buffer.                       | Internal `option` `None`. Caller must avoid. |
| `RepairUnreachable` | A repair case is invoked when the structure is already regular (caller bug). | Internal contradiction; debug-time `assert`. |
| `BrokenInvariant`   | `repr*` predicate fails due to bug.                                            | Refinement theorem unprovable; never raised at runtime. |

## Detailed catalog

### `EmptyDeque` (public)
- **Origin**: `pop empty`, `eject empty`.
- **Visible**: `Some _` vs `None` constructor of `option`.
- **Spec**: `pop q = None ↔ ⟦q⟧ = []` (`api-contracts.md` §1.2).
- **Test coverage**: at least one `Example` per op (T1 in `properties/edge-cases.md`).

### `EmptyBuffer` (internal)
- **Origin**: any buffer helper whose precondition is `size b ≥ k`.
- **Visible**: only inside helper modules; public ops dispatch to total versions.
- **Spec**: each helper's law is conditional on the size precondition (see `properties/functional.md`).
- **Defense**: callers only invoke helpers when their preconditions are statically known. The precondition is part of the type when feasible (e.g. `buf_take_first2 : Buf6 X → size ≥ 2 → …`).

### `RepairUnreachable`
- **Origin**: invoking the repair entry point on a structure whose top is already green.
- **Visible**: only via tests/examples; in production code the repair entry point is gated on a color check.
- **Spec**: `repair_at_red d = None` when `top_color d ≠ Red`. Repair functions take a witness `H : top_color d = Red`.

### `BrokenInvariant`
- **Origin**: refinement theorems would fail; this never gets shipped.
- **Defense**: every commit must pass `make axioms` reporting `Closed under the global context`.

## Failure paths in the heap monad

```text
exec_op H args = None
↔
∃ b ∈ buffer helpers used by op, b H args = None
∧ that helper had a precondition violation propagated up.
```

In a correctly written op, this disjunction must be **provably empty** (i.e., `exec_op H args = Some _` for all `H, args` satisfying `repr*`). The refinement theorem (`api-contracts.md` §1.4) makes this guarantee.

## What we never produce

- **Exceptions** in OCaml extraction: not used. We pattern-match `option`.
- **Partial functions**: every Rocq function is total.
- **Unsafe coercions**: forbidden in public API. Internally, `comp_eq`-style tricks (VWGP §9.2.1) are used only if reduction-inside-Rocq is needed; ADR-0007 records whether we use this.
- **Out-of-memory**: not modeled. The footprint theorem bounds allocations, so realistic callers will not run out.
- **Concurrency / data races**: not modeled (purely functional).

## Agent notes
> If you ever feel tempted to add an `Inductive Error := …` for graceful failure reporting, stop. The contract is: `option` for partial public ops, `M (option …)` only inside the heap monad if a precondition is statically unprovable. Adding error types pollutes the API and breaks the simplicity of the §22 acceptance theorems.
> Empty-deque operations: every `pop`/`eject` test must have *both* an empty-input and a singleton-input case (T1, T2 in `edge-cases.md`).

## Related files
- `api-contracts.md` — public contracts that govern what's a public failure.
- `properties/edge-cases.md` — concrete edge inputs.
- `algorithms.md` — internal helper preconditions.
