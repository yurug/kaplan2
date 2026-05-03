---
id: algorithms
domain: spec
related: [data-model, api-contracts, functional-properties]
---

# Algorithms

## One-liner
Step-by-step description (or pseudocode) of every operation, naive
update, and repair case, anchored to manual sections and theorem
identifiers.

## Scope
Covers: the four packet-deque operations (push/inject/pop/eject) and
their underflow/overflow cascades, plus the simpler RBR warm-up. Does
NOT cover: type definitions (see `data-model.md`) or external SDK
behavior (see `external/INDEX.md`).

## Conventions
- "Naive step" = operation on the top buffer/triple, ignoring
  regularity. May leave the structure semiregular but not regular.
- "Repair" = cascade that walks the (sub)structure to restore
  regularity.
- Each operation is implemented twice in the codebase: once on the
  abstract chain (`*_chain` in `OpsAbstract.v`), once on the heap
  (`exec_*_pkt_C` in `Footprint.v`), and connected by a refinement
  theorem in `Correctness.v`.

---

## 1. RBR `succ` (manual §4 / KT99 §3 / VWGP §2)

```text
succ n :=
  let n' := increment_lsd n in       (* possibly leaves an irregular RBR *)
  regularize n'

regularize chain :=
  walk to first non-1 digit di
  if di = 0: stop
  if di = 2: set di := 0, increment di+1, recurse if needed
```

Theorem `RBR-1`: `regular n → ∃ n', succ n = n' ∧ regular n' ∧ val n' = val n + 1`.

The RBR module (`rocq/KTDeque/RBR/`) is a warm-up only and is not on
the active build path of the deque proofs.

## 2. Packet-deque public operations

### 2.1 Public surface (`rocq/KTDeque/DequePtr/Interface.v`)
- `empty`, `is_empty`, `push x q`, `pop q`, `inject q x`, `eject q`,
  `to_list q`.

### 2.2 Naive top-level updates

`push x q`:
- if `q` is empty: build a singleton chain.
- else: push `x` onto the top prefix buffer.

`inject` is the symmetric mirror (top suffix preferred).

`pop q`: pop from the top prefix if nonempty; else from the top suffix;
else fail. Symmetric for `eject`.

After the naive update the structure is at most semiregular.

### 2.3 Overflow / underflow

If `push` would overfill the top prefix (`B5`), the operation triggers
`make_red_push_chain` to redistribute. If `pop` would underflow the top
prefix (`B0` while inner levels remain), it triggers
`make_green_pop_chain` to refill.

The recursive shape of overflow/underflow rebalancing matches the
manual's repair cases. A canonical exhaustive trace of the cases is
recorded in `section4-repair-cases.md`.

For each case prove:
1. Sequence preservation.
2. The freshly-anchored level becomes green.
3. Inner levels become green / yellow / disappear as appropriate.
4. All deeper levels unchanged except local pointer rewiring.

### 2.4 Heap-level execution

`exec_push_pkt_C H r x = Some (H', r', cost)` allocates the new top
chain link, leaves the rest of `H` untouched, satisfies
`heap_ext H H'`, and `chain_repr_at H' r' (push_chain r) depth` whenever
`chain_repr_at H r d depth`. `cost ≤ NF_PUSH_PKT_FULL = 9`.

---

## 3. Heap-level execution and refinement

For every public op, the schema is:

```text
exec_op H args = Some (H', out, cost)
∧ chain_repr_at H r c depth
→ ∃ c' out',
    chain_repr_at H' r' c' depth
    ∧ out' models the abstract result
    ∧ abstract_spec c c' out'
    ∧ heap_ext H H'
    ∧ cost ≤ NF_*_PKT_FULL.
```

Memory-safety side conditions:
- every read location was already in `H`;
- every newly allocated location was fresh;
- output roots point to allocated cells.

## Agent notes
> Implement each operation **first on the abstract chain**
> (`OpsAbstract.v`), then on the heap (`exec_*_pkt_C` in `Footprint.v`),
> then prove refinement (`exec_*_pkt_C_refines_*_chain` in
> `Correctness.v`). Don't try to prove list equations directly on raw
> cells.
> Symmetry: `pop`/`eject`, `inject`/`push` are mandatory mirrored pairs.
> Use `Common/Symmetry.v`.

## Related files
- `data-model.md` — the types these algorithms manipulate.
- `section4-repair-cases.md` — verbatim KT99 §4.2 cases.
- `properties/functional.md` — invariants each step must preserve.
- `properties/edge-cases.md` — boundary inputs to test.
- `error-taxonomy.md` — what failure looks like for `pop`/`eject` on empty.
