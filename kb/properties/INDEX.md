---
id: properties-index
domain: meta
related: [index, by-task]
---

# Properties — Index

## One-liner
Routing table for invariants, bounds, and edge cases.

## Files

| If you need…                              | Read                  |
|-------------------------------------------|------------------------|
| Sequence laws + regularity invariants     | `functional.md`        |
| Bounds and tooling guarantees             | `non-functional.md`    |
| Boundary inputs + concrete test cases     | `edge-cases.md`        |

## Numbering policy
- `P<N>` for functional invariants.
- `NF<N>` for non-functional bounds.
- `T<N>` for edge-case scenarios.

IDs are **stable**; never renumber. When deleting, mark `(retired: <date> <reason>)` rather than removing the row.

## Cross-coverage matrix (excerpt)

| Property | Tests covering it (T)        | Implementation lemma                       |
|----------|------------------------------|--------------------------------------------|
| P1       | T3, T4, T5, T15, T21         | `Public/Summary.v#push_seq`                |
| P2       | T1, T2, T11–T14, T15, T21    | `Public/Summary.v#pop_seq`                 |
| P3       | T3, T15, T22, T23            | `Public/Summary.v#inject_seq`              |
| P4       | T1, T22, T23                 | `Public/Summary.v#eject_seq`               |
| P5       | T6, T7, T8, T9, T10, T15, T27| `Public/Summary.v#concat_seq`              |
| P6       | T15                          | `Cadeque6/Persistence.v#persistence_holds` |
| P9       | T25, T26                     | `RBR/Proofs.v#RBR_1`                       |
| P25      | T8, T9, T10, T27             | `Cadeque6/OpsConcat.v#C6_2`                |
| P26      | T11, T12, T13, T14           | `Cadeque6/OpsPopEject.v#C6_3`              |
| P27      | T13, T14                     | `Cadeque6/OpsPopEject.v#C6_4`              |

(Full matrix maintained as the implementation evolves; auditors update.)

## Agent notes
> Use this index to answer "given P<N>, where do I look?" or "given a failing T<N>, which property is at risk?"

## Related files
- `../INDEX.md` — master.
- `../indexes/by-task.md` — what to load for `test`/`audit`.
