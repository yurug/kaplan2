---
id: spec-index
domain: meta
related: [index]
---

# Spec — Index

## One-liner
Routing table for the formal specification.

## Where to start

If this is your first contact with the codebase, read
[`why-bounded-cascade.md`](why-bounded-cascade.md) first.  It is the
intuition layer — *why* the algorithm is correct and elegant — and
makes the rest of the spec (type definitions, operation pseudocode,
repair cases) readable rather than mystical.

## Files

| If you need…                                          | Read                              |
|-------------------------------------------------------|------------------------------------|
| The intuition behind the WC O(1) bound                 | `why-bounded-cascade.md`           |
| Type definitions and invariants                        | `data-model.md`                    |
| How operations work                                    | `algorithms.md`                    |
| The public surface and laws                            | `api-contracts.md`                 |
| Build/extraction config and project layout             | `config-and-formats.md`            |
| Error / failure classes                                | `error-taxonomy.md`                |
| Verbatim KT99 §4.2 Section-4 repair cases              | `section4-repair-cases.md`         |

## §22 Acceptance Checklist mapping

| #  | Statement                                                                       | Location                                                  |
|----|---------------------------------------------------------------------------------|-----------------------------------------------------------|
| 1  | A separately usable verified deque module.                                       | `rocq/KTDeque/DequePtr/Interface.v` (`RegularPacketDeque`) |
| 4  | Public sequence laws proved.                                                     | `Interface.v` (`*_to_list` axioms) backed by `OpsAbstract.v` |
| 5  | Persistence by heap extension proved.                                            | `Footprint.v` (heap-ext lemmas + `chain_repr_at_persists_strong`) |
| 6  | Memory safety proved.                                                            | per-op refinement in `Correctness.v` (no-overflow path)   |
| 7  | Bounded footprint proved.                                                        | `Footprint.v` (`NF_*_PKT_FULL = 9`)                       |
| 8  | Zero `Admitted.` invariant.                                                      | `grep -rn "Admitted\|admit\." rocq/KTDeque/` empty        |
| 9  | Single deviation: packet aggregation per ADR-0012.                               | architecture audit + ADR-0012                             |
| 10 | Constants centralized.                                                           | `Footprint.v` cost constants; `Common/Buf5.v` shape consts |

Items 4 and 6 are proved for the no-overflow case; the cascade case is
not covered by any refinement theorem.

## Related files
- `../INDEX.md` — master.
- `../properties/INDEX.md` — invariants (P-entries) referenced by these specs.
- `../architecture/overview.md` — how the modules realize the spec.
