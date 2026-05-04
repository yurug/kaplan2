---
id: api-contracts
domain: spec
related: [data-model, algorithms, error-taxonomy, functional-properties]
---

# API Contracts

## One-liner
Inputs, outputs, and refinement contracts for every public operation in
`rocq/KTDeque/DequePtr/Interface.v`.

## Scope
Covers: signatures, refinement specs, sequence laws, persistence
statements. Does NOT cover: implementation algorithms (see
`algorithms.md`) or internal helpers (see `data-model.md`).

## Conventions
- `t A` = the public type of a packet-deque handle (a `Chain A` wrapper).
- `to_list q` = sequence denotation of `q`.
- All operations are total functions; failure on empty deques is
  reported via `option`, never via exceptions or partiality.

---

## 1. Public deque API (`rocq/KTDeque/DequePtr/Interface.v`)

### 1.1 Signature

| Name        | Signature                                          | Sequence law                              |
|-------------|----------------------------------------------------|-------------------------------------------|
| `empty`     | `t A`                                              | `to_list empty = []`                       |
| `to_list`   | `t A → list A`                                     | spec primitive                             |
| `push`      | `A → t A → t A`                                    | `to_list (push x q) = x :: to_list q`     |
| `pop`       | `t A → option (A × t A)`                           | see §1.2                                   |
| `inject`    | `t A → A → t A`                                    | `to_list (inject q x) = to_list q ++ [x]` |
| `eject`     | `t A → option (t A × A)`                           | see §1.2                                   |

### 1.2 Sequence laws

```text
to_list empty                                  = []
to_list (push x q)                             = x :: to_list q
pop q = None                                   ↔ to_list q = []
pop q = Some (x, q')                           → to_list q = x :: to_list q'
to_list (inject q x)                           = to_list q ++ [x]
eject q = None                                 ↔ to_list q = []
eject q = Some (q', x)                         → to_list q = to_list q' ++ [x]
```

### 1.3 Persistence

The model is purely functional. `q` is unchanged by any operation that
takes `q` as argument; all operations return new handles. Persistence
holds by construction.

The heap-monad refinement layer (`Footprint.v`'s `exec_*_pkt_C`)
additionally guarantees `heap_ext H H'` for every operation.

### 1.4 Footprint

For every public operation `op`, there is a constant cost bound:
- `NF_PUSH_PKT_FULL = 9` (push including overflow rebalance)
- `NF_POP_PKT_FULL = 9` (pop including underflow refill)
- Symmetric `NF_INJECT_PKT_FULL = NF_EJECT_PKT_FULL = 9`

Each unit of cost is one `read`/`alloc`/`freeze` primitive in the cost
monad `MC`.

### 1.5 Memory safety

For every public op `exec_op H args = Some (H', out)`:
- every read location is in `dom H`;
- every newly allocated location is fresh w.r.t. `H`;
- every location reachable from `out` is in `dom H'`.

---

## 2. C public surface (`c/include/ktdeque.h`)

The C exposes the same operations as the Rocq interface, expressed in C
ABI:

| Symbol              | Meaning                                          |
|---------------------|--------------------------------------------------|
| `kt_empty`          | empty deque (NULL pointer)                       |
| `kt_push`           | push at front                                    |
| `kt_inject`         | push at back                                     |
| `kt_pop`            | pop from front (returns NULL on empty)           |
| `kt_eject`          | pop from back (returns NULL on empty)            |
| `kt_length`         | number of base elements (relies on K=2 invariant)|
| `kt_walk`           | enumerate base elements                          |
| `kt_check_regular`  | structural sanity check (not the abstract regularity invariant) |

The C implementation has no formal correspondence with the Rocq
interface; the relationship is established by running both against the
same fuzz workload and diffing outputs.

## Agent notes
> The contracts here are the *external* contract. Internal helpers have
> their own laws stated in `properties/functional.md`. Naming: each
> refinement theorem is named `<op>_refines`. Each sequence law on the
> public type is `<op>_seq`.

## Related files
- `data-model.md` — the types named here.
- `algorithms.md` — how the operations work.
- `error-taxonomy.md` — when `pop`/`eject` return `None`.
- `properties/functional.md` — every law as an indexed P-entry.
