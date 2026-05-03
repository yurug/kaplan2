---
id: edge-cases
domain: properties
related: [functional-properties, algorithms, error-taxonomy]
---

# Edge Cases (T-entries)

## One-liner
Boundary inputs every operation must handle correctly. Each T-entry must be exercised by at least one example or property-based test.

## Conventions
Same as functional/non-functional: `T<N>` IDs are stable.

## Index

| ID  | Trigger                                                 | Properties exercised |
|-----|----------------------------------------------------------|-----------------------|
| T1  | `pop empty` / `eject empty`                              | P2, P4                |
| T2  | `pop`/`eject` on a singleton (1-element deque)           | P2, P4, P28           |
| T3  | `push`/`inject` onto empty                               | P1, P3                |
| T4  | Repeated `push` to grow a buffer through 0,1,2,3,4,5     | P1, P22, P30          |
| T5  | Repeated `push` to overflow level 0 and create level 1   | P1, P22, P28          |
| T6  | `concat empty q`                                          | P5                    |
| T7  | `concat q empty`                                          | P5                    |
| T8  | `concat` of two singletons                                | P5, P25               |
| T9  | `concat` where one side has a `Right` triple              | P5, P25               |
| T10 | `concat` triggering Subcase 1d "size > 8" branch          | P5, P25               |
| T11 | `pop` on a deque whose top preferred path is length 1     | P2, P26               |
| T12 | `pop` on a deque whose top preferred path is length 2     | P2, P26, P29          |
| T13 | `pop` on a deque whose top preferred path is length ≥ 3   | P2, P26, P27, P29     |
| T14 | `pop` triggering each repair Case (1a, 1b, 2a, 2b, 2c)    | P26, P27              |
| T15 | Persistence: keep an old root, push to a new one, query both | P6, P28           |
| T16 | Section-4 buffer hitting size 5 (red); regularization     | P22, P23              |
| T17 | Section-4 deepest-level `One b` with `b = B5`             | P22                   |
| T18 | Stored triple `Big` with empty child and one empty buffer | P25, ST2              |
| T19 | Ordinary `Only` triple with empty child                   | P24                   |
| T20 | Largest deque the test machine can build (smoke)          | NF6, NF11             |
| T21 | `push` then `pop` returns identity                         | P1+P2 round-trip      |
| T22 | `push` then `eject` does NOT return original element       | P1, P4 (semantics)    |
| T23 | `inject` then `pop` returns the older `push`-ed element    | P3, P2                |
| T24 | Mixed sequence of `push`, `inject`, `pop`, `eject`, `concat` of length 100 | P1–P5, P28 |
| T25 | RBR: `succ` of `0…01112` (irregular by carry)              | P9                    |
| T26 | RBR: `succ` of empty number                                 | P9                    |
| T27 | Buffer transfer when concat Case 4 collapses to one buffer (concat scope only) | P5, P25 |

## Detailed cases

### T1 — Pop / eject empty
```rocq
Example T1_pop_empty : pop (@empty A) = None.
Example T1_eject_empty : eject (@empty A) = None.
```

### T2 — Pop singleton
```rocq
Example T2_pop_singleton : pop (push x empty) = Some (x, empty).
```

### T4 — Buffer growth through every size
For `n ∈ {0,1,2,3,4,5}`, push `n+1` elements and verify both `to_list` and the cached buffer color.

### T5 — Level-1 creation
Push 6 elements to a level-0 deque; verify level 1 is created with size 1 (a yellow buffer).

### T13 — Long preferred path pop
Build a cadeque whose top preferred path has length ≥ 3 (some deeply yellow run). Pop. Verify `adopt6` was used and `seq` is correct.

### T14 — Each repair case
For each repair case (1a, 1b, 2a, 2b, 2c) in `algorithms.md` §4.3, build the smallest input that triggers it. Pop. Verify color of the result is green.

### T15 — Persistence
```rocq
Example T15_persistence :
  let q := build_some_deque () in
  let q' := push 99 q in
  let q'' := concat q (push 0 empty) in
  to_list q  = original_seq /\
  to_list q' = 99 :: original_seq /\
  to_list q'' = original_seq ++ [0].
```

### T20 — Smoke
Build a deque of `2^16` elements; verify length and head/tail. Used as a build-time sanity check, not as a proof.

### T24 — Mixed sequence
Property-based test: random sequence of 100 ops, compared against a list reference. Either via `QuickChick` (out of scope per Q15) or via Monolith on extracted code (NF11).

### T25 / T26 — RBR edge
`succ (regular_form 011112) = regular_form 1111101`. `succ (empty) = represent 1`.

## Coverage policy

Per the testing strategy:

- Every T-entry has at least one `Example` or `Lemma` whose name begins with `T<N>_…` in the corresponding test file.
- A T-entry that pertains exclusively to internal helpers (T17, T18, T19) lives in the helper's test file.
- T20 and T24 are "smoke" cases; they may live in OCaml drivers (`ocaml/bench/` or `ocaml/test_monolith/`) rather than as Rocq lemmas. NF11 is satisfied by sustained fuzzing.

## Agent notes
> When implementing a new repair case or operation, *first* identify which T-entries are affected. Add new T-entries if the change reveals an untested boundary. Never skip a T because "it's covered by another test" — if you can articulate which test covers it, write the cross-reference instead.
> For each T, also note which P-entries it covers; this is the bridge that lets the audit checklist verify "every P has at least 2 tests, including one edge case."

## Related files
- `functional.md` — P-entries.
- `non-functional.md` — NF-entries.
- `../spec/algorithms.md` — case structure for `concat`, `pop`.
- `../spec/error-taxonomy.md` — empty-input behavior.
