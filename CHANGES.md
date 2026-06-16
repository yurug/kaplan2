# Changelog

## 0.2.0

Initial opam release.

`ktdeque` is a purely-functional, persistent double-ended queue with
worst-case — not amortised — O(1) `push`, `pop`, `inject` and `eject`,
plus worst-case O(1) `concat`. The implementation is extracted from a
machine-checked Rocq (Coq 9.1) proof.

- **Idiomatic public interface** (`open Ktdeque`):
  - `Deque` — the non-catenable real-time deque (Kaplan–Tarjan §4).
  - `Cadeque` — the same operations plus worst-case O(1) `concat`
    (Kaplan–Tarjan §6).

  Both modules carry documented `.mli` interfaces over
  `empty` / `is_empty` / `push` / `inject` / `pop` / `eject` /
  `peek_front` / `peek_back` / `concat` (Cadeque) / `length` /
  `to_list` / `of_list` / `iter` / `fold_left` / `fold_right` /
  `to_seq` / `of_seq`.
- The raw Rocq extraction remains available as the internal
  sub-library `ktdeque.extracted` (unstable; prefer `Ktdeque.Deque` /
  `Ktdeque.Cadeque`).
- Both keystone theorem bundles are closed with zero admits — totality,
  sequence preservation, the regularity invariant, and a constant
  per-operation cost bound — for both the §4 and §6 constructions.
- On the benchmark suite the extracted artifact is faster than Viennot
  et al.'s hand-written OCaml cadeque on every workload at n = 1M.

Reference: Haim Kaplan and Robert E. Tarjan, *Purely Functional,
Real-Time Deques with Catenation*, Journal of the ACM 46(5), 1999.
