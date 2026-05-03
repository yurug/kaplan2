---
id: glossary
domain: meta
related: [index, prd, data-model]
---

# Glossary

## One-liner
Canonical definitions for every domain term used across the KB.

## Scope
All terms used in more than one file. Section/Theorem/Lemma identifiers (D4-1, C6-3, P4) are catalogued under `properties/INDEX.md` and `spec/INDEX.md`, not here.

## Sources
- **Manual** = `/home/coder/workspace/kaplan2/kaplan_cadeque_execution_manual_v3.md` (the prescriptive contract).
- **KT99** = Kaplan & Tarjan, *Purely Functional, Real-Time Deques with Catenation*, JACM 46(5), 1999.
- **VWGP** = Viennot, Wendling, Guéneau, Pottier, *Verified Purely Functional Catenable Real-Time Deques*, 2025 (preprint LMCS).

---

## Core data types

- **Sequence** — finite ordered list of base elements; the mathematical model. Notation `⟦d⟧`. See `spec/data-model.md`.
- **Stack** — push/pop only. Not a target.
- **Queue** — push/eject (or inject/pop). Not a target.
- **Deque** (double-ended queue) — push, pop, inject, eject. Section-4 deque. **Manual: building block of Cadeque6.**
- **Steque** (stack-ended queue) — push, pop, inject, **plus** concat. Section-5. **Pedagogical, out of scope** (manual §5/§9).
- **Cadeque** (catenable deque) — push, pop, inject, eject, concat. Section-6. **The final artifact.** VWGP's preferred short-hand. We use both spellings.

---

## Levels and recursive slowdown

- **Level** — depth in the recursive structure. Level 0 = top.
- **A^l** (Section-4) — element type at level `l` of a Section-4 deque. `A^0 = A`; `A^(l+1) = A^l × A^l`. The "pair-of-pair" tower.
- **Stored_l(A)** — element type at level `l` in Section 6: `Elt_0(A) = A`, `Elt_(l+1)(A) = Stored(Elt_l(A))`. The "stored-triple" tower.
- **flat_l** — flattening function turning a level-`l` element into a list of base elements. Total length `2^l` for Section 4.
- **Recursive slowdown** — design technique: `T(n) = O(1) + c·T(n−1)` with `c < 1` gives `O(1)` overall. KT99 §3.

---

## RBR (warm-up)

- **RBR** — Redundant Binary Representation. Digits in `{0, 1, 2}`. `succ` operates in O(1) on regular RBRs.
- **Regular RBR** — for every digit `d_j = 2`, there is `i < j` with `d_i = 0` and all `d_k = 1` for `i < k < j`.
- **Packet** — a head digit (green/red, plus the very first digit) followed by zero or more body digits (yellow). VWGP §2.1.
- **Chain** — list of packets representing a number. Same structure idea reused in deque/cadeque.

---

## Colors

- **Color3** — `Green3 | Yellow3 | Red3`. Section 4 only. Worse-to-better order: `Red3 < Yellow3 < Green3`.
- **Color4** — `Green4 | Yellow4 | Orange4 | Red4`. Section 6 only. Worse-to-better order: `Red4 < Orange4 < Yellow4 < Green4`.
- **Buffer color** (Section 4) — sizes 0,5 → red; 1,4 → yellow; 2,3 → green. Manual §5.4.
- **Buffer color** (Section 6) — size 5 → red; 6 → orange; 7 → yellow; ≥ 8 → green. Manual §10.6.
- **Level color** (Section 4) — `min` of prefix and suffix colors, special case for the bottom level. Manual §5.5.
- **Triple color** (Section 6) — depends on triple kind:
  - `child` empty → green;
  - `Only` → worse of prefix/suffix colors;
  - `Left` → prefix color;
  - `Right` → suffix color.

---

## Section-4 specific

- **D4_l(A)** — abstract Section-4 deque at level `l`. `One(buf)` (bottom) or `Two(pre, child, suf)`.
- **Buf5 X** — buffer of 0..5 elements. Six-constructor encoding: `B0 | B1 x | B2 x y | … | B5 a b c d e`. Manual §5.2.
- **D4Cell** — heap cell layout: `{ pre4, child4 : option loc, suf4, col4, jump4 : option loc }`. Manual §6.1.
- **`jump4`** — shortcut pointer to the nearest proper non-yellow descendant, when the cell is top-level or non-yellow.
- **Repair site (Section 4)** — top level if red, else node reached by `jump4` if red. Found in O(1).
- **Repair cases (Section 4)** — Two-Buffer / One-Buffer / No-Buffer (KT99 §4.2; manual §7.5 lists Case A and references B/C from KT99). All three preserve denotation.

---

## Section-6 specific

- **Triple** — node of the cadeque tree. `Stored` (interior, in a buffer) or `Ordinary` (boundary).
- **Stored triple** — `Small(buf)` or `Big(pre, child, suf)`. Lives inside a buffer. Always green. Manual §10.2.
- **Ordinary triple** — `Only(p,c,s) | Left(p,c,s) | Right(p,c,s)`. Lives on the boundary of a cadeque. Manual §10.2.
- **Kind** — `only | left | right`. Describes how an ordinary triple sits relative to its parent. Manual §3.3.
- **Arity** — `0 | 1 | 2`. Number of top-level triples in a cadeque (root). Manual §3.3.
- **Buf6 X** — Section-6 buffer = `{ root6_buf : Root4 X; len6_buf : nat }`. **Implemented by Section-4 deque** (the central design constraint). Manual §8.1.
- **`adopt6`** — shortcut pointer to the tail of the preferred path starting at the cell, when the path length ≥ 3. Manual §6.1 (cadeque) / §11.1.
- **T6Cell** — Section-6 heap cell: `{ role6, pre6, child6 : Root6 (Stored X), suf6, col6, adopt6 : option loc }`.
- **Preferred child** — child of a yellow/orange triple chosen by the recursive descent rule (yellow→left/only, orange→right/only). Manual §10.7. KT99 calls these "preferred children"; VWGP §4.1.2 calls the resulting paths "packets".
- **Preferred path** — maximal downward path obtained by repeatedly following the preferred child. Tail is first green/red triple. Color = tail color.
- **Repair site (Section 6)** — red tail of the preferred path beginning at the left or only top-level triple. Found in O(1) via `adopt6` + at most one natural step. Manual §12.4 / KT99 §6.2.
- **Repair cases (Section 6)** — Cases 1a, 1b, 2a, 2b, 2c. Manual §12.4 / KT99 §6.2.

---

## Heap, persistence, refinement

- **Loc** — finite identifier for a heap cell.
- **Heap** — finite map `Loc → Cell`.
- **Allocation-only heap** — first-phase semantics: `alloc` and `read` only; **no overwrite**. Persistence is automatic. Manual §2.3.
- **`heap_ext H H'`** — every binding of `H` is unchanged in `H'`. The persistence relation. Manual §3.5.
- **`Root4 X`** / **`Root6 X`** — public handle to a deque/cadeque rooted in a heap. Manual §3.4.
- **`repr4 H r d`** — representation invariant: heap `H` decodes root `r` to abstract deque `d`. Manual §6.2.
- **`repr6 H r q`** — the analogous Section-6 invariant. Manual §11.3.
- **Refinement theorem** — every public operation on the heap matches its abstract counterpart up to the representation invariant. Manual §7.8 / §14.2.
- **Persistence theorem** — heap-ext preserves denotation; old roots keep meaning. Manual §1.3 / §14.3.
- **Memory safety theorem** — no dangling reads, fresh allocations, output roots point to allocated cells. Manual §14.4.
- **Footprint** — bounded number of `read` and `alloc` per public op. Manual §15.1.

---

## Regularity vocabulary

- **Semiregular** — between any two red descendants there is a green one (ignoring yellows). Section 4: §5.7. Section 6: see RC2/RC3 in manual §10.8.
- **Regular** — semiregular **and** the first non-yellow descendant (or top preferred path) is green. Section 4: §5.7. Section 6: RC2 + RC3 + RC4 in manual §10.8.
- **Naive step** — public operation applied to the top buffer/triple before regularization. Output may be only semiregular.

---

## Tooling and conventions

- **Rocq** — modern name for Coq Prover (Rocq Prover 9.0+ if available, else Coq 8.20). See `external/rocq-toolchain.md`.
- **dune** — build tool. `dune-project` + `(coq.theory ...)` stanzas.
- **Monolith** — François Pottier's OCaml fuzzing library. Used to validate extracted OCaml against a list-based reference. See `external/monolith-fuzzing.md`.
- **Params.v** — single source of truth for numeric constants used in size/color reasoning. Manual §19.

## Agent notes
> Load this file early; it prevents confusion between Section-4 colors (3) and Section-6 colors (4), between abstract deques and heap-rooted deques, and between Stored vs Ordinary triples.

## Related files
- `INDEX.md` — master routing.
- `domain/prd.md` — public API and target operations.
- `spec/data-model.md` — full type definitions.
- `spec/algorithms.md` — repair cases.
- `properties/functional.md` — invariants (P-entries).
