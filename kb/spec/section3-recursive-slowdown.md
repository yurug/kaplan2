---
id: section3-recursive-slowdown
domain: spec
status: active
source: KT99 §3 "Recursive Slow-Down" (jacm-final.pdf pp. 582–583)
last-updated: 2026-06-02
---

# KT99 §3 — Recursive Slow-Down (faithful transcription)

This is the *why* behind worst-case O(1). The paper is explicit that the idea
"is not explicit in our ultimate construction and is not needed to understand
it" — but it is the cost argument that the rebuild's invariant must mechanize.
See also [`section4-representation.md`](section4-representation.md) (where the
mechanism is instantiated) and [`section4-repair-cases.md`](section4-repair-cases.md)
(the §4.2 operation trace).

## The recurrence (p. 582)

Buchsbaum–Tarjan structures obey `T(n) = O(1) + c·T(log n)`. If `c < 1`, the
recurrence `T(n) = O(1) + c·T(n−1)` gives `T(n) = O(1)`. So:

> An O(1) time bound is obtained if each operation requires O(1) time **plus at
> most a fixed fraction (< 1) of an operation on a smaller recursive
> substructure** — equivalently, one substructure operation per *two* top-level
> operations. This is **recursive slow-down**.

## Work allocation = binary counting (p. 583)

Allocate work cycles so the top level gets ½, the next ¼, the next ⅛, … — the
bit-change pattern of repeated `+1` in binary. To make each `+1` change only a
**constant** number of digits (avoid carry propagation), use a **redundant
binary representation (RBR)**.

### Regular RBR (p. 583) — the formal invariant
Digits `dₙ…d₀`, each `dᵢ ∈ {0,1,2}`, value `Σ dᵢ2ⁱ`. An RBR is **regular** iff:

> for every `j` with `dⱼ = 2`, there is an `i < j` with `dᵢ = 0` and `dₖ = 1`
> for all `i < k < j`.

I.e. scanning most- to least-significant, **after a 2 you must hit a 0 before
the next 2** (or before running out). In particular `d₀ ≠ 2`.

### `+1` in O(1) digit changes (p. 583)
Add 1 to `d₀`; restore regularity by finding the least-significant non-1 digit
`dᵢ`: if `dᵢ = 2`, set `dᵢ := 0` and `dᵢ₊₁ += 1`; if `dᵢ = 0`, do nothing.
**Changes only a constant number of digits.**

## Colors instead of digits (p. 583) — the load-bearing scheme

Three states ↔ three digits {0,1,2}, rendered as **colors**. Each level of the
recursive structure is **green, yellow, or red**.

> A red structure is bad but can be converted to green at the cost of degrading
> the structure one level deeper (green→yellow or yellow→red).
>
> **Invariant: any two red levels are separated by at least one green level,
> ignoring intervening yellow levels.**

The green-yellow-red mechanism over a *linear* structure gives constant-time
catenation for stacks. For **deques** (a *tree* skeleton, needed to handle both
pop and eject) the mechanism is extended with a fourth color, **orange**, and a
**three-beat** rhythm; the O(1) bound there comes from `2/3 < 1` ("2" = tree
branching factor, "3" = work-cycle rhythm). That extension is §6
([`section6-catenable-deques.md`](section6-catenable-deques.md)).

## What the rebuild must take from §3

- The cost proof is **not** amortized: it is the RBR/color invariant making each
  `+1` (each operation) touch a constant number of levels.
- The invariant to mechanize for the non-catenable deque is exactly the
  green/yellow/red separation rule above; for the catenable deque it is the
  GYOR three-beat extension. This is the spec the keystone theorems must state
  *unconditionally*.
