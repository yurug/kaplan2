---
id: section4-representation
domain: spec
status: active
source: KT99 §4.1 "Representation" (jacm-final.pdf pp. 584–586)
last-updated: 2026-06-02
---

# KT99 §4.1 — Non-catenable deque representation (faithful transcription)

Completes the §4 deque spec: this is the representation + regularity invariant;
[`section4-repair-cases.md`](section4-repair-cases.md) is the §4.2 operation
trace. The cost rationale is [`section3-recursive-slowdown.md`](section3-recursive-slowdown.md).

## Structure (p. 584)

A nonempty deque `d` over `A` is an ordered triple
`(prefix(d), child(d), suffix(d))` where:
- `prefix`, `suffix` are **buffers** holding **0–5 elements** of `A`;
- `child(d)` is a deque whose elements are **ordered pairs** of elements of `A`
  (recursive, unwinds linearly).

Descendants: `child⁰(d)=d`, `childⁱ⁺¹(d)=child(childⁱ(d))`. Element of `childⁱ(d)`
= complete binary tree of depth `i` (2ⁱ leaves in `A`). Level `i` holds the
prefix+suffix of `childⁱ(d)`.

**Two-for-one payoff (p. 585):** pairing means one pop/eject at level `i+1`
brings *two* elements up to level `i`; one push/inject at level `i+1` moves *two*
down. This is the recursive slow-down made concrete.

## Colors (p. 585)

Buffer color by size:

| size | 0 | 1 | 2 | 3 | 4 | 5 |
|------|---|---|---|---|---|---|
| color| red | yellow | green | green | yellow | red |

- **green = 2 or 3**, **yellow = 1 or 4**, **red = 0 or 5**.
- A green/yellow buffer absorbs one push or pop without violating `[0,5]`:
  green→(green|yellow), yellow→(green|red).
- Order **red < yellow < green** (red bad, green good).
- **Deque color** = min(color(prefix), color(suffix)) — *unless* the child and
  one buffer are empty, in which case it is the color of the nonempty buffer.

## Regularity invariant (p. 585) — the keystone for the deque

On the descendant sequence `d, child(d), child²(d), …`:

- **semiregular**: between any two red deques there is a green deque, ignoring
  intervening yellows. Formally: for any red `childⁱ(d)`, `childʲ(d)` with `i<j`,
  there is `k`, `i<k<j`, with `childᵏ(d)` green.
- **regular**: semiregular *and* the first non-yellow deque in the sequence (if
  any) is green.

Consequences (p. 585): if `d` is regular or semiregular then `childⁱ(d)` is
semiregular for `i>0`; if `d` is semiregular and red then `child(d)` is regular.

**Maintained invariant:** any top-level deque is **regular**, except
*temporarily semiregular* mid-operation.

## Why one operation = O(1) repair (pp. 585–586)

A regular deque has a green/yellow top, so any op acts on the top buffer,
possibly degrading top green→yellow→red. If the topmost non-yellow descendant is
now red, the deque is only semiregular. **Restore regularity by changing that one
red deque to green**, which may degrade its child green→yellow or yellow→red/green
— exactly `+1` in the RBR. The repair moves elements only between the red deque's
buffers and its child's buffers (preserves elements/order), then restores the
levels above.

### The jump-pointer / substack representation (p. 586) — CRUCIAL for O(1)
The topmost red deque may be arbitrarily deep (many yellows above it). For
real-time performance we need **constant-time access to the topmost red deque**.
So the deque is **not** stored as a flat stack of prefix–suffix pairs; it is
broken into **substacks**:

- one substack for the top-level deque, and one for each non-yellow descendant
  not at top level; each substack = a (top/non-yellow) deque plus all
  consecutive yellow proper descendants.
- Equivalent **pointer node** per nonempty descendant `d`: **four pointers** —
  to its prefix, to its suffix, to the child node *if that child is nonempty and
  yellow*, and **to the node for the nearest non-yellow proper descendant** (if
  it exists and `d` is non-yellow or top-level). *This last pointer is the "jump
  pointer."*

> **A single deque operation requires access to at most the top three substacks,
> and at most the top two elements in any such substack.** Color changes produce
> only minor, constant-time changes to the substack partition (a substack push
> or pop).

## What the rebuild must take from §4.1

- The invariant `I` = "top-level deque regular" per the definition above.
- O(1) is **not** achievable on the naive flat representation: it *requires* the
  substack/jump-pointer compressed structure so the topmost red is reachable in
  O(1) and each op touches ≤ 3 substacks. This is precisely the
  `D4Cell.jump4` that `CLAUDE.md` notes is **currently unused** in the Rocq port
  — the gap analysis is in [`deque-reachable-invariant.md`](deque-reachable-invariant.md).
