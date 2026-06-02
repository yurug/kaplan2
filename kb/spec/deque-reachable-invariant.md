---
id: deque-reachable-invariant
domain: spec
status: draft
last-updated: 2026-06-02
---

# Deque reachable-state invariant (Gate-B keystone) — paper-spec draft

**For review.** This is the paper-first design of the *one* invariant the
non-catenable deque keystone theorem needs, derived from KT99 §3+§4
([`section3-recursive-slowdown.md`](section3-recursive-slowdown.md),
[`section4-representation.md`](section4-representation.md)). No Rocq is written
against it until you sign off.

## The unconditional theorem we want

> **`deque_wc_o1`**: there is an invariant `I` on deque states such that
> `empty ⊨ I`; each of `push/inject/pop/eject` maps `I`-states to `I`-states; and
> for every `I`-state, the operation **never fails** and executes in a number of
> cell touches bounded by a fixed constant `K`, independent of size and history.

Today only a *conditional* form exists:
`kt4_all_role_heap_packet_view_exec_cost_refinement_contract` proves the
constant-cost/refinement step **assuming** `kt4_all_role_heap_packet_view_repr`
on the input (see [`../reports/honest-audit-2026-06-02.md`](../reports/honest-audit-2026-06-02.md)).
The missing half is establishing+preserving that premise on reachable states.
`I` *is* that premise, stated so it is actually closed.

## What is already proven (assets to keep)

- **`regular_kt`** (`DequePtr/OpsKTRegular.v:164`) — the §3/§4 color invariant on
  the colour-tagged `KChain`, stated locally:
  - `KEnding b` regular;
  - `KCons Green p c`: `p` is a `PNode`, `c` regular;
  - `KCons Yellow p c` / `KCons Red p c`: additionally `kchain_top_color c ≠ Red`.
  This is exactly KT99's "between two reds a green, ignoring yellows" (§4.1
  p. 585) made local: every red/yellow link sits directly above a non-red top.
  It is **preserved by all four public ops** (`*_kt4_preserves_regular_top`).
- **Packet-level repair cost** `packet_*_full_correct_O1_repr_thm` — one packet
  repair costs ≤ `NF_PUSH_PKT_FULL = 9`. ✓

## The gap, precisely

`regular_kt` is a *structural color* invariant on the **abstract** chain. The
cost contract is stated over the **imperative heap** (`exec_*_C` on
`Heap (D4Cell …)`). The keystone needs a bridge invariant —
`kt4_all_role_heap_packet_view_repr` — asserting that the heap **faithfully
represents** a regular chain *and* that, after executing any of the four ops, the
result is again such a represented, re-enterable state. `regular_kt` does **not**
imply it (the audit's `*_not_push_closed` chain proves successive candidate
bridges fail — notably the terminal-`B5` states that need different front/back
packet normal forms, and the nested-underflow pending-`B0` view).

The accretion tried to *discover* this bridge invariant by patching the heap-view
candidate. It never closed. **The fix is to state `I` from the paper's
representation, not from the heap-view candidate.**

## Paper grounding — the missing structural ingredient

KT99 §4.1 (p. 586) is explicit that O(1) is **not** achievable on a flat
representation: it requires the **substack / jump-pointer compressed structure**
so the topmost red deque is reachable in O(1) and each op touches ≤ 3 substacks.

- The abstract `KChain` *does* bundle yellow runs into packets (`KCons color
  packet chain` — Viennot's GADT shape), which is the substack idea at the model
  level: the topmost red is a bounded number of `KCons` links down because reds
  are separated by greens.
- But the **imperative jump pointer** (`jump4`, the "pointer to nearest
  non-yellow descendant", §4.1 p. 586) exists **only** in
  `c/experiments/ktdeque_d4cell.c` — *not* in the Rocq port and *not* in
  production C. That experiment itself notes its repair is "O(depth) in the worst
  case" without jump4 (`ktdeque_d4cell.c:701`). So the heap layer the cost
  contract reasons about has no structural witness that "locate the repair site"
  is O(1); the all-role invariant has been trying to assert re-enterability
  without the representation that guarantees it. This matches `CLAUDE.md`'s hard
  rule: *"bounded cascade depth via jump pointers (`D4Cell.jump4`, currently
  unused)."*

## Proposed invariant `I` (to mechanize)

`I(state)` ≜ all of:
1. **Regularity:** `regular_kt` on the abstract chain (already preserved).
2. **Faithful compressed representation:** the heap at the root decodes
   (`chain_repr`) to that regular chain, with yellow runs bundled into packets
   (the substack partition), so the topmost non-yellow / topmost red link is at a
   bounded offset from the root.
3. **Re-entrancy:** after any op's `exec_*_C`, the output heap again satisfies
   (1)+(2) — this is the part `all_role_heap_packet_view_repr` was reaching for,
   but now provable because (2) pins the layout.

Then `deque_wc_o1` follows from: `I ⇒ all_role_repr` (by construction of (2)+(3))
+ the existing packet-level cost bound + "one repair per op" (regularity bounds
the cascade to a single red→green conversion).

## Rebuild actions implied (for Phase 4, after sign-off)
- Decide whether to mechanize the jump pointer in the imperative layer
  (`D4Cell.jump4`) so clause (2) has a real O(1)-locate witness, or to prove
  the bounded offset purely from the packet/chain structure. KT99 says the
  pointer is needed for the imperative bound; the abstract bound may follow from
  the bundling alone. **This is the key design choice for 3a.**
- State `I` and `deque_wc_o1` first; only then prove preservation. Do **not**
  reintroduce the `*_ready_state` candidate ladder.

## Open question for the reviewer
Is the intended production target the **abstract** chain bound (cost = cell
touches in the model, where packet bundling already gives the O(1) offset), or
the **imperative** heap bound (which per KT99 needs `jump4`)? The honest-audit
cost contract is stated at the imperative `exec_*_C` layer, so faithfully closing
it points to mechanizing `jump4`.
