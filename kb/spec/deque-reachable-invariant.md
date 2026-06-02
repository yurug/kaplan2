---
id: deque-reachable-invariant
domain: spec
status: decided
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

## Decision (2026-06-02): abstract chain bound, no jump pointer

The keystone targets the **abstract chain bound** — cost = cell touches in the
model — proving the bounded repair offset from the packet / yellow-run bundling
already present in `KChain` (`KCons color packet chain`). We do **not** mechanize
`jump4`; the imperative heap bound becomes an optional future refinement, not the
keystone. This is the deliberate move that sidesteps the heap-realizability
bridge (`all_role_heap_packet_view_repr`) that the accretion never closed.

Consequences for the proof (Phase 4):
- The O(1) operation is the **non-recursive single repair** (one
  `green_of_red_k` dispatch — already proven `*_green_calls_le_1`), **not** the
  recursive `push_chain_full` (which `CLAUDE.md` flags as an O(log n) proof
  artifact). Cost = the existing packet budgets (`NF_PUSH_PKT_FULL` etc.).
- The remaining open work shrinks to **abstract totality + preservation**: define
  `I` = `regular_kt` **plus** the consistency that makes the single repair
  *total*, and prove `empty ⊨ I`, every op preserves `I`, and `I` ⇒ the
  single-repair precondition. This is tractable in a way the heap bridge was not.
- Clauses (2) heap-faithfulness and (3) heap re-entrancy in the proposed `I`
  above are **dropped** (they belonged to the imperative target); `I` is purely
  an abstract-chain predicate.

## Pinned `I_kt` — validated against the code (2026-06-02)

Traced where every op actually fails (`OpsKT.v`) and what `green_of_red_k`
(`OpsKT.v:1084`) needs. `kt4_total_state` (`PublicTheorems.v:7780`) already
encodes top-level totality but is **not push-closed** because it asserts its
conditions only at the top, not recursively. The validated invariant has **three
ingredients**, all abstract-chain predicates:

1. **`regular_kt c`** (`OpsKTRegular.v:164`) — reds separated by greens
   (ignoring yellows); packets are `PNode`. *Already proven preserved.*
2. **`colors_consistent c`** — at **every** link and inside every packet's
   yellow-run `PNode`s:
   - `Green`-tagged ⟹ both buffers `buf5_is_green_shape` (`B2`/`B3`);
   - `Yellow`-tagged ⟹ both buffers `buf5_is_not_red_shape` (`B1`–`B4`).
   This kills the *immediate* `PushFail` arms (`OpsKT.v:1485,1497,1499,1500`):
   push on a `Green` link needs prefix `∈ {B2,B3}`; on a `Yellow` link needs
   prefix `∈ {B1..B4}`.
3. **`well_leveled c`** — at chain-depth `k`, every element in the level-`k`
   buffers has `E.level = k`, **and if `k > 0` it is unpairable**
   (`∃ x y, E.unpair e = Some (x,y)`). *This is the ingredient my first
   hypothesis missed.* The repair's buffer-concat ops (`green_prefix_concat`
   etc., `OpsKT.v:408`) re-pair the overflow via `E.pair` — needing
   `E.level c = E.level d` (`OpsKT.v:423`), from the level clause — and in the
   underflow arm `E.unpair` the popped deep element, needing the unpairability
   clause. (Reuses Model.v's existing `buf_all_at_level`/`packet_levels`/
   `chain_levels` for the level part, lifted to `KChain`.) This is what the old
   `kt4_*_packet_view_ready` predicates (`PublicTheorems.v:679`) were grasping at.

`I_kt c ≜ regular_kt c ∧ colors_consistent c ∧ well_leveled c`.

### Why `I_kt` is push-closed (the crux the accretion missed)
`green_of_red_k` returns `None` only via its buffer-concat ops (under
`regular_kt` the catch-all `_ ⇒ None` at `OpsKT.v:1116` is unreachable: tails are
`KEnding`/`PNode`-headed, so Cases 1–3 cover it). Each concat op
(`OpsKT.v:408–506`) succeeds when the **level-below** buffer is green-sized
(so `green_push` doesn't hit a full `B5`) and the elements are well-leveled (so
`E.pair`/`E.unpair` succeed). `colors_consistent` gives the first
**recursively** (so the green below a red is green-*sized* at every depth, not
just the top), and `well_leveled` gives the second. Hence:

> **Crux lemma.** If `regular_kt (KCons Red p tail)`, `colors_consistent`, and
> `well_leveled`, then `green_of_red_k (KCons Red p tail) = Some c'` and `c'`
> satisfies `regular_kt ∧ colors_consistent ∧ well_leveled` with a green/yellow
> top. (Decomposes into 4 buffer-op totality+preservation lemmas for
> `green_prefix_concat` / `green_suffix_concat` / `prefix_concat` /
> `suffix_concat` + 1 for `make_small`.)

### The unconditional keystone
> **`deque_wc_o1`.** `empty_kchain ⊨ I_kt`; for `op ∈ {push,inject,pop,eject}`
> and every `c` with `I_kt c` (and `kt4_nonempty_state c` for pop/eject):
> `op c ≠ Fail`, the result satisfies `I_kt`, and the operation dispatches
> `green_of_red_k` at most once, so its cost is ≤ the proven packet budget
> (`NF_PUSH_PKT_FULL` / `NF_POP_PKT_FULL`). No heap-view premise.

### Proof architecture (Phase 4a, bottom-up; new file `DequePtr/DequeKeystone.v`)
1. Buffer-op lemmas: `green_prefix_concat`/`…_suffix`/`prefix_concat`/`suffix_concat`
   total + green/not-red-preserving + level-preserving when the level-below
   buffer is green-shaped and well-leveled; same for `make_small`.
2. Crux lemma (above) by the 3 `green_of_red_k` cases.
3. `I_kt ⟹ kt4_total_state` (top-level totality precondition) — discharges the
   recursive `green_of_red_k`-success clauses from (2).
4. `colors_consistent` + `well_leveled` preserved by each op (reuse existing
   `*_kt4_preserves_regular_top` for ingredient 1).
5. `deque_wc_o1`, then a `Print Assumptions` audit; the new gate checks
   `deque_wc_o1` itself.

### Element-interface check (resolved 2026-06-02 — corrected)
Ingredient 3 (`well_leveled`) interacts with `Common/Element.v`. Status after
reading the `ELEMENT` module type **and both instances**:
- **Overflow direction — covered by the existing interface.** The overflow arms
  need `E.level c = E.level d` for the ejected pair (`OpsKT.v:423`); the level
  clause of `well_leveled` gives it, and `level_pair` gives the re-paired
  element level `k+1`. `unpair_level` (`Element.v:247`) handles the reverse.
- **Underflow direction — do NOT add an `ELEMENT` axiom.** First instinct was to
  add `level e = S l → ∃ x y, unpair e = Some …` to the module type. **That is
  false for `ElementFlat`:** an `XFP l r` with `level l ≠ level r` has positive
  `level` but `unpair = None` (the `Nat.eq_dec` guard, `Element.v:343–347`). So
  it is not a theorem of every instance and must not be an axiom.

**Resolution:** put unpairability **in the invariant**, not the interface.
`well_leveled` requires depth-`k` (`k>0`) buffer elements to be unpairable
(clause 3 above). This is sound because every deep element the algorithm ever
stores is produced by `E.pair`, which `unpair_pair` makes unpairable — so the
property is *preserved* by the ops and need not be assumed of arbitrary elements.
**No `ELEMENT` change; no new axiom.** (Catching this required checking the
instances, not just the module type — exactly the value of validating before
proving.)
