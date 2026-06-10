# SESSION_STATE — rebuild (Phase 4b in progress)

## PHASE 4b STATUS (2026-06-03)
DONE, committed green: kb/spec/catenable-type-design.md (design memo);
Catenable/Model.v (types: stored/cnode/cbody/cpacket/cchain + mutual sequence
semantics + examples); Catenable/Color.v (computed GYOR node_color, node_sizes
floors, the invariant J = chain_wf + chain_ends_green; empty_J, singleton_J).
J v1 deliberately omits level-stratification (recorded in-file; add in place if
an obligation demands it).

DONE also: Catenable/Ops.v with push/inject (colour-driven surgery via root_and_child/tree_of;
pkt_update = compose) AND concat (Cases 1-4 + 1a-1d, sequence-verified by vm_compute incl.
Case 1 CPair path). DONE also: pop/eject + §6 repair (Cases 1/2a-2c; pair-collapse via Viennot vector path;
drain-verified by vm_compute). DONE also: CatKeystone.v skeleton — cat_keystone_{empty,push,inject,concat,pop,eject}
proven from 7 Admitted obligations (functional keystone; empty already closed).
STATUS: 5 admits remain (cad_push/inject_seq DISCHARGED via SeqLemmas:
push_chain_seq/inject_chain_seq under chain_wf + chain_wf_root_prefix/suffix side
conditions + tree_of_seq/root_and_child_seq sequence-neutrality).
REMAINING obligations, in suggested order:
1. cad_push/inject_preserves_J — the surgery J-preservation (4a-style): prove
   tree_of preserves chain_wf/ends_green given node sizes+colour facts; node_push
   keeps sizes (only grows); receiver side conditions as in the seq lemmas.
2. cad_concat_total_J_seq — totality: every option arm Some under J (buf_eject2/
   pop2 sizes from J floors; make_left/right case-by-case); J of outputs (tree_of
   J-rebundling + the new node sizes per case — 1a/1c stored >=3 etc.); sequence
   via SeqLemmas + buf_stored_seq_app (stored_seq of SBig/SSmall unfold).
3. cad_pop/eject_total_J_seq — HERE J grows the level clause: popped element
   SGround needs stratification (add stored_level-style Prop to J in Color.v, in
   place; re-check empty_J/singleton_J and prior discharges). Repair totality:
   red terminal => child nonempty (colour def) => pop_raw Some; repair J: spliced
   node green (>=8 sizes per §6 Lemma 6.4); repair seq via SeqLemmas + concat seq.
THEN cost layer + gate. REMAINING for 4b (orig): (a) DISCHARGE the 7 obligations (expected: J grows the level/
stratification clause at pop-totality — SGround-ness is level-0; push/inject seq
needs J sizes for the empty-prefix suffix-push case; tree_of/root_and_child seq
lemmas are the workhorses — prove cchain_seq (tree_of n c) = cnode_seq n (cchain_seq c)
and the root_and_child inverse first); (b) then the COST layer: primitive-count
counters mirroring the frozen op code + constant bounds => cat_wc_o1; (c) gate:
point the catenable gate profile at cat_wc_o1. Old note: CatKeystone.v (cat_wc_o1 from admitted
obligations: J-preservation for all 5 ops, totality of the option-returning concat/pop/eject
under J, sequence correctness, primitive-count bound).

OLD design note for push/inject (KT99 Lemma 6.1 made
structural — the path surgery):
- push onto CEmpty => singleton only-triple.
- push onto CSingle (Pkt body n) rest: the receiving node = head of body (or n
  if body=BHole); push onto its prefix (suffix if prefix empty). Colour
  transitions change the PATH DECOMPOSITION (KT99: "adds t to or deletes t from
  the front of a preferred path"):
  * Y->G (head body node becomes green): SPLIT the packet — head becomes its
    own green packet: CSingle (Pkt BHole t') (CSingle (Pkt body_rest n) rest).
  * O->Y (head was BPairO t lc b'): preference flips right->left. New preferred
    continuation = INLINE the parked green-left chain lc = CSingle (Pkt lb ln)
    lrest: new packet = Pkt (BPairY t' lb) ln over lrest; the OLD continuation
    becomes the parked RIGHT chain = CSingle (Pkt b' n) rest. (Yellow's
    nonpreferred child needs no green condition — checked, clause 2 is
    orange-only.)
  * G stays G / Y stays Y / O stays O: in-place buffer push, no surgery.
  * Top node green that becomes... push on a GREEN top only adds elements =>
    >=8 stays >=8?? push INCREASES sizes: G stays G; Y(7)->G(8); O(6)->Y(7);
    R(5)->O(6) (red top can't occur under J's chain_ends_green at top).
  So push transitions are colour-INCREASING (toward green) — the easy
  direction; pop/eject decrease and trigger the red repair.
- Helpers to write first: node_push/node_inject (buffer-level), packet head
  access, the Y->G split and O->Y flip as named functions; then push/inject;
  Lemma 6.1 analogue = push preserves J (semiregular/regular split per KT99).
- THEN concat (Cases 1-4; constant element moves), THEN pop/eject repair
  (Cases 1, 2a-2c — uses concat recursively at the child level per KT99 Case
  1a! NOTE: KT99 pop-repair Case 1a calls CATENATE on child deques (d2 and
  d1''): the repair is NOT concat-free. cost story still constant: one level,
  constant catenations).
- Keystone: CatKeystone.v cat_wc_o1 from admitted obligations (rule 6).

Running unattended (user asleep) to progress the rebuild plan. Read this first.

## PHASE 2 (re-curation) DONE 2026-06-03
Non-canonical variants removed from rebuild (preserved on archive, pushed): rocq
Cadeque6/7/8/9 + Buffer6 + Public + catenable extractions; OCaml experimental lib
+ 24 catenable benches + viennot_cad + catenable tests/examples; Makefile/gate-script
catenable targets (catenable profile now SKIPs with archive pointer). All green:
rocq, ocaml, runtest, C check, 4 gate profiles, keystone gate 4/4. release-gate
anchors deque-keystone-gate.
NEXT = Phase 4b (catenable, fresh KT99 §6/Viennot build). First design task (do in
a FRESH focused session, paper-first like 4a): the Rocq type encoding of §6's
non-uniform recursion (triple = prefix/middle/suffix where the middle deque's
elements are STORED TRIPLES) + GYOR colours + preferred paths + the compressed
forest (adoptive pointers) for O(1) topmost-red access. Then J + cat_wc_o1 stated
top-down from admitted obligations (methodology rule 6). Mine
external-refs/VerifiedCatenableDeque (Color/GYOR.v, Cadeque/) for design only.

## ★★★ PHASE 4a CLOSED (2026-06-03) ★★★
`rocq/KTDeque/DequePtr/DequeKeystone.v`: **ZERO admits**; `deque_wc_o1_{push,inject,pop,eject}`
all report **Closed under the global context**. The unconditional WC-O(1) deque keystone is
proven (totality + I_kt preservation + one-repair cost bound; empty ⊨ I_kt; push/inject take
E.level x = 0). Whole rocq/KTDeque theory builds green. Mission item 1 DONE; item 2 (RBR) DONE.
NEXT (mission item 3, only if continuing): catenable Phase-4 per kb/spec/catenable-concat-invariant.md
— this is a LARGE fresh build (KT99 §6/Viennot GYOR structure); prefer to leave for the user's
review of the keystone unless instructed otherwise. Remaining small follow-ups instead:
(a) point a minimal gate at deque_wc_o1_* (+ keep frontier greps out), (b) consider linking
green-calls bound to NF_PUSH_PKT_FULL in DequeKeystone's Print Assumptions block.

## Branch / build
- Work ONLY on branch `rebuild`. Do NOT push (push needs human approval).
- Build: `eval $(opam env --switch=default 2>/dev/null); dune build rocq/KTDeque/DequePtr/DequeKeystone.vo` (and `dune build rocq/KTDeque` for the whole theory).
- `dune` is at `/home/yann/.opam/default/bin/dune`; `make` does NOT see it (it uses /bin/sh) — call `dune` directly after sourcing opam env.

## Mission (in priority order)
1. **Close Phase 4a — the deque keystone** in `rocq/KTDeque/DequePtr/DequeKeystone.v`. Discharge the remaining `Admitted` obligations until zero admits + clean `Print Assumptions` on `deque_wc_o1_{push,inject,pop,eject}`.
2. If 4a closes: finish `rocq/KTDeque/RBR/Succ.v` (close the one `Abort.`) — decision #2.
3. If those close: begin the catenable Phase 4 proof work per `kb/spec/catenable-concat-invariant.md` (§6/Viennot GYOR) — additive only.

## Current state (as of start)
- `DequeKeystone.v` compiles. `deque_wc_o1_*` proven modulo **5 admits**:
  - `I_kt_implies_kt4_total_state` (totality core)
  - `push/inject/pop/eject_kt4_preserves_I_kt` (preservation)
- 4 totality obligations already discharged (Qed) by reducing to the single lemma above via existing infra.
- Invariant: `I_kt c := regular_kt_top c /\ colors_consistent c /\ well_leveled c` (see `kb/spec/deque-reachable-invariant.md`).

## The crux to solve
The residue is **recursive green-readiness / repairability** (the KT cascade bound):
- `kt4_total_state`'s Green clause needs `yellow_wrap_pr_total_pre tail` = (tail Red-headed ⇒ `green_of_red_k tail = Some`).
- `green_of_red_k_ready_at` Case 2 (Hole-inner red over a `KCons` tail) needs the tail's buffers **green-shaped**, not just not-red.
- Hypothesis to encode in `colors_consistent`: every link's tail is "green-ready" — a `Hole`-inner link's tail is Green-headed (green buffers) or `Ending`; and every red-headed tail is repairable. Make this RECURSIVE.
- Then `I_kt_implies_kt4_total_state` should follow via `green_of_red_k_total_under_ready_levels`. The hard part shifts to **preservation** (the 4 `*_preserves_I_kt`): the green-ready clause must survive push/inject (green→yellow at same depth) and the `green_of_red_k` repair (Case 1/2 produce green heads; Case 3 produces a green head over a fresh red inner — check it stays repairable) and pop/eject.

## Reuse (do NOT reprove these — they exist + are audited)
- `green_of_red_k_total_under_ready_levels`, `green_of_red_k_case{1,2,3}_total_under_levels`, `green_of_red_k_ready_at`, `green_of_red_k_context_ready_at`, `green_of_red_k_ready_at_from_context` (PublicTheorems.v).
- `kt4_total_state_{push,inject,pop,eject}_pre`, `{push,inject,pop,eject}_kt4_total_under_pre` (totality plumbing — already wired in DequeKeystone).
- `{push,inject,pop,eject}_kt4_preserves_regular_top` (the regular_kt_top half of preservation — REUSE for the regular component).
- `{push,inject,pop,eject}_kt4_green_calls_le_1` (cost — already wired).
- Model.v: `buf_all_at_level`, `packet_levels`, `chain_levels`.
- Element is concrete `ElementTree` (Model.v:61) — positive-level elements unpair (a theorem); use it for `well_leveled`'s unpairability needs.

## METHODOLOGY / GUARDRAILS (do not violate)
- **Top-down with tracked admits** (rebuild plan rule 6): use `Admitted` (never `admit.`). The admit set is the to-do list via `Print Assumptions`.
- **Never leave the build broken.** Only `git commit` when `dune build rocq/KTDeque/DequePtr/DequeKeystone.vo` exits 0. If an edit breaks the build and you can't fix it quickly, `git checkout -- <file>` to revert and try a different approach.
- **Net admits must not increase** across a commit unless a big admit is split into strictly smaller, precisely-stated ones.
- **One invariant, refine in place.** Do NOT spawn many named candidate predicates (that is the accretion anti-pattern that failed before). Refine `colors_consistent` / `I_kt` directly.
- **No destructive operations.** Do NOT delete files, do NOT do the Phase-2 re-curation (removing Cadeque variants) — that needs human go-ahead. Additive proof work only.
- **Commit frequently** with descriptive messages; end every commit message with:
  `Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>`
- Update this SESSION_STATE.md after each meaningful step (admit count, what changed, next step) so progress survives context resets.
- If genuinely stuck on the green-readiness invariant after several honest attempts, do NOT churn: record the precise obstruction in `kb/spec/deque-reachable-invariant.md` + here, make sure everything is committed green, and move to mission item 2 (RBR) so the night is still productive.

## make_small_preserves_levels roadmap (mapped 2026-06-03)
Target: `make_small b1 b2 b3 = Some c -> buf_all_at_level k b1 -> buf_all_at_level (S k) b2 -> buf_all_at_level k b3 -> chain_levels k c`. (Then `green_of_red_k` Case 1 = `chain_to_kchain_g`, which preserves levels — needs a trivial `chain_to_kchain_g` level lemma since it only adds Green tags; well_leveled_at k c <-> chain_levels k (kchain_to_chain c), and kchain_to_chain (chain_to_kchain_g c) = c.)
9 cases (prefix_decompose b1 x suffix_decompose b3). Reuse EXISTING (do not reprove):
- `pair_each_buf_after_halve_preserves_levels` (PublicTheorems.v:12127) + `..._total_under_levels` (7241) — Overflow/Overflow case.
- `suffix_rot_unpair_total_under_levels` (7279), `prefix_rot_unpair_total_under_levels` (7305) — Underflow/Overflow + Overflow/Underflow.
- `make_small_total_under_levels` (7331) — existence (pattern to mirror).
- `make_small_chain_to_kchain_g_context_ready` (7452) — shows the output-shape reasoning per case (mirror its case structure).
Need NEW trivial level lemmas: `prefix23` (OpsKT.v:273), `suffix23` (280), `suffix12` (288), `mk_ending_from_options` (594), `buffer_unsandwich` (349), `buffer_push_chain`/`buffer_inject_chain` level-preservation, `buf5_push_naive`/`buf5_inject_naive`/`buf5_pop_naive`/`buf5_eject_naive` (have `buf5_*_preserves_levels` in OpsAbstract.v 211-243). Most simple cases close by cbn + the E.unpair_level/E.level_pair facts (pattern as in `prefix_concat_preserves_outer_green_levels` proof, PT:6512).

## make_small_preserves_levels — ATTEMPT NOTE (2026-06-03)
A uniform automation that ALSO destructs b2 into 6 => 216 cases x heavy tactics (repeat constructor + lia + E.level_pair rewrites) ran >5 min without finishing — too slow, reverted. DO NOT destruct b2. Instead: `unfold make_small in Hmake`, destruct b1+b3 (36 cases), and in each case handle b2's ONE operation via its helper lemma WITHOUT destructing b2:
  - (underflow,underflow): `buffer_unsandwich b2` -> `buffer_unsandwich_levels`.
  - (underflow,ok)/(ok,underflow): `buf5_pop_naive`/`buf5_eject_naive b2` -> `buf5_pop/eject_preserves_levels` (OpsAbstract); `buf5_push/inject_naive` -> `buf5_push/inject_preserves_levels`.
  - (underflow,overflow)/(overflow,underflow): `suffix_rot`/`prefix_rot` -> `suffix_rot/prefix_rot_preserves_levels`, then `E.unpair` -> `element_unpair_at_s_levels`.
  - (ok,ok): output `ChainCons (PNode p1' Hole s1') (Ending b2)` directly; p1'/s1' are b1/b3 (level k), b2 level (S k).
  - (ok,overflow)/(overflow,ok): `buffer_inject_chain`/`buffer_push_chain b2 (E.pair ..)` -> `buffer_*_chain_levels` (the pair is level S k).
  - (overflow,overflow): `buffer_halve` + `pair_each_buf` -> `pair_each_buf_after_halve_preserves_levels`; `suffix12` -> `suffix12_levels`.
  Each case: get the component levels from the helper, then prove chain_levels via constructors + `prefix23_levels`/`suffix23_levels`/`mk_ending_from_options_levels`. Keep buffer ops folded with `cbn -[E.pair E.unpair buffer_unsandwich buf5_pop_naive buf5_eject_naive suffix_rot prefix_rot buffer_halve pair_each_buf buffer_push_chain buffer_inject_chain]`. This is ~9 distinct case bodies, fast.

## make_small_preserves_levels — FOUNDATION COMPLETE (2026-06-03)
All 10 helper level lemmas proven (Qed) in DequeKeystone.v: `prefix23_levels`, `suffix23_levels`, `suffix12_levels`, `mk_ending_from_options_levels`, `buffer_push_chain_levels`, `buffer_inject_chain_levels`, `buffer_unsandwich_levels`, `suffix_rot_preserves_levels`, `prefix_rot_preserves_levels`, `element_unpair_at_s_levels`. Plus existing reuse: `pair_each_buf_after_halve_preserves_levels` (PT:12127), `buf5_{push,inject,pop,eject}_preserves_levels` (OpsAbstract:211-243), `E.unpair_level`/`E.level_pair`.
ASSEMBLY RECIPE for `make_small_preserves_levels` (forall k b1 b2 b3 c, level k b1 -> level (S k) b2 -> level k b3 -> make_small b1 b2 b3 = Some c -> chain_levels k c):
  `unfold make_small in Hmake`; destruct b1, b3 (prefix/suffix_decompose). For the 9 (pre-decomp x suf-decomp) cases, the inner matches in Hmake on `buffer_unsandwich b2` / `E.unpair _` / `Nat.eq_dec` / `suffix_rot`/`prefix_rot`/`buffer_halve`/`pair_each_buf` give the output; `destruct (E.unpair ..) eqn:Hup; [|discriminate]` then use `element_unpair_at_s_levels` for the pair levels (need `E.level elem = S k` from `buffer_unsandwich_levels`/`buf5_pop/eject_preserves_levels`/`suffix_rot/prefix_rot_preserves_levels`); `injection Hmake` to get c; then prove `chain_levels k c` via the matching helper (`mk_ending_from_options_levels` / `prefix23_levels`+`suffix23_levels` for the PNode-Hole cases / `buffer_push_chain_levels`/`buffer_inject_chain_levels` for Ok/Overflow / `suffix12_levels`+`pair_each_buf_after_halve_preserves_levels` for Overflow/Overflow). Then `green_of_red_k_preserves_well_leveled` Case 1 = `chain_levels k (make_small ...)` lifted through `chain_to_kchain_g` (trivial: adds Green tags; need `chain_to_kchain_g_well_leveled : chain_levels k c -> well_leveled_at k (chain_to_kchain_g c)`, by induction on c).

## Progress log (newest first)
- 2026-06-03 iter (REPAIR PRESERVATION FULLY CLOSED): PROVED make_small_colors_consistent (structural, no level premises) + green_prefix/suffix_concat_green_shapes + prefix/suffix_concat_outer_green_shape + green_of_red_k_preserves_colors_consistent. Combined with green_of_red_k_preserves_well_leveled, the bounded repair now provably preserves the FULL invariant payload (colours + levels). Build green, 4 admits.
  FINAL STRETCH (the 4 *_preserves_colors_leveled admits): per-op case analysis mirroring the *_total proofs. Arms:
  * KEnding arms: outputs KEnding or KCons Green (B3 Hole B3) (KEnding B0) — structural cc + levels (level-0 elements: push x has E.level x = 0... CAREFUL: preserves lemmas don't have the E.level x = 0 hypothesis! KEnding push B5->Green-split needs buf levels at 0 from well_leveled + pushed x at 0 — MUST add E.level x = 0 to push/inject_kt4_preserves_colors_leveled signatures (mirroring *_total) and thread through push/inject_kt4_preserves_I_kt + deque_wc_o1_push/inject (already have Hx there).
  * Yellow non-overflow arms: buffer +/-1 stays not-red (B1..B3 -> B2..B4 etc.); packet_levels of modified packet (buf5 facts); tail unchanged (cc_tail_color Yellow + cc + wl tail all unchanged).
  * Yellow B4/B1 repair arms: output = green_of_red_k (KCons Red (PNode modified i suf) tail): build cc of that red chain (cc_color_shape Red = I; cc_yellow_run i inherited; cc_tail_color Red tail from input's cc_tail_color Yellow tail (same: tc=Green); cc tail) + wl of it (packet_levels with modified buffer: B5 from B4+x — needs E.level x = 0; B0 from B1-drop ✓) then apply BOTH repair-preservation lemmas.
  * Green arms (yellow_wrap_pr): output KCons Yellow (PNode pre' i suf) tail' where tail'=tail (non-red top) or repaired tail. cc: Yellow shapes (pre' = green+1/-1 = not-red ✓ B4 or B1..); cc_yellow_run i ✓; cc_tail_color Yellow tail': tail Green/Ending => unchanged tc ✓; tail Red => tail' = repaired, top Green (green_of_red_k_top_green, OpsKTRegular:288) ✓; cc tail' via repair-cc lemma; wl tail' via repair-wl lemma (NOTE: repaired at index packet_depth+k — wl input gives tail at that index ✓ same k passes through).
  * Will need a yellow_wrap_pr_preserves lemma first: forall pre' i suf tail k, (premises: packet_levels k (PNode pre' i suf), shapes pre'/suf not-red?? wait yellow link needs not-red shapes of pre' AND suf — suf is the GREEN link's old suf (green => not-red ✓), cc_yellow_run i, cc_tail_color Green->… the input link was GREEN: cc_tail_color Green tail (tc <> Yellow); for output Yellow link need cc_tail_color Yellow tail' (tc' = Green): tail Green-top => ✓; tail KEnding ✓; tail Red-top => repaired Green-top ✓ — all cases OK) -> yellow_wrap_pr pre' i suf tail = PushOk c' -> colors_consistent c' /\ well_leveled_at k c'.
- 2026-06-03 iter (DESIGN FIX: tail-colour discipline): The Hole=>tail_green_ready clause was TOO STRONG — green_of_red_k Case 3 outputs Green-over-fresh-Red with non-green inner buffers (the prior accretion's exact *_not_push_closed counterexample). Refined colors_consistent IN PLACE: new `cc_tail_color col tail` clause (Yellow/Red links over Green-or-Ending; Green over non-Yellow; Yellow top-only); `tail_green_ready` now DERIVED via `tail_green_ready_of_cc` for col<>Green. context_ready/ready_at_of_consistent gained `col <> Green` premise (call sites: eapply with [| exact Hcc | exact Hwl]; discriminate — evar ordering). ALL existing proofs survive. Build green, 4 admits.
  ANALYSIS (verified on paper, record for the colours-preservation proof):
  * Case-1 outputs (chain_to_kchain_g of make_small): all links Green with structurally green buffers (prefix23/suffix23 = B2/B3; BD_*_ok/overflow kept bufs = B2/B3); depth-2 case inner = suffix12/B1 not-red; tails Green-or-Ending => cc holds UNCONDITIONALLY given success. Lemma: make_small_colors_consistent (no level premises; needs prefix_decompose_shapes/suffix_decompose_shapes + prefix23/suffix23/suffix12 shape lemmas + buffer_push/inject_chain cc lemmas).
  * Case-2 output Green link: shapes from green concat lemmas ✓; cc_yellow_run inner: pre2'/suf2' NOT-RED needs new lemma green_prefix_concat_green_b2_not_red (b2 green premise from derived tail_green_ready of the input RED link); cc_yellow_run child + cc_tail_color Green c2 (c2 non-Yellow) + cc c2 INHERITED from input tail link's cc.
  * Case-3 output: Green-over-Red ✓ legal now; R's cc_tail_color Red c1 inherited from input red link's cc_tail_color; cc_yellow_run child inherited.
  * Op-level: push Yellow keeps tail (cc_tail_color Yellow unchanged); push Green -> yellow_wrap_pr outputs Yellow over (tail-or-repaired): repaired is Green-topped (green_of_red_k_top_green, OpsKTRegular:288) ✓; pre'=B4 not-red, suf green=>not-red ✓.
- 2026-06-03 iter (MAJOR: repair level-preservation PROVEN): (a) Fixed well_leveled_at to DEPTH-AWARE tail index `packet_depth p + k` (naive S-k-per-link was FALSE for nested packets; Model.v chain_levels has the same bug — do not use it; use new chain_levels_d). (b) PROVED `make_small_preserves_levels` (goal-carried style: keep Hmake in goal so destructs abstract it — in-hyp rewrites fail under match binders; ms_reduce Ltac keeps blocks folded). (c) PROVED `green_of_red_k_preserves_well_leveled` (3 cases; Case-3 needs colors_consistent for not-red shapes; depth bookkeeping via well_leveled_at_eq+lia; gotcha: re-`cbn in Hwltail` after destructing i1 or lia sees mismatched packet_depth atoms). Also: chain_to_kchain_g_well_leveled, well_leveled_at_eq, prefix/suffix_decompose_levels. Imports added: Buf5Ops, OpsAbstract. Build green, 4 admits.
  NEXT: op-level well_leveled preservation: prove `push_kt4_preserves_well_leveled`-style facts by case analysis mirroring the *_total proofs (non-repair arms: buffer changes only — need packet_levels of modified packet, easy from buf5 facts; repair arms: green_of_red_k_preserves_well_leveled, noting yellow_wrap_pr wraps result in KCons Yellow + the repair is applied to (KCons Red (PNode modified-buffer i suf) tail) so need colors_consistent of THAT red chain — the cc clauses for Red links are permissive ✓, only cc_yellow_run i + Hole=>tail_green_ready needed, inherited from input). THEN the colors_consistent half (green_of_red_k_preserves_colors_consistent — outputs green-headed; Case 3 fresh Red inner; needs tail_green_ready of outputs), then assemble the 4 *_preserves_colors_leveled admits.
- 2026-06-03 iter (rot + unpair-levels): proved `suffix_rot_preserves_levels`, `prefix_rot_preserves_levels`, `element_unpair_at_s_levels`. make_small foundation now COMPLETE (10 helpers). Build green, 4 admits. Next: assemble `make_small_preserves_levels` per the recipe above.
- 2026-06-03 iter (buffer-chain/unsandwich): proved `buffer_push_chain_levels`, `buffer_inject_chain_levels`, `buffer_unsandwich_levels` (Qed, build green, 4 admits). FINDING: `suffix_rot_unpair_total_under_levels`/`prefix_rot_unpair_total_under_levels` (PT:7279/7305) give only EXISTENCE of the unpair, NOT output levels — so make_small Overflow cases need NEW `*_preserves_levels` rot lemmas. They ARE derivable: the paired input is level `S k`, suffix_rot/prefix_rot keep level `S k`, and `E.unpair_level` gives the unpaired pair at level `k` (and `center` level `S k`). NEXT: prove `suffix_rot_preserves_levels`/`prefix_rot_preserves_levels` (output: cd_paired/ab_paired level `S k` so unpair gives level-k pair via E.unpair_level; center level `S k`), then assemble `make_small_preserves_levels` (9 cases, mirror `make_small_total_under_levels` PT:7331 structure), then `green_of_red_k_preserves_well_leveled`.
- 2026-06-03 iter (helper lemmas): proved 4 simple make_small helper level lemmas in DequeKeystone.v (Qed): `prefix23_levels`, `suffix23_levels`, `suffix12_levels`, `mk_ending_from_options_levels`. Build green, 4 admits. NEXT: buffer-op level lemmas (`buffer_unsandwich`, `buffer_push_chain`/`buffer_inject_chain` preserve levels; `buf5_*_naive` reuse OpsAbstract `buf5_*_preserves_levels`), then assemble `make_small_preserves_levels` (9 cases) reusing `pair_each_buf_after_halve_preserves_levels`/`suffix_rot`/`prefix_rot_unpair_total_under_levels`.
- 2026-06-03 iter (RBR + frontier map): closed RBR/Succ.v Abort (was a wrong-valued example on irregular input; replaced with correct `succ_rec_five_irregular` reflexivity). RBR now zero Abort/admit (mission item 2 DONE). Confirmed deque preservation reuse: `prefix_concat_preserves_outer_green_levels` (PublicTheorems 6503) and `suffix_concat_preserves_outer_green_levels` (6534) give green-shape + level-k/(S k) of concat outputs — directly usable for `green_of_red_k_preserves_well_leveled` Cases 2/3. GAP: Case 1 uses `make_small` (9 sub-cases) and has NO ready output-level lemma — need a new `make_small_preserves_levels` (assemble from buffer-op level facts like the concat ones; pattern as in `prefix_concat_preserves_outer_green_levels`'s proof: destruct all buffer shapes, use `E.unpair_level`/`E.level_pair`). So well_leveled half = {Case2/3 ready, Case1 needs make_small level lemma}; colours half still the harder wall. NEXT deque iteration: write `make_small_preserves_levels`, then `green_of_red_k_preserves_well_leveled`, then op-level well_leveled preservation, then colours.

- 2026-06-03 start: 5 admits in DequeKeystone.v. Totality reduced to `I_kt_implies_kt4_total_state`. Crux = recursive green-readiness.
- 2026-06-03 iter: refined `colors_consistent` with `cc_color_shape` + `tail_green_ready` (Hole-inner link => green/Ending tail). Proved 4 helper lemmas (Qed): `context_ready_of_consistent`, `ready_at_of_consistent`, `green_of_red_k_some_of_consistent`, `yellow_wrap_pr_total_pre_of_consistent`. Build green; still 5 admits (machinery, not yet wired to discharge).
- KEY FINDING: `kt4_total_state`'s B4 repair clauses are `forall x` (any level), but the existing totality lemmas need `E.level x = k`. `prefix_decompose (B5 x a b c d) = BD_pre_overflow (B3 x a b) c d` => the overflow pair is `(c,d)` (original B4, level k), x is kept; so `green_of_red_k` succeeds regardless of x. Public `push_kt4` is only ever called at the top with a level-0 element.
- DECISION: do NOT prove `I_kt_implies_kt4_total_state` (forall-x blocks it). Instead reprove the 4 `*_total` lemmas DIRECTLY using the helpers, adding `E.level A x = 0` to push/inject (faithful: public pushes level-0); pop/eject need no x. Then DELETE `I_kt_implies_kt4_total_state` and thread `E.level x = 0` through `deque_wc_o1_push`/`deque_wc_o1_inject`.

## STATUS 2026-06-03 (totality CLOSED)
- DequeKeystone.v builds green with **4 admits**: only `push/inject/pop/eject_kt4_preserves_I_kt`.
- All 4 `*_total` lemmas proven DIRECTLY (push/inject carry `E.level x = 0`; threaded through `deque_wc_o1_push`/`_inject`). `I_kt_implies_kt4_total_state` DELETED. `deque_wc_o1_*` each depend only on their `*_preserves_I_kt`.
- Helpers (Qed, reusable): `context_ready_of_consistent`, `ready_at_of_consistent` (free pre'/suf'), `green_of_red_k_some_of_consistent`, `yellow_wrap_pr_total_pre_of_consistent`.

## STATUS 2026-06-03 (4 admits — colour+level preservation only)
DequeKeystone.v green with exactly 4 admits: `push/inject/pop/eject_kt4_preserves_colors_leveled`
(`I_kt c -> op = result -> colors_consistent c' /\ well_leveled c'`). Everything else closed:
totality (direct), cost (`*_green_calls_le_1`), regular_kt_top preservation (reused), and the
`*_preserves_I_kt` wrappers (Qed). `deque_wc_o1_*` depend only on these 4.

### Reusable-lemma map for preservation (surveyed 2026-06-03)
- well_leveled half: `OpsAbstract.v` has `buf5_{push,inject,pop,eject}_preserves_levels` (211-243) and `{push,inject,pop,eject}_chain_preserves_levels` (253-336) — but those are for the abstract `Chain`, and there is NO ready `push_kt4 <-> push_chain` refinement via `kchain_to_chain` (only `kt4_packet_chain_view` relation + endpoint-only `push_chain_full (kchain_to_chain (KEnding b)) = ...`). So well_leveled must be proved DIRECTLY. The buffer-concat LEVEL lemmas to assemble `green_of_red_k_preserves_well_leveled` are in PublicTheorems.v: `prefix_concat_total_under_levels`/`suffix_concat_total_under_levels` (existence), `prefix_concat_preserves_outer_green_levels` (6503), `suffix_concat_preserves_outer_green_levels` (6534), `green_prefix_concat_preserves_green_outer_not_red_inner_levels` (7045), `green_prefix_concat_success_preserves_green_outer_levels` (7077), suffix duals (7109,7141), `..._from_not_red` (7173,7207), and `make_small_total_under_levels`. `green_of_red_k_case3_total_under_levels` (6479) shows the assembly pattern (uses prefix/suffix_concat_total_under_levels). Build `green_of_red_k_preserves_well_leveled` (3 cases) from these, then op-level via case analysis mirroring the `*_total` proofs (non-repair cases use `buf5_*_preserves_levels`).
- colours half: `green_of_red_k_top_green` (OpsKTRegular.v:288), `green_of_red_k_preserves_regular` (456), `kchain_top_color_chain_to_kchain_g_not_red` (PublicTheorems 10585), `make_small_chain_to_kchain_g_context_ready` (7452) — Case 1/2 outputs green-headed; Case 3 outputs `KCons Green (PNode .. Hole ..) (KCons Red ..)` (fresh red inner). Need bespoke `green_of_red_k_preserves_colors_consistent` showing the output satisfies `cc_color_shape`/`cc_yellow_run`/`tail_green_ready`. THIS is the prior wall.

### How to attack `*_preserves_colors_leveled` (the wall)
No pre-built level/colour preservation for the ops — bespoke. Plan:
1. **well_leveled** half first (more mechanical): prove `green_of_red_k c = Some c' -> well_leveled_at k c -> well_leveled_at k c'` and `yellow_wrap_pr pre i suf c = PushOk c' -> (levels of pre,suf,c at k) -> well_leveled_at k c'`. These need the buffer ops (`green_prefix_concat`/`make_small`/`prefix_concat`) to preserve `buf_all_at_level` — prove those small lemmas (they pair/unpair at adjacent levels; reuse `E.unpair_level`/`E.level_pair`). Then op-level well_leveled preservation by case analysis mirroring the `*_total` proofs.
2. **colors_consistent** half (harder): `green_of_red_k` Case 1/2 outputs are green-headed (`chain_to_kchain_g`, see `kchain_top_color_chain_to_kchain_g_not_red`, `make_small_chain_to_kchain_g_context_ready`); Case 3 outputs `KCons Green (PNode .. Hole ..) (KCons Red ..)` — must show the fresh Red inner is still colours-consistent and the new green head satisfies `tail_green_ready`/`cc_yellow_run`. yellow_wrap_pr turns green->yellow at same depth keeping the tail. Build `green_of_red_k_preserves_colors_consistent` then op-level.
   - WATCH: this is exactly where the prior accretion failed. If after several honest attempts colors_consistent isn't preserved, the `tail_green_ready` clause may be slightly wrong (too strong/weak) — adjust the ONE definition in place, re-check `*_total` still build (they only use it via helpers), and record findings here. Do NOT spawn candidate predicates.
3. If colours preservation stalls: ensure all green+committed, then switch to mission item 2 (RBR/Succ.v) so the night stays productive.

## REMAINING: preservation (the hard residue)
`*_preserves_I_kt : I_kt c -> op = result -> I_kt c'`. Split each into:
- regular_kt_top c': REUSE existing `push/inject/pop/eject_kt4_preserves_regular_top` (proven).
- colors_consistent c' /\ well_leveled c': NEW. This is the genuine work — must survive yellow_wrap_pr (green->yellow same depth, keeps tail) and green_of_red_k repair (Case 1/2 -> green head; Case 3 -> green head over fresh red inner; check tail_green_ready + cc_yellow_run + levels preserved). Look first for existing level-preservation lemmas (grep `chain_levels`/`packet_levels` preserved by green_of_red_k / yellow_wrap_pr / push_kt4). well_leveled may reuse them; colors_consistent is bespoke.

## NEXT STEPS (precise)
1. Reprove `push_kt4_total : forall A x c, I_kt c -> E.level A x = 0 -> exists c', push_kt4 x c = PushOk c'` directly:
   destruct c; KEnding => eexists/reflexivity; KCons _ Hole => `cbn in Hcc; contradiction`; Green => `destruct pre`, B2/B3 use `yellow_wrap_pr_total` + `yellow_wrap_pr_total_pre_of_consistent` (on tail at depth 1), others contradiction via green-shape; Yellow => B1/B2/B3 direct `eexists;reflexivity`, B4 use `yellow_push_red_repair_witness_from_ready` with `Hx`, `packet_levels` (proj1 of `well_leveled_at` of the link) and `ready_at_of_consistent`; Red top => `regular_kt_top` gives `top<>Red` contradiction. Use `cbn -[yellow_wrap_pr green_of_red_k]` when reducing the goal so those stay folded.
2. Symmetric `inject_kt4_total` (suffix side; `yellow_inject_red_repair_witness_from_ready`).
3. `pop_kt4_total` / `eject_kt4_total` directly (no x). pop on Yellow pre=B1 => `green_of_red_k (KCons Red (PNode B0 i suf) tail)` via `yellow_pop_red_repair_witness_from_ready` (no level hyp needed); B0 buffers => packet_levels trivially. Check pop_kt4 def (OpsKT.v:1539+) for exact shapes.
4. Delete `I_kt_implies_kt4_total_state`; update `deque_wc_o1_push`/`deque_wc_o1_inject` to take `E.level A x = 0` and pass it to `*_total`. Build green, commit. Admits then 4 (the `*_preserves_I_kt`).
5. Then attack `*_preserves_I_kt`: regular part via existing `*_preserves_regular_top`; colors_consistent + well_leveled preservation is the remaining hard work (the repair cases). This is the real residue.

## References
- Plan: `kb/runbooks/rebuild-plan-2026-06-02.md`
- Deque invariant spec: `kb/spec/deque-reachable-invariant.md`
- KT99 transcriptions: `kb/spec/section3-recursive-slowdown.md`, `section4-representation.md`, `section6-catenable-deques.md`
- Honest audit: `kb/reports/honest-audit-2026-06-02.md`
