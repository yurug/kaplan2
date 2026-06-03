# SESSION_STATE — autonomous loop (started 2026-06-03)

Running unattended (user asleep) to progress the rebuild plan. Read this first.

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

## Progress log (newest first)
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
