---
id: rebuild-plan-2026-06-02
domain: meta
status: proposed
last-updated: 2026-06-02
---

# Rebuild plan — 2026-06-02

**Status: decisions resolved 2026-06-02 (see below). Work happens on the
`rebuild` branch.** Phases 0–1 (preserve + honest baseline) done. **Phase 3
(paper specs) DONE and the keystone targets decided** (deque = abstract bound,
no jump4; catenable = faithful §6/Viennot GYOR). Phase 2 (re-curate, destructive)
and Phase 4 (prove) still await explicit go-ahead.

## Why we are doing this

Two agents (Claude, Codex) grew the proof by accretion: candidate invariants
were *discovered* in Rocq by trial and error rather than *designed* on paper
first, and the KB recorded the search instead of the answer. The result
(diagnosed in [`../reports/honest-audit-2026-06-02.md`](../reports/honest-audit-2026-06-02.md)):

- Sound, axiom-clean proofs (1,828 theorems, all closed under the global
  context) — **these are assets**.
- But the two keystone claims are conditional/restricted, and the labels hide
  it. The release gate scores the *frontier* (`*_gap` lemmas), not a closed
  top-level theorem.
- Five catenable variants (`Cadeque6/7/8/9`) + `DequePtr` + `RBR`, none retired;
  ~31 benches; two parallel audit bundles. The canonical choice is invisible.

The strategy (chosen 2026-06-02): **re-curate, keep the proofs** — not a
from-scratch rewrite. Catenable canonical variant to be decided **on paper
first**. Re-audit done.

## Methodology fixes (the "do better" the rebuild encodes)

1. **Invariant-first.** The regularity/totality/representation invariant is part
   of the *spec*. Write it on paper (citing KT99 §4 for the deque, §6 for the
   catenable deque) and state the **unconditional top-level theorem** before
   proving. No new invariant candidate gets a Rocq file until its English
   statement and the cascade-bounding argument are in `kb/spec/`.
2. **One canonical variant per structure.** `DequePtr` for the deque; catenable
   chosen at Phase 3b. Everything else lives on `archive/` only.
3. **Honest labels.** A gate is "closed" **only** when its *unconditional*
   top-level theorem is closed and `Print Assumptions`-clean. Conditional
   theorems are labeled `CONDITIONAL on <premise> — premise OPEN`. The gate
   script checks the top-level theorem, never the mere existence of frontier or
   `_gap` lemmas.
4. **Living status, not a history log.** One screen of gate status. Failed
   invariant candidates go to a `lessons.md` appendix with *why* they failed —
   not into the main status doc.
5. **Promotion gate (per layer).** A layer is promoted to rebuilt `main` only
   with: (a) written spec/invariant; (b) admit-free proof; (c) clean
   `Print Assumptions`; (d) the unconditional theorem stated, even if marked
   OPEN with the precise remaining obligation.

## Phases

### Phase 0 — Preserve (DONE, non-destructive)
- WIP-commit the full drifted tree → `f1d701f`.
- `archive/pre-rebuild-2026-06-02` branch + `archive-pre-rebuild-2026-06-02`
  tag pin the complete state (all variants + in-progress Gate D).
- **DONE:** archive branch + tag pushed to `origin` (2026-06-02). `main` and the
  `rebuild` branch remain local (not pushed) pending the rebuild's completion.

### Phase 1 — Honest baseline on `main` (IN PROGRESS, non-destructive)
- Land `reports/honest-audit-2026-06-02.md` (done).
- Supersede `runbooks/minimum-release-gate.md` with a banner (done).
- Reduce `tools/check_wc_o1_release_gate.sh` to assert the *top-level*
  unconditional theorems only; move the `*_gap`/frontier greps into a separate
  `frontier-status` report so a green gate means "summit," not "progress."
- Update `kb/INDEX.md` quick-load bundles to point at the honest audit.

### Phase 2 — Re-curate the tree (FIRST DESTRUCTIVE STEP — needs approval)
Keep on rebuilt `main`:
- `rocq/KTDeque/Common`, `rocq/KTDeque/DequePtr`, the chosen catenable variant,
  `rocq/KTDeque/Extract` trimmed to `kTDeque` + the chosen catenable extraction.
- `c/` (the empirical port), the qcheck suite, and a *minimal* bench set.

Keep also: `RBR` (decision #2 — finish `Succ.v`, do not drop).

Remove from `main` (retained on `archive/`):
- The non-canonical catenable variants (`Cadeque6`, `Cadeque7`, `Cadeque8`, and
  `Cadeque9` if Phase 3b rejects it), `Public` if unused.
- The dead extractions (`kCadeque8*`, `kCadeque`, `kTCatenableDeque`) and the
  ~20 variant-specific benches (`k8_*`, `kc8_*`, …).

Sequencing note: this is reversible (everything is on `archive/`), but it is the
point of no easy return for casual readers, so it waits for explicit sign-off
and for the Phase-3b catenable decision.

### Phase 3 — Paper specs for the two keystones (the methodology fix)

**Sources (confirmed present in-repo, 2026-06-02):** `jacm-final.pdf` (KT99,
27pp — authoritative §1–§7); `viennot-wendling-gueneau-pottier-verified-catenable-deques.pdf`
(Viennot et al. 2025, 65pp); vendored Viennot Coq dev `external-refs/VerifiedCatenableDeque/`
and OCaml reference `ocaml/bench/viennot/`. Decision (2026-06-02): **follow KT99
closely; mine Viennot for insight only** (no port of intrinsic types / `Equations`
proofs, per ADR-0004).

**Pre-draft reading not yet done** (the orientation pass flagged these as the
gaps): KT99 **§6** (catenable) and **§7** (cascade / jump-pointer depth bound)
are *not* transcribed in the KB (only §4.2 is, in `spec/section4-repair-cases.md`),
and the team's manual §7.5 is source-corrupted — re-extract from the PDF. The
production deque invariant is `regular_kt` in `DequePtr/OpsKTRegular.v` (not
`Regularity.v`'s older colour-less `regular_chain`). The catenable concat-cost
bridge lives in `Cadeque9/Normalize.v` + `spec/cadeque9-paper-faithful-plan.md`.

- **3a — Deque reachable-state invariant (Gate B).** Transcribe KT99 §7 to
  `kb/spec/`, read `OpsKTRegular.v`'s `regular_kt`, then define invariant `I`
  such that `empty ⊨ I`, every public op preserves `I`, and `I ⇒
  kt4_all_role_heap_packet_view_repr`. Note the gap precisely: regularity is the
  *size budget* (top ≤ 4, spine ≤ 3) and is currently only proved
  `regular_chain → regular_top_chain` (one step, weakened); the all-role
  invariant is an *orthogonal* heap-realizability + colour-aware + per-op
  executability layer. `I` must carry both. State the unconditional theorem
  `∀ s, reachable s → cost(op s) ≤ K ∧ op s ≠ Fail`.
- **3b — Catenable–catenable concat (Gate D).** Transcribe KT99 §6 (the
  GYOR colour scheme; cf. Viennot `Color/GYOR.v`) to `kb/spec/`, then state the
  representation/invariant under which `concat(catenable, catenable)` is
  genuinely O(1). Key reconciliation to make explicit: `kcad9_concat` already has
  the correct *constant-linking shape*, but the abstract model uses `Buf6 = list`
  so concat is `++` (O(length)) in the model; real O(1) is deferred to
  `Normalize.v`'s constant-fuel-over-reachable-states bridge. The paper-spec must
  state the single reachable-state invariant that makes the linked spines O(1) to
  join in the real representation. **This may reveal the current Cadeque9
  representation needs change** — treat that as the real research result, not a
  failure to paper over. (Canonical catenable variant is decided by this step.)

### Phase 4 — Promote proofs against the specs
Per keystone, in dependency order, either:
- (a) reuse the existing conditional theorem + add the *new* reachability /
  preservation proof that discharges its premise; or
- (b) restate and reprove against the paper invariant.
Promote `Common → DequePtr → deque public theorems → extraction → catenable →
catenable public theorems → extraction`, each through the Phase-1 promotion gate.

### Phase 5 — Re-extract, re-bench, honest docs
- One extraction per structure; trimmed reproducible bench set.
- README / package claims matched to *closed* theorems only; the adversarial
  persistent-fork bench retained as the operational WC O(1) evidence.

## Decisions (resolved 2026-06-02)

1. **Catenable canonical variant** — *follow KT99 §6 closely, mine Viennot for
   insight.* Resolved by decision #6: adopt the §6/Viennot GYOR structure;
   Cadeque9 is not canonical.
2. **RBR** — *finish* `Succ.v` (close the `Abort.`); RBR stays in the rebuilt
   tree. Queued as a Phase-4 proof task.
3. **Branch topology** — *work on the `rebuild` branch*, promote to `main` at
   the end. (`rebuild` created 2026-06-02 off the honest baseline `8b10737`.)
4. **Backup** — *archive pushed* to `origin` (branch + tag). `main`/`rebuild`
   stay local until the rebuild lands.
5. **Deque keystone target** — *abstract chain bound, no `jump4`* (cost = cell
   touches in the model; bounded repair offset from packet bundling). Sidesteps
   the heap-realizability bridge. Remaining work = abstract totality +
   preservation of `I` = `regular_kt` + size/color consistency. See
   [`../spec/deque-reachable-invariant.md`](../spec/deque-reachable-invariant.md).
6. **Catenable keystone target** — *adopt the faithful KT99 §6 / Viennot GYOR
   structure now* (triples + preferred paths + compressed forest). Build the
   catenable tree fresh from `J`; Cadeque9 → archive only. Sequenced after the
   deque keystone. See
   [`../spec/catenable-concat-invariant.md`](../spec/catenable-concat-invariant.md).

## Risks

- Phase 3 is genuine research, not transcription. The deque invariant (3a) is
  the same wall the accretion hit; designing it on paper is the bet that a
  clean statement is reachable where blind search was not. If 3a stalls, the
  honest fallback is to ship `DequePtr` with sequence + regularity + packet-cost
  closed and the reachable-state O(1) explicitly OPEN — which is already more
  honest than today's labels.
- 3b may force a representation change to the catenable structure, i.e. real
  redesign work, not promotion of existing proofs.
