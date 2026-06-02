---
id: rebuild-plan-2026-06-02
domain: meta
status: proposed
last-updated: 2026-06-02
---

# Rebuild plan — 2026-06-02

**Status: PROPOSED — awaiting approval before Phase 2 (the first destructive
step).** Phases 0–1 (preserve + honest baseline) are non-destructive and are
being landed now.

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
- **Open decision:** push the archive branch/tag to `origin`? (Currently local
  only; `main` is 254 commits ahead of `origin/main`.)

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

Remove from `main` (retained on `archive/`):
- The non-canonical catenable variants (`Cadeque6`, `Cadeque7`, `Cadeque8`, and
  `Cadeque9` if Phase 3b rejects it), `RBR` (unless Phase-3 work needs it),
  `Public` if unused.
- The dead extractions (`kCadeque8*`, `kCadeque`, `kTCatenableDeque`) and the
  ~20 variant-specific benches (`k8_*`, `kc8_*`, …).

Sequencing note: this is reversible (everything is on `archive/`), but it is the
point of no easy return for casual readers, so it waits for explicit sign-off
and for the Phase-3b catenable decision.

### Phase 3 — Paper specs for the two keystones (the methodology fix)
- **3a — Deque reachable-state invariant (Gate B).** Define invariant `I` such
  that `empty ⊨ I`, every public op preserves `I`, and `I ⇒
  kt4_all_role_heap_packet_view_repr`. This is the KT99 §7 alternating
  green/yellow + jump-pointer (`D4Cell.jump4`) argument made precise. Write it in
  `kb/spec/` with the unconditional theorem statement
  `∀ s, reachable s → cost(op s) ≤ K ∧ op s ≠ Fail`.
- **3b — Catenable–catenable concat (Gate D).** Decide the canonical catenable
  variant by writing, from KT99 §6, the representation/invariant under which
  `concat(catenable, catenable)` is genuinely O(1) (constant linking, no operand
  traversal). State the unconditional theorem. **This may reveal that the
  current Cadeque9 representation cannot support it without change** — the plan
  must allow that discovery and treat it as the real research result, not a
  failure to paper over.

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

## Open decisions for you

1. **Catenable canonical variant** — resolved by Phase 3b on paper (likely
   `Cadeque9`, but only if §6 says its representation supports
   catenable–catenable O(1)).
2. **RBR** — finish `Succ.v` (close the `Abort.`) or drop it to `archive/`?
3. **Branch topology** — rebuild on `main` directly (current plan), or on a
   `rebuild/` branch promoted to `main` at the end?
4. **Push** — push `archive/pre-rebuild-2026-06-02` to `origin` now for
   off-machine backup?

## Risks

- Phase 3 is genuine research, not transcription. The deque invariant (3a) is
  the same wall the accretion hit; designing it on paper is the bet that a
  clean statement is reachable where blind search was not. If 3a stalls, the
  honest fallback is to ship `DequePtr` with sequence + regularity + packet-cost
  closed and the reachable-state O(1) explicitly OPEN — which is already more
  honest than today's labels.
- 3b may force a representation change to the catenable structure, i.e. real
  redesign work, not promotion of existing proofs.
