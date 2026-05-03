---
id: escape-hatches
domain: runbooks
related: [audit-checklist, non-functional-properties]
---

# Escape Hatches — Allowed Simplifications and Forbidden Shortcuts

## One-liner
Consolidated reference for manual §20 (allowed simplifications) and
§21 (forbidden shortcuts). **Stop and ask the user before applying any
simplification.**

## Scope
Covers: when (if ever) we may deviate from the manual; what is never
permitted; how to escalate. Does NOT cover: routine tactical decisions
(see `conventions/proof-style.md`).

## Manual §20 — Allowed simplifications, ladder from best to worst

The manual lists five simplifications, **ordered from preferred to
last-resort**. A higher-numbered simplification implies the
lower-numbered ones have already been applied or examined.

| Rung | Simplification                                                                                                              | Status                |
|------|------------------------------------------------------------------------------------------------------------------------------|-----------------------|
| 20.1 | Keep natural child pointers AND keep shortcuts (`jump` / `adopt`).                                                            | **Adopted** (ADR-0003). Not a "simplification" for us; it's the design. |
| 20.2 | Postpone Section-5 steque entirely.                                                                                           | **Adopted** (PRD).        |
| 20.3 | Postpone explicit cost layer; keep only footprint.                                                                            | **Adopted** (PRD).        |
| 20.4 | Keep all buffer sizes cached explicitly.                                                                                      | **Adopted**. |
| 20.5 | Replace the shortcut pointer with a cached direct pointer to the current repair site at the root only, but document the deviation clearly. | **Reserve as last resort.** Requires user sign-off + an ADR. Triggers NF12 violation if not documented. |

### How to apply 20.5 (if ever)

1. Stop. **Ask the user** before any code change.
2. Capture the blocker that forces this rung (situation, what was tried, what's needed).
3. Wait for user sign-off.
4. Open a new ADR amending ADR-0003 (or invalidating it).
5. Update NF12 status.
6. Implement.

## Manual §21 — Forbidden shortcuts

The following are **never** permitted in the core correctness layer
(`rocq/KTDeque/Common/`, `rocq/KTDeque/RBR/`, `rocq/KTDeque/DequePtr/`):

1. **Axiomatizing sequence semantics** — `chain_to_list`, `packet_seq` must be Rocq `Fixpoint`s, not `Axiom`s.
2. **Axiomatizing regularity preservation** — every regularity-preservation lemma is *proved*, not assumed.
3. **`Admitted` in core files** — caught by `make axioms` (NF4).
4. **Replacing the buffer implementation with plain lists** — `Buf5` is the canonical buffer.
5. **Dropping persistence from the heap model** — heap is allocation-only (NF3). No `update`/`overwrite` operations.
6. **Proving only logical operations and skipping the heap refinement** — every public op needs a `*_refines` theorem (manual §14.2).

`Admitted` is tolerated **only** in `Cost/` (out of scope) and only if isolated and clearly marked.

## Cross-references between §20 and §21

§20 simplifications operate on the *what* of the data structure; §21
forbids shortcuts on the *how* of the proof discipline. They are
complementary, not contradictory: e.g., 20.5 (cached direct pointer)
does not violate §21 because the natural tree is still present and
sequence semantics is still proved as a `Fixpoint`.

## Escalation procedure

When you hit a blocker:

1. Try the rungs of `kb/conventions/proof-style.md` "preferred tactics" first.
2. If that fails after a few iterations, document the blocker (situation, what was tried, what's needed).
3. Pause. **Do not silently apply §20 simplifications.**
4. Ask the user.
5. Once unblocked, document the resolution.

## Agent notes
> The `§20.1` "keep natural child pointers AND shortcuts" is the manual's #1 recommendation; we adopted it. Don't propose "drop shortcuts" as a simplification — that goes the wrong direction.
> Every `Admitted` deserves a comment; if you see one without escalation logged, that's a HIGH audit finding.

## Related files
- `audit-checklist.md` — items 2 and 4 enforce most of §21.
- `../properties/non-functional.md` — NF4 and NF12.
- `../architecture/decisions/adr-0003-deviation-shortcuts.md` — the allowed deviation.
