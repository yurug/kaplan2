---
id: honest-audit-2026-06-02
domain: verification
status: active
supersedes: wc-o1-verification-audit-2026-05-24, minimum-release-gate, gate-d-top-down-plan
last-updated: 2026-06-02
---

# Honest WC O(1) audit — 2026-06-02

This report is the authoritative status of the worst-case-O(1) claims. It was
produced by reading the actual theorem **statements** and the literal
`Print Assumptions` output, not the prose labels in the historical runbooks. It
supersedes the "closed/partial" language in
[`runbooks/minimum-release-gate.md`](../runbooks/minimum-release-gate.md) and
[`runbooks/gate-d-top-down-plan.md`](../runbooks/gate-d-top-down-plan.md).

## Method

- `dune clean` then a full rebuild of the two audit bundles
  (`DequePtr/PublicTheoremsAudit.vo`, `Cadeque9/PublicTheoremsAudit.vo`) with
  `--no-buffer`, capturing every `Print Assumptions`.
- Read the literal Coq statements of the two headline cost theorems and their
  premises.
- Resolved the Gate-D cost model (`primitive_costed_step`, `step_limit`,
  `cost_certificate`, `reachable_operands_inv`) down to whether the bound or the
  fuel/source-bound parameters scale with `n`.

## Result 1 — the proofs are sound and axiom-clean

**1,828 `Print Assumptions` statements, every one "Closed under the global
context."** Zero `Axioms:` sections; no `TODO_gate_d`, `admit`, `Admitted`, or
recursive `*_full` proof-artifact in any dependency base. The only non-clean
artifact in the whole tree is a single stray `Abort.` in
`rocq/KTDeque/RBR/Succ.v:90`, which is on no release path.

This is not a project with fake results. The Rocq is honest at the kernel level,
and the sound lemmas are assets to preserve.

## Result 2 — the load-bearing subtlety: clean ≠ unconditional

`Print Assumptions` reporting "Closed under the global context" means **no
axioms**. It says nothing about whether a theorem's *premises* are ever
dischargeable. A theorem `∀x, P x → Q x` is "clean" even if `P x` holds for no
reachable state. **Both keystone cost theorems have exactly this shape**, and
that is how the release gate stays green while the real claim stays open. The
release script
([`tools/check_wc_o1_release_gate.sh`](../../tools/check_wc_o1_release_gate.sh))
compounds this: it checks that dozens of intermediate `*_gap` and
`*_frontier_obligations` lemmas *exist* and print clean — i.e. it audits the
search frontier, not a closed top-level theorem.

## Result 3 — Gate B (non-catenable deque `kt4`): closed except the keystone

| Property | Status |
| --- | --- |
| Sequence correctness (`*_kt4_seq_thm`) | **Closed, clean** |
| Regularity preservation (`*_kt4_preserves_regular_top`) | **Closed, clean** |
| Packet-level constant cost (`packet_*_full_correct_O1_repr_thm`, budgets ≤ `NF_PUSH_PKT_FULL`) | **Closed, clean** |
| Per-operation WC O(1) on reachable states | **OPEN** |

The per-operation cost contract
`kt4_all_role_heap_packet_view_exec_cost_refinement_contract`
(`rocq/KTDeque/DequePtr/PublicTheorems.v:2699`) is **conditional on the premise
`kt4_all_role_heap_packet_view_repr H lroot c`** (`:2702`). No theorem proves
that invariant holds at `empty` and is preserved by all four public operations
on reachable states. That establishment **is** the open frontier: the entire
`*_not_push_closed` / `*_gap` / `*_frontier_obligations` pile is the
still-unsuccessful search for the invariant. It is genuine incompleteness, not
unsoundness.

**Honest statement:** "given the all-role invariant, each op is O(1)" ✓;
"all reachable deques satisfy that invariant" ✗.

## Result 4 — Gate D (catenable Cadeque9): genuine constant, restricted operation

The headline theorem
`kcad9_gate_d_public_shipped_full_split_operation_cost_refinement_contract_thm`
(`rocq/KTDeque/Cadeque9/GateDPublicTheorems.v:744`) proves a per-operation
charge bound that is a **genuine size- and history-independent constant**:
`concat_fuel·3 + endpoint_fuel + 5 + 2·source_bound`. Decisively, the size-side
obligation is discharged for an *arbitrary* `source_bound`
(`GateDProofPlan.v:10207`; the `StoredBig9`/`StoredMiddle9` cases close by
`contradiction`), so the bound carries **no hidden dependence on `n`**. The
proof is admit-free.

**The catch:** the premise `kcad9_gate_d_fast_public_script_reachable_operands_inv`
requires every `concat`'s right operand to be
`kcad9_gate_d_fast_public_push_inject_only`-reachable from empty
(`GateDProofPlan.v:7611`) — a *plain* deque built by push/inject only, never
itself a concat result, never popped. So Gate D proves O(1) for **appending a
simple deque**, not for **concatenating two already-catenated deques** — the
defining hard case of a *catenable* deque. The runbook's own
`..._append_right_operand_..._not_closed_thm` and "not prefix-closed" results
are the evidence that the general operand case is open.

**Honest statement:** WC O(1) for `concat(catenable, simple)` ✓;
for `concat(catenable, catenable)` ✗.

## Results 5 — Gates A / C / E

- **A (honest docs):** real, appropriately scoped.
- **C (static no-linear-path guard):** real, appropriately scoped.
- **E (C / ports):** correctly labeled as an *empirical* differential-fuzzing
  gate, not a Rocq-refined C proof.

## Bottom line

The drift is not bad proofs — it is a widening gap between the formal statements
and the prose labels, filled by ~1,800 lemmas (many of them `_gap` markers and
failed invariant candidates). The two things a reader assumes are done are
exactly the two things **not** closed:

1. the deque's **reachable-state O(1) invariant** (Gate B keystone), and
2. **catenable–catenable concat in O(1)** (Gate D keystone).

Everything around them is sound and clean. The rebuild's job is to state those
two keystone theorems *unconditionally and up front*, mark them OPEN until
discharged, and stop letting the gate score the frontier as if it were the
summit. See [`runbooks/rebuild-plan-2026-06-02.md`](../runbooks/rebuild-plan-2026-06-02.md).
