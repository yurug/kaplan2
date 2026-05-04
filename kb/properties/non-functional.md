---
id: non-functional-properties
domain: properties
related: [functional-properties, edge-cases, api-contracts, adr-0012]
---

# Non-Functional Properties (NF-entries)

## One-liner
Bounded performance, memory, and tooling guarantees the implementation
must satisfy.

## Conventions
Same as `functional.md`: `NF<N>` IDs are stable; each entry has
Statement / Violation / Why / Test strategy.

## NF1 — Bounded read footprint per public operation

**Statement**: There exist constants `R_push, R_pop, R_inject, R_eject`
such that for any `H, r, args`, the number of distinct heap cells read
by `exec_op H r args` is ≤ the corresponding constant.
**Why**: §22 item 7 (manual §15.1).
**Cost bounds (`rocq/KTDeque/DequePtr/Footprint.v`):**
  - `NF_PUSH_PKT      = 3`  — naive push (1 read + 1 alloc + 1 freeze).
  - `NF_MAKE_RED_PKT  = 6`  — overflow rebalance.
  - `NF_PUSH_PKT_FULL = NF_PUSH_PKT + NF_MAKE_RED_PKT = 9` — push including overflow.
  - `NF_MAKE_GREEN_PKT = 6` — underflow refill.
  - `NF_POP_PKT_FULL   = NF_PUSH_PKT + NF_MAKE_GREEN_PKT = 9`.
  - Symmetric `NF_INJECT_PKT_FULL = NF_EJECT_PKT_FULL = 9`.
**Test strategy**: structural inversion in `Footprint.v`:
  - `exec_push_pkt_C_full_cost`, `packet_push_wc_O1`,
  - `exec_pop_pkt_full_C_cost`, `packet_pop_wc_O1`,
  - and the symmetric inject/eject lemmas.
  These prove the cost bound for the cost-monad (`MC`) routine; the C
  side runtime witness is `c/tests/wc_test.c` (allocation-count flat
  across n=1k/10k/100k).

## NF2 — Bounded allocation footprint per public operation

**Statement**: Analogous constants bound `|H' \ H|`. The same `NF_*_PKT_FULL`
constants from `Footprint.v` simultaneously bound reads, allocs, and freezes
(each primitive costs 1 in the `MC` monad).
**Why**: §22 item 7; needed for true persistent worst-case O(1) (per
ADR-0012, packet aggregation).
**Test strategy**: cost lemmas above + `wc_test.c` runtime witness.

## NF3 — No overwrite (allocation-only heap)

**Statement**: `dom H ⊆ dom H'` and for every `l ∈ dom H`, `H l = H' l`.
**Why**: gives persistence "for free" (manual §2.3).
**Test strategy**: each `exec_op_refines` lemma includes `heap_ext H H'`.

## NF4 — No `Admitted` / no `Axiom` in core modules

**Statement**: `make axioms` reports `Closed under the global context`
for the public summary. No `Admitted` in `rocq/KTDeque/`. Permissible
axioms: at most `FunctionalExtensionality` if a proof genuinely needs
it, isolated in `rocq/KTDeque/Common/Axioms.v` with a justification
comment.
**Why**: §22 item 8.
**Test strategy**: `make axioms` invocation in CI / Makefile target.

## NF5 — Symmetry duplication budget

**Statement**: No two non-trivial proof scripts in operation files have
similarity > 80%, except across left/right pairs explicitly delegated
to `rocq/KTDeque/Common/Symmetry.v`.
**Why**: manual §18 — "do not prove left and right cases twice."
**Test strategy**: code review at audit time.

## NF6 — Build time bound

**Statement**: `dune build` (cold cache) completes in ≤ 60 minutes on
a workstation-class machine.
**Why**: developer ergonomics; VWGP §8.2 reports their model functions
take ~30 minutes to type-check.
**Test strategy**: timed `make` in audit reports. Not a release blocker,
but a regression flag.

## NF7 — Comment density

**Statement**: `rocq/KTDeque/Common/`, `rocq/KTDeque/DequePtr/` each
have ≥ 40% non-blank-line ratio of comment lines.
**Why**: literate programming for proof artifact + onboarding.
**Test strategy**: simple `awk` script in `runbooks/audit-checklist.md`.

## NF8 — Function and file size bounds

**Statement**: Every function ≤ 30 lines (proof obligations and big
mutual-recursion blocks excepted); every file ≤ 200 lines (mutual
blocks excepted).
**Why**: navigability; methodology default.
**Test strategy**: `wc -l` audit; reviewer judgment on exceptions.

## NF9 — Constants centralized

**Statement**: Every numeric literal used in size or color reasoning
is a `Definition` in `rocq/KTDeque/Common/Params.v`. No bare
`5`/`6`/`7`/`8` in algorithm modules.
**Why**: §22 item 10. Manual §19.
**Test strategy**: `grep -E '\b(5|6|7|8)\b'` scan should be near-empty.

## NF10 — OCaml extraction succeeds

**Statement**: `dune build` produces extracted OCaml in
`ocaml/extracted/` with no warnings of severity ≥ `error`.
**Why**: enables Monolith fuzzing and demo runtime.
**Test strategy**: build target.

## NF11 — Monolith fuzzing passes 60 s

**Statement**: the fuzz binary runs for ≥ 60 s without printing a
discrepancy against the list reference.
**Why**: §32 user override / VWGP §9.1 do this. Provides runtime
sanity beyond proofs.
**Test strategy**: see `external/monolith-fuzzing.md`.

## NF12 — Single deviation invariant

**Statement**: The structural deviations from KT99/VWGP described in
the manual are (a) the explicit retention of natural child pointers
plus shortcut caches, and (b) packet aggregation per ADR-0012. No
other simplification is committed without escalation.
**Why**: §22 item 9.
**Test strategy**: architecture audit; reviewer sign-off.

The live tree (`rocq/KTDeque/DequePtr/`) uses packet aggregation
(`Packet`/`Chain` GADT-style inductive). Three further C-side
deviations beyond what Rocq covers — nested PNodes (depth ≥ 2;
ADR-0012), DIFF link encoding (ADR-0013), and K=2 pair-tree flattening
(ADR-0014) — are tracked in their own ADRs. None of these is proven
against the abstract spec; the cost bounds NF_*_PKT_FULL = 9 above
bound the Rocq heap monad, not the C-level allocation count directly
(though the C `wc_test` runtime witness matches at n=100k).

## Agent notes
> If a build target slows past 60 minutes (NF6) without an explanatory
> commit, that is a regression and must be flagged.
> For NF1/NF2: the bounds need not be tight; "≤ 100" is fine if the
> math doesn't support a smaller constant. The point is that they are
> *constants*, independent of input size.

## Related files
- `functional.md` — what must be true (semantics).
- `edge-cases.md` — exotic inputs to test bounds against.
- `../runbooks/audit-checklist.md` — how to run these checks.
