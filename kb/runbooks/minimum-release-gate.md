---
id: minimum-release-gate
domain: verification
status: active
last-updated: 2026-05-24
---

# Minimum Release Gate

This runbook turns the WC O(1) audit into a concrete release plan. It is stricter
than "tests pass": a release candidate must have a mechanically inspectable path
from public API, to invariant, to functional theorem, to constant-cost theorem,
to extracted or ported code.

The current target is a minimum release that ships the non-catenable deque as the
production API and labels every catenable module as experimental/reference until
the catenable gate is closed.

## Gate A - repository claims are honest

Status: closed for current docs on 2026-05-24.

Requirements:

- The README, OCaml README, dune comments, and package docs must not recommend
  `KCadeque8`, `KCadeque9`, or any catenable module as strict WC O(1).
- The KB must have a current status page that supersedes stale historical
  reports.
- The public package description may claim WC O(1) only for the non-catenable
  `KTDeque` surface.

Implementation tasks:

- Update stale docs that advertise `KCadeque8`.
- Add this release-gate runbook to the KB index.
- Keep `kb/reports/wc-o1-verification-audit-2026-05-24.md` as the current audit
  record.
- Add a docs scan to `tools/check_wc_o1_release_gate.sh`.

Exit check:

```sh
rg -n 'KCadeque8.*recommended|Recommended catenable API|bench-validated strict WC O\(1\)|shipped as Cadeque8|use the `KCadeque8` module|verified strict WC O\(1\) catenable' README.md ocaml/README.md ocaml/extracted/dune kb/INDEX.md
```

Any remaining hit must be historical context with an explicit "not current" or
"known blocker" marker.

## Gate B - non-catenable production proof spine

Status: not closed.

Required theorem package for the exact public family:

- totality under the public regular invariant;
- sequence correctness;
- regularity preservation;
- constant cost independent of length/history;
- a short extraction mapping explaining why the OCaml functions are the ones
  covered by those theorem names.

Implementation tasks:

- Add a `KTDeque/DequePtr/PublicTheorems.v` or equivalent summary module that
  imports the needed lemmas and exposes one named theorem bundle per operation.
- Add a `Print Assumptions`/assumption-audit command for the bundle.
- Update the OCaml README to point to the bundle, not scattered proof files.

Exit checks:

```sh
dune build rocq/KTDeque
dune runtest
make -C c check
```

Then run the assumption audit described by the bundle. The expected output for
public theorems is no project-local admits and no unaccounted axioms beyond
module signatures that are intentionally abstract.

## Gate C - static no-linear-path guard

Status: implemented, currently failing on real blockers.

The release gate must mechanically reject production code paths that call
semantic/list helpers from latency-critical operations.

Blocked patterns for strict production modules:

- `to_list` followed by rebuild;
- `from_list` in pop/eject/concat paths;
- `buf6_elems`, `List.length`, `List.rev`, unbounded `app`, or folds in public
  operations;
- recovery branches that copy by depth unless proved unreachable and disabled in
  release builds;
- `Obj.magic` public fast paths without theorem coverage over the same
  invariant.

Implementation tasks:

- Add a script target that fails while known catenable blockers remain.
- Keep the target out of `dune build` so normal development is not blocked, but
  make it the command a release manager runs before tagging.

Implemented command:

```sh
make wc-o1-gate
```

As of 2026-05-24 it fails on five blocker groups:

- unbounded `KCadeque9.buf6_concat`;
- `KCadeque8` list fallback rebuilds;
- catenable shim `Coq_E.to_list` flattening;
- unverified inline catenable paths;
- C asserted-unreachable branches remain outside the Rocq proof boundary.

The operation-level Cadeque9 concat timing harness exists as:

```sh
dune exec --profile=release ocaml/bench/k9_concat_cost.exe
```

Exit check:

```sh
make release-gate
```

This command is expected to fail until the catenable blockers are removed or the
release profile explicitly excludes catenation from its claim.

## Gate D - catenable implementation redesign

Status: blocked by design work.

Current blockers:

- `KCadeque8` has a known `(T+T) eject` path that falls back through
  `kcad8_to_list` / `kcad8_from_list`.
- `KCadeque9` now has a cached-length OCaml shim for `buf6_size`, but the
  proof/refinement story is not closed and `buf6_concat` is still linear.
- `KCadequeShim` can flatten surfaced element trees through `Coq_E.to_list`.
- `KCadeque9Inline` can return states outside the proved strong invariant.

Implementation tasks:

- Implement an operational `Buf6` with cached length, or a proven equivalent.
- Redesign Cadeque9 concat so `(T+T)` stores the right middle spine in a
  constant-shape cell instead of concatenating middle buffers.
- Remove public fallback rebuilds.
- Prove boundary element invariants and totality.
- Either prove bounded surfaced elements in the shim or remove one-operation
  flattening.

Exit checks:

- The static guard passes for catenable production modules.
- Operation-level adversarial benches time `concat` itself and stay flat.
- Public catenable theorem bundles match the Gate B shape.

## Gate E - C and other ports

Status: not closed.

Requirements:

- C is either documented as an empirical port or refined to the Rocq model.
- The asserted-unreachable C fallback branches are proved unreachable or removed
  from release builds.
- Rust and handwritten OCaml prototypes remain explicitly non-production until
  their internals are replaced and proved.

Exit checks:

```sh
make -C c check
make -C c check-all
```

These tests are evidence. They do not replace the proof/refinement requirement.

## Overnight implementation order

1. Close Gate A as far as documentation can.
2. Add the static release-gate target for Gate C.
3. Re-run `dune build`, `dune runtest`, and `make -C c check`.
4. Record any remaining blockers explicitly rather than weakening the gate.

The catenable redesign is intentionally not treated as a quick patch. The
previous regressions came from accepting local fixes without a complete
invariant/cost story; this gate is designed to prevent repeating that pattern.
