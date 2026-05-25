---
id: wc-o1-verification-audit-2026-05-24
domain: verification
status: blocking-findings
last-updated: 2026-05-24
---

# Worst-case O(1) verification audit - 2026-05-24

## Scope

This audit reviews the current repository state against the strict bar the
project is aiming for:

1. Every public deque operation has the intended functional semantics.
2. Every latency-critical public operation is worst-case O(1), not amortized
   O(1), not expected O(1), and not O(1) only under an unproved reachability
   assumption.
3. The claim is clear enough that a reviewer can follow the definitions,
   invariants, cost model, extraction boundary, tests, and ports without
   relying on folklore or stale comments.

The review covers the Rocq models/proofs, extracted OCaml, C port, Rust port,
bench harnesses, and KB/README claims.

## Executive conclusion

The codebase is not currently in a state where all exposed data structures can
be claimed both functionally correct and worst-case O(1).

The strongest negative findings are not proof gaps. They are direct code paths:

- At audit start, `KCadeque9` used `buf6_size` in `pop`/`eject`, and the
  extracted implementation computed it as `List.length (buf6_elems b)`. This
  direct OCaml hot path was replaced on 2026-05-24 by a cached logical length in
  `KCadequeShim`; the remaining release blocker is to connect that hand-written
  extraction support to a proof/refinement story.
- `KCadeque9` uses `buf6_concat` in `concat` and refill paths, and extracted
  `buf6_concat` materializes both buffers as lists and rebuilds a buffer. This
  is linear.
- `KCadeque8` still has a known `(T+T) eject` path where the structural path
  fails and the public operation falls back through `kcad8_to_list` /
  `kcad8_from_list`. This is linear.
- Several public documents still advertise `KCadeque8` as strict WC O(1), even
  though the KB already records an open worst-case bug.

The non-catenable `KTDeque` layer is much closer to the desired bar. It has
conditional sequence theorems for `kt4`, regularity preservation documented for
`kt2`, and constant-shape operation code. It still needs a tighter public
certificate that the exact extracted/public family being shipped has totality,
regularity preservation, and a connected cost theorem.

## Current classification

| Component | Functional status | WC O(1) status | Ship status |
| --- | --- | --- | --- |
| `KTDeque` / `KChain` non-catenable OCaml extraction | Sequence theorems exist for `kt4` operations conditional on success. Regularity file documents closed preservation for `kt2`. | Plausible and partially mechanized, but public `kt4` totality/preservation/cost linkage needs consolidation. | Candidate core, not enough clarity yet for a blanket claim. |
| C non-catenable port | Tests and differential/region checks pass locally. | Operation shape is constant in the main path. Two asserted-unreachable branches now fail fast instead of running the old `O(depth)` recovery, but they remain outside the Rocq proof boundary. | High-quality port, but empirical/refinement gap remains. |
| `KTCatenableDeque` / Cadeque6 | Reference/spec layer. | Contains spec-level normalization/list paths. Not WC O(1). | Reference only. |
| `KCadeque` / Cadeque7 | Legacy catenable layer. | Known O(n) fallbacks. | Do not recommend for strict latency. |
| `KCadeque8` | Sequence and invariant preservation evidence exists, but public fast paths can fall back. | Not WC O(1): known `(T+T) eject` linear fallback remains. | Must be marked legacy/experimental until fixed or hidden. |
| `KCadeque9` | Sequence proofs exist for the actual list-style spec, but totality/invariant story is incomplete. | Not WC O(1): `buf6_concat` is linear; cached `buf6_size` is now implemented in OCaml but not yet part of a proof/refinement bundle. | Research candidate only. |
| `KCadeque9Inline` | Hand-written fast path with `Obj.magic`; can return weakened states outside the proved strong invariant. | Not certified. Depends on unproved next-op repair assumptions. | Experimental only. |
| Rust `ktdeque-deque4` | Correct vector model. | Explicitly not real-time O(1). | Prototype/reference only. |
| OCaml `lib/deque4.ml` | Bench helper. | Explicitly amortized O(log n). | Bench helper only. |

## Findings

### F1. `Buf6` is still an abstract/list-level component in the proof stack

`rocq/KTDeque/Buffer6/SizedBuffer.v` explicitly says that operational `Buf6`
should be a Section-4 deque with cached length, but that the current file is
only the abstract specification:

- `SizedBuffer.v:12-23`: operational design is `Root4` plus cached length, and
  the refinement layer is future work.
- `SizedBuffer.v:27-29`: current `Buf6 X` wraps `list X`.
- `SizedBuffer.v:82-83`: `buf6_size` is `length (buf6_elems b)`.

This is acceptable for semantic proofs, but not for a WC O(1) implementation
claim. Every operation that calls exact `buf6_size`, `buf6_elems`, list append,
or list rebuild is outside the strict bound unless a separate operational
refinement removes that cost.

### F2. Extracted `KCadequeShim.buf6_size` had a direct linear hot path

At the start of the audit, the extracted shim did not implement cached length:

- `ocaml/extracted/kCadequeShim.ml` defined `buf6_elems` by converting the chain
  to a list, then defined `buf6_size b = List.length (buf6_elems b)`.
- `ocaml/extracted/kCadeque9.ml` called `buf6_size h'` on pop and
  `buf6_size t'` on eject.

That was a direct WC O(1) violation, independent of benchmarking.

Update from the overnight implementation: `KCadequeShim.buf6` now carries a
cached logical length, and `buf6_size` reads that field. This removes the direct
OCaml traversal from `KCadeque9` pop/eject, but it does not by itself close the
release gate:

- the Rocq `Buf6` spec is still list-level;
- the cached-length shim is hand-written extraction support and needs an
  explicit refinement statement;
- `KCadequeShim.buf6_pop/eject` still flatten surfaced `Coq_E` elements;
- `KCadeque9.buf6_concat` is still linear.

### F3. Extracted `KCadeque9.buf6_concat` is linear, and `concat` calls it

`KCadeque9` contains direct linear concat paths:

- `ocaml/extracted/kCadeque9.ml:174-175`:
  `buf6_concat a b = KCadequeShim.mkBuf6 (app (buf6_elems a) (buf6_elems b))`.
- `ocaml/extracted/kCadequeShim.ml:59-65`: `mkBuf6` folds over the list,
  injecting each element one by one.
- `ocaml/extracted/kCadeque9.ml:282-297`: every non-empty concat case calls
  `buf6_concat`; the `(T+T)` case also does
  `buf6_concat (buf6_inject m1 cell) m2`.

This makes `kcad9_concat` linear in ordinary reachable states. It is not merely
amortized; it is an immediate traversal/rebuild on the operation itself.

The codebase already contains local evidence that this is known but not
resolved:

- `ocaml/bench/k9_compare.ml:206-208` prints that raw Cadeque9 concat is
  skipped because there is "no O(1) buf6_concat in spec".
- `ocaml/bench/k9_wc_stress.ml:83-86` omits concat-built tests because
  `buf6_concat` is `O(|a|+|b|)` at spec level.

### F4. Cadeque9 comments and reports contradict the implementation

The intended Cadeque9 `(T+T)` idea is to store the right middle spine as a field
inside a `StoredBig9`, avoiding a middle-spine concat:

- `rocq/KTDeque/Cadeque9/Model.v:195-201` shows
  `K9Triple h1 (buf6_inject m1 (StoredBig9 t1 m2 h2)) t2`.
- `rocq/KTDeque/Cadeque9/Ops.v:724-731` repeats this as the structural payoff
  and calls it one allocation.

The actual operation is different:

- `rocq/KTDeque/Cadeque9/Ops.v:770-780` builds
  `StoredSmall9 (buf6_concat t1 h2)` and then calls
  `buf6_concat (buf6_inject m1 cell) m2`.
- The extracted code matches this linear definition
  (`ocaml/extracted/kCadeque9.ml:294-297`).

The existing KB report `kb/reports/cadeque9-complete.md:100-114` says `(T+T)`
concat is "trivially O(1)", but describes the actual `buf6_concat`-based code
as if `buf6_concat` were constant. That report must be superseded or corrected.

### F5. The Cadeque9 drain benchmark does not test concat cost

`ocaml/bench/k9_tt_concat_stress.ml` validates a narrower property:

- Lines `70-83` build `combined = K.kcad9_concat t1 t2` outside the timed eject
  loop, then time `drain_eject combined`.
- Local run on 2026-05-24 showed flat eject batches:
  `N=1000` max about `162 ns/op`, `N=1000000` max about `174 ns/op` for the
  default path.

That is useful evidence that Cadeque9 avoids the old Cadeque8
post-concat drain-eject pathology. It does not validate that `kcad9_concat`
itself is WC O(1). Since F3 shows concat traverses/rebuilds buffers, the bench
cannot support the current concat complexity claim.

The overnight implementation added `ocaml/bench/k9_concat_cost.ml` to time the
concat call itself. Local run on 2026-05-24:

- `N=1000`: about `169,415 ns` per concat.
- `N=10000`: about `3,688,619 ns` per concat.
- `N=100000`: about `122,706,604 ns` per concat.
- `N=1000000`: about `2,924,602,985 ns` per concat.

The exact constants are machine-dependent; the scaling is the important point.
This directly confirms the linear `buf6_concat` blocker.

### F6. Cadeque9's strong invariant omits boundary element restrictions

`rocq/KTDeque/Cadeque9/WFStrong.v:73-81` defines `wf_kcad9_strong` using only
size bounds on `K9Simple`, `K9Triple` head/tail, and the middle. It does not
state that boundary buffers contain only `XBase9` values.

The pop implementation knows this is a gap:

- `rocq/KTDeque/Cadeque9/Ops.v:224-227` says the `XStored9` patterns are
  defensive and that the invariant will be extended later to forbid `XStored9`
  in boundary buffers.
- `ocaml/extracted/kCadeque9.ml:232-237` and `:243-249` return `None` if a
  boundary pop surfaces `XStored9`.

So the current theorems are not yet a clean ADT totality story. A non-empty
value satisfying the stated size-only invariant can still take a defensive
failure branch unless an additional reachable-state invariant is assumed.

This is also an API issue: `ocaml/extracted/kCadeque9.mli:26-38` exposes
constructors for `XStored9`, `StoredBig9`, `K9Simple`, and `K9Triple`. External
OCaml callers can construct states outside the intended reachable subset.

### F7. Inline catenable variants remain outside the proof boundary

At audit start, `KCadeque9Inline` could return a triple after pop/eject without
checking the Cadeque9 `>= 5` boundary invariant. The cached-length change made
it possible to tighten that path: the inline code now falls back to the
certified path when the pre-operation boundary length is `<= 5`.

This removes the specific "temporarily weakened invariant" fast path, but the
inline modules are still not mechanically verified public operations:

- they are hand-written OCaml, not extracted from the Rocq operation;
- they use `Obj.magic` to read level-0 payloads;
- their correctness and cost are not packaged as the same theorem bundle as the
  extracted operations.

They must remain experimental until a proof/refinement story covers the exact
inline code or the inline modules are excluded from the release surface.

### F8. `KCadeque8` remains non-WC O(1), but docs still recommend it

The existing KB already records the remaining bug:

- `kb/reports/cadeque8-wc-o1-evidence.md:32-45` says the `(T+T) eject bug` is
  still open and that eject falls back to O(n).

The code has the fallback:

- `rocq/KTDeque/Cadeque8/WF.v:16-24` documents that the public path falls back
  to `kcad8_from_list` when the structural path fails.
- `ocaml/extracted/kCadeque8.ml:204-207` builds a deque from a list by folding.
- `ocaml/extracted/kCadeque8.ml:368-374` uses `kcad8_to_list` and
  `kcad8_from_list` on pop fallback.
- `ocaml/extracted/kCadeque8.ml:378-384` uses `rev (kcad8_to_list k)` and
  `kcad8_from_list` on eject fallback.

At audit start, these docs were stale and unsafe:

- `README.md:223-245` says Section 6 is shipped as Cadeque8 and strict WC O(1).
- `ocaml/README.md:133-146` says all five `kcad8_*` operations are WC O(1) and
  recommends `KCadeque8` for new code.
- `ocaml/extracted/dune:13-17` marks `KCadeque8` as the recommended catenable
  API and bench-validated strict WC O(1).

The overnight implementation removed those current release recommendations from
the root README, OCaml README, and extraction dune comments. Historical reports
that mention the old claims now carry supersession/status pointers.

### F9. The catenable shim has another unresolved WC O(1) obligation

`KCadequeShim.buf6_pop` and `buf6_eject` flatten a surfaced `KTDeque` element:

- `ocaml/extracted/kCadequeShim.ml:130-161` calls `KTDeque.Coq_E.to_list e` on
  pop.
- `ocaml/extracted/kCadequeShim.ml:163-194` calls `List.rev
  (KTDeque.Coq_E.to_list e)` on eject.

The shim header acknowledges that a surfaced level `l > 0` element contains
`2^l` base values (`kCadequeShim.ml:12-15`). The earlier Cadeque8 audit also
records this as a missing level-0/bounded-surface invariant
(`kb/reports/cadeque8-wc-o1-evidence.md:154-160`).

This must be resolved before any catenable implementation can be certified
strict WC O(1). Either the surfaced element is proved bounded in all public
states, or the representation must avoid flattening it in one operation.

### F10. C port is strong empirically, but still has a refinement and fallback gap

Local command `make -C c check` passed on 2026-05-24. It ran the main tests,
debug tests, region tests, thread tests, and `wc_test`. The reported allocation
maxima stayed flat:

- `n=1000`: total max per op `7`.
- `n=10000`: total max per op `7`.
- `n=100000`: total max per op `8`.

This is useful evidence, but not a proof. At audit start, the C code still had
fallback branches with no Rocq counterpart that copied `2 * depth` buffers in
`NDEBUG` builds. The overnight implementation removed those recovery loops and
replaced them with fail-fast `abort()` calls after the existing assertions.

That removes the hidden O(depth) release path, but the proof/refinement gap
remains: the final story must prove these branches unreachable and make that
proof part of the C refinement, or otherwise remove the branches entirely.

### F11. Non-catenable KTDeque needs one public proof spine

The KTDeque non-catenable layer is the closest to the target:

- `rocq/KTDeque/DequePtr/OpsKTSeq.v:1458-1505` proves `kt4` sequence laws
  conditional on `PushOk`/`PopOk`.
- `rocq/KTDeque/DequePtr/OpsKTRegular.v:30-53` documents closed preservation
  theorems for `kt2` and says the combination with `Footprint.v` gives the
  WC O(1) theorem for the KChain layer.
- `rocq/KTDeque/DequePtr/Footprint.v` contains constant-cost lemmas for the
  packet-level cost monad, such as `exec_push_pkt_C_cost`,
  `exec_inject_pkt_C_cost`, `exec_pop_pkt_C_cost`, and
  `exec_eject_pkt_C_cost`.

The clarity gap is that the public/extracted story is spread across variants:
`kt2`, `kt3`, `kt4`, packet cost functions, and OCaml extraction. The report
does not claim a concrete bug here. It says the proof chain must be packaged as
one statement per public function family:

- totality under the regular invariant;
- sequence correctness;
- invariant preservation;
- constant cost bound;
- extraction/refinement mapping to the OCaml function actually exposed.

### F12. Rust and handwritten OCaml variants are intentionally not WC O(1)

These are correctly documented, but they must stay out of any blanket claim:

- `rust/ktdeque-deque4/src/lib.rs:6-14` says the v0 Rust implementation uses a
  persistent `Vec<T>` and is not real-time O(1). The operations copy vectors
  (`:68-72`, `:81-87`, `:94-97`, `:106-113`).
- `ocaml/lib/deque4.ml:1-12` says the hand-written OCaml `Deque4` is a bench
  helper, amortized O(log n), and not part of the public opam package.

## Mechanical checks run during this audit

Commands:

- `make -C c check`: passed.
- `dune build`: initially blocked by missing local `rocq`, `qcheck`, and
  `monolith`; after those tools were installed, passed on 2026-05-24.
- `dune runtest`: passed after the tools were installed; QCheck suites for
  `Deque4`, `KTDeque`, and the catenable abstract/full variants completed.
- `dune exec ocaml/bench/k9_qcheck.exe`: passed after the cached-length shim
  change (`200` runs, `40,000` operations total).
- `dune exec ocaml/bench/k8i_qcheck.exe`: passed after the cached-length shim
  change (`500` runs, `100,000` operations total).
- `dune exec --profile=release ocaml/bench/k9_tt_concat_stress.exe`: passed and
  showed flat drain-eject batches, but does not time concat itself.
- `dune exec --profile=release ocaml/bench/k9_concat_cost.exe`: added and run;
  it times `KCadeque9.kcad9_concat` itself and shows clear scaling with input
  size.
- `tools/check_wc_o1_release_gate.sh`: added by the overnight implementation.
  It now passes the docs honesty scan and fails on five real blocker groups:
  unbounded Cadeque9 concat, Cadeque8 fallback rebuilds, shim flattening,
  unverified inline paths, and C branches outside the proof boundary.
- `rg -n "Admitted|admit\.|Axiom|Parameter|Abort" rocq/KTDeque`: no
  `Admitted`/`admit.` hits were found. The hits are module-type parameters and
  axioms in interface files, plus one `Abort` in `RBR/Succ.v`.

The last check is not a substitute for `Print Assumptions` on public theorems.
It is only a smoke test.

## Required plan to reach the desired clarity

### P1. Define the public surface first

Create a single status matrix in the KB and README that marks each module as
one of:

- `production candidate`;
- `proof/reference`;
- `experimental optimization`;
- `legacy/known non-WC`;
- `prototype/not WC`.

Then enforce it in packaging:

- Export abstract types for production modules. Do not expose constructors for
  reachable-state-sensitive structures such as `K9Triple`, `XStored9`, or
  `StoredBig9`.
- Move `to_list`, `buf6_elems`, `buf6_size`, and diagnostic constructors into a
  non-latency-critical/debug interface when possible.
- Remove docs that recommend `KCadeque8` or `KCadeque9` as strict WC O(1) until
  the proof and implementation gates below pass.

### P2. State the exact theorem shape for every public operation

For each production operation, require four theorem families:

1. Representation correctness:
   `repr op(args) = abstract_op (repr args)`.
2. Totality/success:
   under the public invariant, non-empty operations return `Some` exactly when
   the abstract sequence is non-empty, and update operations do not fail.
3. Invariant preservation:
   the resulting representation satisfies the same public invariant.
4. Worst-case cost:
   a bound `cost(op(args)) <= C_op` where `C_op` is a closed constant
   independent of length, history, sharing, and prior operation sequence.

Conditional sequence lemmas are useful, but they are not enough for a public ADT
claim. The public theorem must remove the condition by proving totality under
the invariant.

### P3. Build the operational `Buf6` refinement before claiming catenable O(1)

The catenable layer cannot be certified while `Buf6` is just a list-level spec
or an extracted chain without cached length.

Required work:

- Implement the operational `Buf6` promised in `SizedBuffer.v`: Section-4 root
  plus cached length, or another representation with equivalent constant-time
  size/emptiness operations. The OCaml shim now caches length; this still needs
  to be represented in the proof/refinement story.
- Prove that extracted `buf6_size` is O(1) and tied to the logical length. No
  production operation may compute size by list traversal.
- Eliminate or structurally avoid unbounded `buf6_concat`. For every call site,
  prove at least one argument is statically bounded by a small constant, or
  change the representation so the operation stores a catenation node/cell
  instead of merging buffers.
- Prove a bounded-surface invariant for `KCadequeShim.buf6_pop/eject`, or remove
  the one-operation flattening of arbitrary-level `Coq_E.to_list`.

### P4. Redesign Cadeque9 concat around a real constant-time encoding

The comments already point to the intended `(T+T)` design:

`K9Triple h1 (buf6_inject m1 (StoredBig9 t1 m2 h2)) t2`

That avoids concatenating `m1` and `m2`. The implementation must be brought back
to such a constant-shape operation, or a different constant-shape encoding must
be chosen and proved.

The redesign also has to address `S+S`, `S+T`, and `T+S` cases. Current code
merges unbounded simple/boundary buffers with `buf6_concat`. A valid design must
either:

- bound `K9Simple` size by construction;
- normalize large simple values into triples before catenation in O(1);
- encode the boundary join as stored cells without merging unbounded buffers;
- or use a genuinely catenable operational buffer whose own concat is proved
  WC O(1).

### P5. Remove list fallbacks from production public operations

For production modules, ban the following from core operation implementations:

- `to_list` followed by rebuild;
- `from_list` in pop/eject/concat fallback paths;
- `List.length` or list traversal for operational size;
- unbounded `List.rev`, `app`, or fold in a latency-critical operation;
- `Obj.magic` fast paths not covered by a theorem over the same invariant.

These functions may exist in semantic/debug modules, but not in the operation
body used by the strict-latency API.

### P6. Add syntactic and semantic CI gates

Benchmarks are useful but secondary. The CI gate should include:

- `Print Assumptions` reports for the public theorems.
- A static scan over extracted production operation bodies rejecting
  `kcad*_to_list`, `kcad*_from_list`, `buf6_elems`, `List.length`, `app`,
  `List.rev`, and unbounded folds.
- A call-graph check from every public operation to ensure no linear semantic
  helper is reachable.
- Differential/property tests against list semantics.
- Adversarial benchmarks that time the operation itself, not only the drain
  after the operation. This specifically means a `kcad9_concat` timing harness
  that times one concat per sample across increasing sizes and records the max.
- Fallback counters that are zero in debug and release builds, with branches
  removed or trapped if the proof says they are unreachable.

### P7. Clarify the C proof boundary

For the C port:

- Decide whether it is a verified implementation or an empirical port.
- If verified, state and prove a refinement relation from the C `FULL`/`DIFF`
  representation to the Rocq model.
- Prove or remove the asserted-unreachable fallback branches.
- Keep allocation-count and fallback-counter tests in CI, but label them as
  evidence, not proof.

### P8. Supersede stale reports and docs

Immediate documentation actions:

- Mark `kb/reports/cadeque9-complete.md` as superseded by this audit, or edit it
  to say Cadeque9's structural idea is not implemented as WC O(1).
- Edit `README.md`, `ocaml/README.md`, and `ocaml/extracted/dune` so they no
  longer recommend `KCadeque8` as strict WC O(1).
- Add a short "Current WC O(1) status" page that readers can trust without
  reading all historical reports.
- Keep historical reports, but add status banners to avoid stale conclusions
  being quoted as current fact.

## Minimum release gate for a strict WC O(1) claim

Do not ship a strict WC O(1) catenable API until all of the following are true:

1. The public API exposes only abstract constructors for the production type.
2. For each public op, there is an unconditional functional correctness theorem
   under the public invariant.
3. For each public op, there is an invariant preservation theorem under the same
   invariant.
4. For each public op, there is a constant cost theorem connected to the code
   that is extracted or hand-ported.
5. The extracted production operation call graph contains no list rebuild,
   unbounded size traversal, unbounded concat, or fallback rebuild.
6. Adversarial benches time the operation itself and remain flat across size.
7. C/Rust/other ports are either proved/refined or explicitly documented as
   non-verified ports with no stronger claim than the evidence supports.

## Bottom line

The project has valuable pieces: the non-catenable KTDeque proof work, strong C
testing, and a clear understanding of the old Cadeque8 failure mode. But the
catenable implementation is not yet mechanically defensible as worst-case O(1).

The central cleanup is to make the operational boundary explicit:

- semantic list specs stay in Rocq as specs;
- production operation bodies must not call list-level helpers;
- every invariant needed for totality and bounded cost must be part of the
  public theorem, not a comment or benchmark assumption.

Once that is done, the codebase can be simplified around one production
non-catenable implementation and one catenable candidate, with old variants
clearly marked as historical or experimental.
