# Cadeque9 — paper-faithful KT99 §6 with full WC O(1)

> **Status:** drafted 2026-05-24, after discovering that our [Cadeque8]
> uses a fundamentally weaker invariant than the KT99 §6 algorithm.
> Viennot et al.'s reference Coq development confirms the paper's
> required invariants — size ≥ 3 for stored cells, size ≥ 5 for node
> buffers — which our Cadeque8 has relaxed to non-emptiness (size ≥ 1).
> The (T+T) eject WC O(1) bug ([commit 91eddfc], partial fix) is a
> direct consequence: under our weaker invariant, concat is forced to
> produce stored cells with empty suffixes, which the rebalance cannot
> safely unfold.  Strengthening to the paper's invariant requires a
> structural redesign documented here.
>
> This plan **supersedes** [cadeque8-tt-eject-wc-o1-plan.md], which
> proposed local fixes (Options A-E) that turn out to be patches on
> the wrong tree.

## 1. The discovery

Viennot's `theory/Cadeque/Types.v` (external reference) encodes the
KT99 §6 invariant intrinsically via dependent types:

```coq
Inductive stored (A : Type) : level -> Type :=
  | Big {l qp qs a lC rC} :
      prefix' (stored A l) (3 + qp) ->          (* size ≥ 3 *)
      chain A (S l) a only lC rC ->             (* CHAIN, not deque *)
      suffix' (stored A l) (3 + qs) ->          (* size ≥ 3 *)
      stored A (S l)
  | Small {l q} :
      suffix' (stored A l) (3 + q) ->           (* size ≥ 3 *)
      stored A (S l)

Inductive node' (A : Type) : arity -> kind -> color -> Type :=
  | Only {qp qs a C} :
      node_coloring qp qs (S a) C ->
      prefix' A (5 + qp) ->                     (* boundary ≥ 5 *)
      suffix' A (5 + qs) ->                     (* boundary ≥ 5 *)
      ...
```

Two paper-mandated invariants are missing from our Cadeque8:

1. **Size bounds**: ≥ 5 for boundary buffers (`h`, `t` in K8Triple),
   ≥ 3 for stored cell prefixes and suffixes.

2. **No sub-deque inside stored cells**: Viennot's `Big` contains a
   *chain* (`chain A (S l) ...`), not a *deque*.  A chain has no
   boundary buffers and no boundary invariant — it's just a level-l+1
   spine of stored cells.  Our `StoredBig8 _ (KCadeque8 X) _` recursive
   wrapper is what forces us to use `K8Triple ø _ ø` to "embed" a
   middle buffer, creating the empty-boundary cells that break
   rebalance.

The combination of these two — weak size bound + recursive deque
nesting — is what makes our (T+T) concat unsafe.  Strengthening only
(1) (Option E in the prior plan) without also fixing (2) cannot close
the gap, because we'd still have nested `K8Triple ø _ ø` carriers
from concat.

## 2. Target invariant (extrinsic, our style)

In Coq, Viennot uses intrinsic dependent typing — type indices
enforce sizes statically.  In our project the convention (per ADR-0004)
is **extrinsic invariants** stated as Prop predicates over otherwise
loose types.

The translation:

```coq
(* SIZED-BUFFER PREDICATES *)

Definition buf6_size {X : Type} (b : Buf6 X) : nat :=
  List.length (buf6_elems b).

(* For the rest of this doc:  |b| := buf6_size b. *)

Definition wf_node_buf {X : Type} (b : Buf6 (KElem8 X)) : Prop :=
  buf6_size b >= 5.

Definition wf_stored_buf {X : Type} (b : Buf6 (KElem8 X)) : Prop :=
  buf6_size b >= 3.

(* STORED CELLS *)

Definition wf_stored9 {X : Type} (s : Stored9 X) : Prop :=
  match s with
  | StoredSmall9 b           => wf_stored_buf b
  | StoredBig9   pre sm suf  =>
      wf_stored_buf pre /\
      wf_stored_buf suf /\
      Forall wf_stored9 (buf6_elems sm)
        (* Note: sm is Buf6 (Stored9 X) — a chain of stored cells.
           No boundary buffer.  No recursive K8Triple. *)
  end.

(* TOP-LEVEL DEQUE *)

Definition wf_kcad9_strong {X : Type} (k : KCadeque9 X) : Prop :=
  match k with
  | K9Empty            => True
  | K9Simple b         => wf_node_buf b
  | K9Triple h m t     =>
      wf_node_buf h /\
      wf_node_buf t /\
      Forall wf_stored9 (buf6_elems m)
  end.
```

Note the type-level change: `StoredBig9` now wraps a `Buf6 (Stored9 X)`
directly, not a `KCadeque9 X`.  This is the structural difference
from Cadeque8 — no recursive deque nesting.

## 3. Why the structural change matters

Under Cadeque8's `StoredBig8 pre (KCadeque8 X) suf`, the inner deque
is a *full* `KCadeque8` with its own h/t.  Concat constructs cells like
`StoredBig8 t1 (K8Triple h2 m2 ø) ø` to carry an arbitrary deque
fragment — but this introduces `K8Triple` values with empty boundaries
(which we tolerated because Cadeque8's wf doesn't forbid them).

Under the new `StoredBig9 pre sm suf` (with `sm : Buf6 (Stored9 X)`),
there is no inner deque to nest — `sm` is just a buffer of stored
cells with no boundary structure.  Concat constructs cells like:

```coq
StoredBig9 t1                                  (* size ≥ 3, taken from t1 *)
           (push (Small h2_compact) m2)        (* sm: chain *)
           t2_compact                          (* size ≥ 3, taken from t2 *)
```

where `h2_compact` and `t2_compact` are small slices of h2 and t2.
No nested K9Triple-with-empty-boundary.  No empty-suf cells.  Rebalance
unfolds the cell directly: pre → new boundary, sm → injected back into
outer m, suf → new boundary.

## 4. How the size invariants prevent every edge case

Consider concat (T+T) under the new invariant:

```
arg1 = K9Triple h1 m1 t1     wf: |h1| ≥ 5, |t1| ≥ 5
arg2 = K9Triple h2 m2 t2     wf: |h2| ≥ 5, |t2| ≥ 5
```

To build the result's boundary cell, we need cell.pre and cell.suf
each of size ≥ 3.  Strategy: borrow 3 from t1 for cell.pre, 3 from h2
for cell.suf, splice the residues into sm/result-h/result-t.  Concrete:

```
Let (t1_keep, t1_borrow) = split t1 at index 3 from the right.
    |t1_borrow| = 3,  |t1_keep| = |t1| - 3 ≥ 2.

Let (h2_borrow, h2_keep) = split h2 at index 3 from the left.
    |h2_borrow| = 3,  |h2_keep| = |h2| - 3 ≥ 2.

cell = StoredBig9 t1_borrow                    (* pre, size 3 *)
                  (* sm = m2 with adjustments — see below *)
                  h2_borrow                    (* suf, size 3 *)

m_new = inject m1 cell

result = K9Triple h1 m_new t2
```

But wait — what about t1_keep, h2_keep, and m2?  Those still need to
be carried.  They're size 2 each (so don't satisfy the ≥ 3 stored
buf invariant) and m2 is a buffer of stored cells.

This is where the **eager-rebalance pre-concat** step matters in KT99:
before applying the concat recipe, the algorithm ensures the input
buffers have enough surplus.  If h1 is at size exactly 5, the concat
must allow it to stay at 5 (no shrinkage).  If h2 is at size exactly
5, we can borrow 3 but t1_keep and h2_keep need a home.

The cleanest answer:
**t1_keep becomes a degenerate cell `StoredSmall9 (t1_keep ++ extras)`**
injected at the end of m1, padded with enough elements to satisfy
size ≥ 3.  Same for h2_keep.

This is where the **paper's repair-case dance** comes in — KT99's §6
algorithm has specific cases handling the small-buffer transitions.
The Cadeque6 module in this project already implements §12.4 (the
five repair cases 1a, 1b, 2a, 2b, 2c) at the imperative-DSL layer.
**We can reuse the design from Cadeque6** for the case analysis.

## 5. Implementation strategy: new module `Cadeque9`

**Recommend a NEW module, not in-place refactoring of Cadeque8.**

Rationale:
- Cadeque8's `Stored8` and `KCadeque8` type definitions are baked into
  ~30 Rocq files and ~6 OCaml files (extracted, shim, inline).
- Changing the type definition has cascading effects on every proof
  and every extracted-OCaml consumer.
- A clean new `Cadeque9/` lets us iterate on the algorithm + proofs
  without risking the production-ready Cadeque8 + Cadeque8Inline ops.
- Once Cadeque9 ships with full WC O(1), we can:
  - Compare benches side-by-side.
  - Re-target `KCadeque8Inline` to wrap `KCadeque9` (if perf allows).
  - Mark Cadeque8 as deprecated.

Module layout:

```
rocq/KTDeque/Cadeque9/
  Model.v            -- types + sequence semantics
  WFStrong.v         -- size ≥ 3 / ≥ 5 invariants + helpers
  Ops.v              -- push, inject, pop, eject, concat (paper recipe)
  Repair.v           -- the five KT99 §6.2 repair cases (1a..2c)
                       — adapted from Cadeque6/RepairS12.v
  Seq.v              -- sequence-preservation theorems
  WF.v               -- wf preservation theorems for all 5 ops
  OpsFast.v          -- non-option-typed variants (kt4-style)
  Extract.v          -- extraction directives for OCaml
```

## 6. Step-by-step plan

### Phase 1 — types and sequence semantics  (~1 day)

**File**: `rocq/KTDeque/Cadeque9/Model.v`

```coq
Inductive KElem9 (X : Type) : Type :=
  | XBase9   : X -> KElem9 X
  | XStored9 : Stored9 X -> KElem9 X
with Stored9 (X : Type) : Type :=
  | StoredSmall9 : Buf6 (KElem9 X) -> Stored9 X
  | StoredBig9   : Buf6 (KElem9 X) ->            (* prefix      *)
                   Buf6 (Stored9 X) ->            (* sm = stored chain *)
                   Buf6 (KElem9 X) ->            (* suffix      *)
                   Stored9 X
with KCadeque9 (X : Type) : Type :=
  | K9Empty  : KCadeque9 X
  | K9Simple : Buf6 (KElem9 X) -> KCadeque9 X
  | K9Triple : Buf6 (KElem9 X) ->                (* head boundary       *)
               Buf6 (Stored9 X) ->                (* m = stored chain  *)
               Buf6 (KElem9 X) ->                (* tail boundary       *)
               KCadeque9 X.
```

Plus the recursive `kcad9_to_list / stored9_to_list / kelem9_to_list`
following the same inline-fix pattern as Cadeque8/Model.v.

**Deliverables**: type definitions, sequence flattening, ~200 lines.
**Risk**: low — almost identical to Cadeque8 modulo the `StoredBig9` field type.

### Phase 2 — size predicates + sized-buffer helpers  (~0.5 day)

**File**: `rocq/KTDeque/Buffer6/SizedBuffer.v` (extend existing)

Add:
```coq
Definition buf6_size_ge {X : Type} (n : nat) (b : Buf6 X) : Prop :=
  buf6_size b >= n.

Lemma buf6_push_size_ge : forall X (x : X) n b,
  buf6_size_ge n b -> buf6_size_ge (S n) (buf6_push x b).
(* and similar for inject, pop, eject, etc. *)
```

**Deliverables**: ~10 lemmas about `buf6_size_ge` under push/inject/pop/eject.
**Risk**: low.

### Phase 3 — split / slice primitives  (~0.5 day)

**File**: `rocq/KTDeque/Buffer6/SmallMoves.v` (extend existing)

The (T+T) concat needs:
```coq
Definition buf6_split_front : forall X, nat -> Buf6 X -> Buf6 X * Buf6 X.
(* split_front n b returns (first_n_elts, rest); requires |b| ≥ n *)

Definition buf6_split_back : forall X, nat -> Buf6 X -> Buf6 X * Buf6 X.
```

For n = 3 in our use, these are bounded constants — each call does
3 pops/ejects, so O(1).  The implementation:

```coq
Definition buf6_take3 (b : Buf6 X) : option (Buf6 X * Buf6 X) :=
  match buf6_pop b with
  | None => None
  | Some (x1, b1) =>
      match buf6_pop b1 with
      | None => None
      | Some (x2, b2) =>
          match buf6_pop b2 with
          | None => None
          | Some (x3, b3) => Some (mkBuf6 [x1; x2; x3], b3)
          end
      end
  end.
```

**Deliverables**: 4 splice primitives + their seq/size laws (~150 lines).
**Risk**: low — purely combinatorial.

### Phase 4 — push / inject  (~0.5 day)

These are trivial — they grow boundary buffers.  Under the new wf,
they preserve size ≥ 5 automatically (since size only increases).

```coq
Definition kcad9_push (x : X) (k : KCadeque9 X) : KCadeque9 X :=
  match k with
  | K9Empty            => K9Simple (mkBuf6 [XBase9 x])
  | K9Simple b         => K9Simple (buf6_push (XBase9 x) b)
  | K9Triple h m t     => K9Triple (buf6_push (XBase9 x) h) m t
  end.
```

**Wait** — for `K9Empty` case, the result is `K9Simple` with a
1-element buffer.  Under wf ≥ 5, this is wf-violating!  Yes — this
means `wf_kcad9_strong` is **not preserved** by single pushes from
empty.  The wf must be **conditional**: hold only on "established"
deques.

**Resolution**: distinguish between K9Simple of "small" size (1-4)
and "large" size (≥ 5).  Until the deque grows past size 5, we're in
a transient state.  Define `wf_kcad9_strong` to:

```coq
| K9Simple b   => buf6_size b >= 1   (* allow small for very-new deques *)
| K9Triple h m t  => |h| ≥ 5 /\ |t| ≥ 5 /\ Forall wf_stored9 m
```

Or alternatively, use the §6 paper's actual top-level recipe:
- K9Empty: zero elements.
- K9Simple: 1-N elements, where the buffer has whatever size.  Concat
  promotes to K9Triple only when both sides are non-empty, AND the
  promotion guarantees ≥ 5 boundaries.
- K9Triple: always ≥ 5 boundaries.

Concretely: `kcad9_push x K9Simple b` stays as `K9Simple` (grow the
buffer).  Even if b reaches large size, K9Simple is allowed — the
top-level deque doesn't have to be K9Triple.  The K9Triple shape is
only used when concat creates it.

**Deliverables**: push/inject defs + size-preservation + seq lemmas (~80 lines).
**Risk**: low.

### Phase 5 — pop / eject with eager rebalance  (~2 days)

This is the hard part.  Under the new invariant, pop must trigger
rebalance when the boundary drops to size 4 (NOT to size 0).

**Algorithm** (pop from `K9Triple h m t`, with `|h| ≥ 5`):

```
pop K9Triple h m t :
  case h.size of
    n when n >= 6 →
      (* No rebalance needed; just shrink h. *)
      let (x, h') := buf6_pop h in
      PopOk x (K9Triple h' m t)
    n when n == 5 →
      (* Boundary is at the lower threshold; pop would shrink it
         below 5.  Trigger rebalance to refill h. *)
      let (x, h') := buf6_pop h in
      (* h' has size 4 now — needs refill. *)
      rebalance_h_to_5 (K9Triple h' m t)
```

The `rebalance_h_to_5` step:
- Peek at m's leftmost stored cell.
- If it's `StoredSmall9 b`: |b| ≥ 3.  Append the 3+ elements to h'
  to reach |h'| ≥ 7.  Replace m's leftmost cell with whatever's left.
  But |b| - (5 - |h'|) ≥ |b| - 4.  Hmm — only if |b| ≥ 5 is this safe;
  otherwise we'd shrink b below ≥ 3 (the stored buf invariant).
  → Need a different recipe: pull only as many elements as needed,
    leaving b ≥ 3.
- If it's `StoredBig9 pre sm suf`: unfold into (pre, sm cells, suf)
  and inject them into h' + outer m.

This **is the KT99 §6.2 repair-case dance** — five cases (1a, 1b, 2a,
2b, 2c) corresponding to different cell shapes and buffer-size
combinations.  Cadeque6's `RepairS12.v` and `Adopt6.v` already
implement these at the imperative layer; we can adapt the abstract
case dispatch.

**Deliverables**: pop, eject + rebalance + repair-case dispatch
(~600 lines), modeled on Cadeque6/RepairS12.v.
**Risk**: medium — the case analysis is intricate.

### Phase 6 — concat with buffer splitting  (~2 days)

`kcad9_concat (K9Triple h1 m1 t1) (K9Triple h2 m2 t2)` under
`|h1|, |t1|, |h2|, |t2| ≥ 5`:

```coq
| K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
    (* Split t1 keeping ≥ 5 elements for the cell.pre lower-bound is
       ≥ 3.  So we can use ALL of t1 (size ≥ 5 ≥ 3). *)
    (* Split h2 to feed cell.suf (≥ 3 elements).
       If |h2| ≥ 6: take 3 from h2's right end, leave |h2| - 3 ≥ 3.
                     But h2_kept is "used" as a stored-buf in concat —
                     so |h2_kept| ≥ 3 is enough.  But where does h2_kept go?
       If |h2| = 5: take 3, leave 2.  2 < 3, not a stored-buf.
                     → Different recipe: pull more from h2 OR use h2 as a
                       single cell. *)

    (* Recipe (cleanest, working for |t1|, |h2| ≥ 5): *)
    let cell := StoredBig9 t1                       (* size ≥ 5 ≥ 3 *)
                           m2                       (* the inner chain *)
                           h2                       (* size ≥ 5 ≥ 3 *)
    in
    let m_new := buf6_inject m1 cell in
    K9Triple h1 m_new t2
```

**Wait — this is incredibly clean.**  The new encoding uses **all of
t1 as cell.pre, all of h2 as cell.suf, and m2 directly as the cell's
sm-chain** (no `K9Triple ø _ ø` carrier).

Sizes:
- cell.pre = t1, size ≥ 5 ≥ 3 ✓
- cell.suf = h2, size ≥ 5 ≥ 3 ✓
- cell.sm = m2, a buf of stored cells ✓
- Result.h = h1, size ≥ 5 ✓
- Result.t = t2, size ≥ 5 ✓

**Concat is `inject + 1 alloc` = O(1).  No splitting needed.**

(Same recipe for (S+T) and (T+S) — push/inject the boundary buffer
of the simple side as a `StoredSmall9` cell at the appropriate end
of m.)

This is the **core payoff** of the structural change: without sub-
deque nesting, concat becomes obviously O(1) and the resulting cells
are obviously safe.

**Deliverables**: concat (4 cases) + seq + wf (~200 lines).
**Risk**: low — concat becomes trivial.

### Phase 7 — sequence preservation  (~1 day)

For each op, prove `to_list (op k) = expected`.  Mostly identical to
Cadeque8/Seq.v but with the new `Stored9` flatten:

```coq
Lemma stored9_to_list_big :
  forall X pre sm suf,
    stored9_to_list (StoredBig9 pre sm suf) =
      kelem9_flat_list (buf6_elems pre)
      ++ stored9_flat_list (buf6_elems sm)
      ++ kelem9_flat_list (buf6_elems suf).
Proof. reflexivity. Qed.
```

**Deliverables**: 5 seq theorems + helpers (~400 lines).
**Risk**: low — mechanical.

### Phase 8 — wf preservation  (~2 days)

For each op, prove `wf_kcad9_strong k → wf_kcad9_strong (op k)`.
The hard case is `pop` and `eject` — need to show:
1. Rebalance preserves wf (size ≥ 5 boundary).
2. Repair-case dispatch is total (every reachable state has a case).
3. Each repair case produces a wf result.

This benefits from Cadeque6's existing repair-case formalization.

**Deliverables**: 5 wf preservation theorems + repair-case lemmas (~500 lines).
**Risk**: medium-high — pop/eject preservation is the hardest part.

### Phase 9 — fast variants  (~0.5 day)

Mirror Cadeque8's `OpsFast.v`: define `_fast` variants returning
`push_result9` / `pop_result9` flat sums.  Prove them equal to the
option-typed versions.

**Deliverables**: 5 fast ops + equivalence theorems (~200 lines).
**Risk**: low.

### Phase 10 — OCaml extraction  (~0.5 day)

Extraction directives for Cadeque9 → `kCadeque9.ml`.  Reuse
`KCadequeShim` for the buf6 layer.

**Deliverables**: extraction file + extracted .ml/.mli (~150 lines).
**Risk**: low.

### Phase 11 — benches + KB updates  (~0.5 day)

- Adapt `k8i_qcheck`, `k8_concat_pop_stress`, `k8_concat_eject_stress`,
  `k8_tt_concat_stress`, `k8_wc_stress`, `k8_aggregate` to use
  `KCadeque9`.
- Run full bench suite, confirm all max-batch flat across N.
- KB note: this plan landed, Cadeque8 deprecated.

**Deliverables**: ported bench files + run results + KB updates.
**Risk**: low.

## 7. Total effort estimate

| Phase                      | Days |
|----------------------------|------|
| 1. Types + sequence       | 1    |
| 2. Size predicates        | 0.5  |
| 3. Split/slice primitives | 0.5  |
| 4. Push/inject            | 0.5  |
| 5. Pop/eject + rebalance  | 2    |
| 6. Concat                 | 2    |
| 7. Seq preservation       | 1    |
| 8. WF preservation        | 2    |
| 9. Fast variants          | 0.5  |
| 10. OCaml extraction      | 0.5  |
| 11. Benches + KB          | 0.5  |
| **Total**                 | **11 days** |

Roughly two weeks of focused work.  The bulk is Phases 5 and 8
(pop/eject + their wf preservation).

## 8. Risk assessment

**Highest-risk phases:**
- **Phase 5** (pop/eject + rebalance): repair-case dispatch is
  intricate.  Mitigation: lean heavily on Cadeque6/RepairS12.v's
  existing case analysis — we already have a proven implementation
  of the same algorithm at the imperative DSL layer.
- **Phase 8** (wf preservation for pop/eject): proves the repair
  cases preserve the strong invariant.  Cadeque6/WF.v has analogous
  proofs; adapt to the extrinsic style.

**Schedule risk**: 11 days is the optimistic estimate.  Add 50%
buffer for surprises (the Cadeque8 work surfaced 2 unexpected bugs
during plan execution; expect similar here).  Realistic estimate:
**3 weeks**.

**Correctness risk**: the design is faithful to Viennot (proven
formalization) and to KT99 §6 (peer-reviewed paper).  We're not
inventing new algorithms — we're mirroring an existing proof.

## 9. Why a new module, not refactor

Cadeque8 ships today.  It has:
- Five fully proven ops (seq + wf).
- A `KCadeque8Inline` OCaml override with empirically validated WC O(1)
  on most workloads.
- Bench-validated faster than Viennot's hand-coded OCaml on pop, eject,
  concat, adversarial workloads (commits `02bc875`, `5c43717`).
- Two known edge-case bugs (T+T eject; small-buffer concat).

Refactoring Cadeque8 in place would:
- Require touching ~30 Rocq files.
- Risk breaking the already-shipped consumer (`KCadeque8Inline`).
- Force every proof to re-verify under stronger invariants.

Building Cadeque9 alongside:
- Allows incremental landing (phase-by-phase, tested independently).
- Lets us compare benches Cadeque8 vs Cadeque9.
- Once Cadeque9 stabilizes, Cadeque8 can be deprecated and removed —
  but that's an explicit step.

## 10. Open questions

1. **K9Simple invariant choice.** Should K9Simple require size ≥ 5
   (and force fall-back to K9Empty when shrinking below)? Or allow
   any size including 1?  Viennot's `Only_end` permits size ≥ 1
   (the `q` in `S q` ranges over all nats).  We should match.

2. **Does `Stored9` need level indexing?**  Viennot's `stored A l`
   is level-indexed; ours would be extrinsic.  An extrinsic
   "no infinite nesting" predicate may be needed for termination of
   `to_list`.  Investigate during Phase 1.

3. **Re-extracting `KCadeque8Inline` against Cadeque9?**  The inline
   OCaml hot path is tightly coupled to `KCadeque8`'s shape.
   Re-targeting would require a `KCadeque9Inline` from scratch.
   Defer to a follow-up; Cadeque9 ships first.

4. **Can we drop `Cadeque8` after Cadeque9 lands?**  Yes, after a
   migration period.  External users (if any) need an upgrade path.

5. **Should `Cadeque7` (the design doc that was never built) be
   resurrected as Cadeque9?**  Cadeque7's design (per
   `kb/spec/kcadeque-design.md`) is closer to Viennot's packet+chain
   structure.  Investigate during Phase 1 whether to fold Cadeque7's
   design into Cadeque9 or keep our recursive-Stored approach with
   the paper-faithful invariants only.

## 11. Headline summary

The (T+T) eject WC O(1) bug is a symptom of an invariant that's
fundamentally weaker than the algorithm requires.  KT99 §6 mandates
size ≥ 3 for stored cells and ≥ 5 for node boundaries.  Under these
bounds, concat becomes trivially O(1) (one allocation, no buffer
splitting needed), and all the rebalance edge cases vanish.

The fix is a new module `Cadeque9` that:
1. Drops the recursive `StoredBig _ KCadeque _` nesting in favor of
   `StoredBig _ (Buf6 Stored) _` (matching Viennot's `Big prefix
   chain suffix`).
2. Adds the paper-mandated size invariants extrinsically.
3. Re-implements the five repair cases at the abstract layer (we
   already have them at the imperative layer in Cadeque6).

Estimated **3 weeks of focused work** (11 nominal days + 50% buffer).
The deliverable: a Coq-extracted catenable deque that mechanically
realizes KT99 §6, with **provable** WC O(1) per op on every reachable
state.  Cadeque8 stays in place during the transition; the inline
fast-path module either re-targets later or is deprecated alongside
Cadeque8.
