(** * Module: KTDeque.Cadeque6.Repair -- operational repair primitives.

    First-time reader: read manual §12.4 and [kb/spec/why-catenable.md]
    before this file.

    ## Why this exists

    Phase 5.6 of the catenable plan: introduce the operational
    primitives that reshape ill-sized triples into well-sized
    ones, so that the operational [cad_*_op] versions of push /
    inject / pop / eject / concat preserve [regular_cad].

    The abstract operations in [OpsAbstract.v] preserve
    [to_list] but not [regular_cad].  Concrete counter-example
    (documented in [kb/plan-catenable.md]):

      cad_push 0 (cad_inject CEmpty 7)
        = CSingle (TOnly [0] CEmpty [7])
        -- pre=1, suf=1, child empty -- violates OT2.

    The repair primitives reshape such results into well-sized
    forms with the same observable sequence.

    ## What this file provides

    - [normalize_only_empty_child]: the simplest repair.  Takes
      [pre] and [suf] of a [TOnly] with empty child; returns a
      well-sized [Cadeque] with the same flattened list.

    - Sequence law connecting [normalize_only_empty_child] to
      simple list concatenation.

    - Well-sizedness theorem: the result satisfies [well_sized_cad].

    ## What's deferred

    - [make_small] for non-empty-child triples.
    - The five repair cases (1a/1b/2a/2b/2c per manual §12.4) for
      red-tail repair.
    - The full operational [cad_*_op] family.

    These are subsequent chunks of Phase 5.6.

    ## Cross-references

    - [Cadeque6/Model.v]            -- types.
    - [Cadeque6/OpsAbstract.v]      -- abstract ops + their seq laws.
    - [Cadeque6/Regularity.v]       -- regular_cad invariant.
    - [Buffer6/SmallMoves.v]        -- buf6_concat and friends.
    - manual §12.4                  -- the five repair cases.
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Color Regularity.

(** ** [normalize_only_empty_child]: trivial reshape for child-empty
    [TOnly] triples that may have both buffers non-empty.

    Given a [pre] and [suf] meant to live in a [TOnly _ CEmpty _],
    produce a well-sized [Cadeque X] with the same flattened
    elements:

    - If both buffers are empty: return [CEmpty].
    - Otherwise: merge them into a single prefix buffer and return
      [CSingle (TOnly merged CEmpty buf6_empty)].

    The result is always well-sized: either [CEmpty] (vacuous) or
    a [TOnly] with [pre = merged > 0] / [suf = empty] / child
    [CEmpty] -- OT2's second branch. *)

Definition normalize_only_empty_child {X : Type}
                                      (pre suf : Buf6 X) : Cadeque X :=
  match buf6_elems pre, buf6_elems suf with
  | [], [] => CEmpty
  | _, _ => CSingle (TOnly (buf6_concat pre suf) CEmpty buf6_empty)
  end.

(** ** Sequence law: flattening the normalized result gives the
    list of [pre]'s elements followed by [suf]'s. *)

(** Helper: flattening a single non-empty merged buffer. *)
Lemma cad_to_list_base_singleton_only_empty :
  forall (X : Type) (xs : list X),
    cad_to_list_base (CSingle (TOnly (mkBuf6 xs) CEmpty buf6_empty))
    = xs.
Proof.
  intros X xs.
  unfold cad_to_list_base. rewrite cad_to_list_single.
  rewrite triple_to_list_only.
  unfold buf6_flatten, buf6_elems.
  rewrite cad_to_list_empty.
  rewrite (flat_concat_singleton_id X xs).
  cbn. rewrite app_nil_r. reflexivity.
Qed.

Lemma normalize_only_empty_child_seq :
  forall (X : Type) (pre suf : Buf6 X),
    cad_to_list_base (normalize_only_empty_child pre suf)
    = buf6_to_list pre ++ buf6_to_list suf.
Proof.
  intros X [pre_xs] [suf_xs].
  unfold normalize_only_empty_child, buf6_elems, buf6_to_list.
  destruct pre_xs as [|p ps]; destruct suf_xs as [|s ss].
  - reflexivity.
  - unfold buf6_concat, buf6_elems.
    rewrite cad_to_list_base_singleton_only_empty.
    reflexivity.
  - unfold buf6_concat, buf6_elems.
    rewrite cad_to_list_base_singleton_only_empty.
    rewrite app_nil_r. reflexivity.
  - unfold buf6_concat, buf6_elems.
    rewrite cad_to_list_base_singleton_only_empty.
    reflexivity.
Qed.

(** ** Well-sizedness: the normalized result is always well-sized. *)

Theorem normalize_only_empty_child_well_sized :
  forall (X : Type) (pre suf : Buf6 X),
    well_sized_cad (normalize_only_empty_child pre suf).
Proof.
  intros X [pre_xs] [suf_xs].
  unfold normalize_only_empty_child, buf6_elems.
  destruct pre_xs as [|p ps]; destruct suf_xs as [|s ss].
  - cbn. exact I.
  - cbn. split; [exact I |].
    right; left.
    unfold buf6_concat, buf6_size, buf6_elems. cbn. lia.
  - cbn. split; [exact I |].
    right; left.
    unfold buf6_concat, buf6_size, buf6_elems. cbn.
    rewrite length_app. cbn. lia.
  - cbn. split; [exact I |].
    right; left.
    unfold buf6_concat, buf6_size, buf6_elems. cbn.
    rewrite length_app. cbn. lia.
Qed.

(** ** Top-level paths green: the normalized result has Green
    top-level paths.

    The result is either [CEmpty] (vacuous) or a [CSingle (TOnly
    merged CEmpty empty)].  In the latter case the triple has
    child [CEmpty], so its [triple_color] is [Green4] by §10.6's
    "child empty -> green" rule.  Its preferred-path tail is
    itself, with colour Green. *)

Theorem normalize_only_empty_child_top_paths_green :
  forall (X : Type) (pre suf : Buf6 X),
    top_level_paths_green (normalize_only_empty_child pre suf).
Proof.
  intros X [pre_xs] [suf_xs].
  unfold normalize_only_empty_child, buf6_elems.
  destruct pre_xs as [|p ps]; destruct suf_xs as [|s ss]; cbn;
    try exact I; reflexivity.
Qed.

(** ** Semiregular: vacuously, since the result has only a
    top-level triple with empty child (no inner structure to
    check). *)

Theorem normalize_only_empty_child_semiregular :
  forall (X : Type) (pre suf : Buf6 X),
    semiregular_cad (normalize_only_empty_child pre suf).
Proof.
  intros X [pre_xs] [suf_xs].
  unfold normalize_only_empty_child, buf6_elems.
  destruct pre_xs as [|p ps]; destruct suf_xs as [|s ss]; cbn;
    try exact I; split; cbn; exact I.
Qed.

(** ** Top-kind discipline: result is either CEmpty or CSingle TOnly. *)

Theorem normalize_only_empty_child_top_kinds :
  forall (X : Type) (pre suf : Buf6 X),
    top_kinds_well_formed (normalize_only_empty_child pre suf).
Proof.
  intros X [pre_xs] [suf_xs].
  unfold normalize_only_empty_child, buf6_elems.
  destruct pre_xs as [|p ps]; destruct suf_xs as [|s ss]; cbn;
    try exact I; reflexivity.
Qed.

(** ** Headline: the normalized result is regular. *)

Theorem normalize_only_empty_child_regular :
  forall (X : Type) (pre suf : Buf6 X),
    regular_cad (normalize_only_empty_child pre suf).
Proof.
  intros X pre suf.
  split; [|split; [|split]].
  - apply normalize_only_empty_child_semiregular.
  - apply normalize_only_empty_child_top_paths_green.
  - apply normalize_only_empty_child_well_sized.
  - apply normalize_only_empty_child_top_kinds.
Qed.
