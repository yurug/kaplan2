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

(** * [cad_push_op]: operational push.

    Differs from the abstract [cad_push] only when the input is a
    [CSingle (TOnly pre CEmpty suf)] with [pre] empty -- the case
    where naive push would create a TOnly with both buffers
    non-empty under an empty child (violating OT2).  In that case
    we [normalize_only_empty_child] to merge the new element and
    the suffix into a single prefix buffer.

    For all other shapes, the abstract push already preserves
    well-sizedness, so we delegate. *)

Definition cad_push_op {X : Type} (x : X) (q : Cadeque X) : Cadeque X :=
  match q with
  | CEmpty => CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty)
  | CSingle t =>
      match t with
      | TOnly pre c suf =>
          match c with
          | CEmpty =>
              match buf6_elems pre with
              | [] => normalize_only_empty_child (buf6_push x pre) suf
              | _  => CSingle (TOnly (buf6_push x pre) CEmpty suf)
              end
          | _ => CSingle (TOnly (buf6_push x pre) c suf)
          end
      | _ => CSingle (triple_push_prefix x t)
      end
  | CDouble tL tR => CDouble (triple_push_prefix x tL) tR
  end.

(** ** Sequence law: [cad_push_op] prepends [x] to the abstract sequence. *)

Theorem cad_push_op_seq :
  forall (X : Type) (x : X) (q : Cadeque X),
    cad_to_list_base (cad_push_op x q) = x :: cad_to_list_base q.
Proof.
  intros X x q. destruct q as [|t|tL tR].
  - reflexivity.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + (* TOnly *)
      destruct c as [|ct|ctL ctR].
      * (* CEmpty: pivot on pre_xs *)
        destruct pre as [pre_xs]. destruct suf as [suf_xs].
        destruct pre_xs as [|p ps]; cbn [cad_push_op buf6_elems].
        -- (* pre empty: use normalize *)
           rewrite normalize_only_empty_child_seq.
           unfold buf6_to_list, buf6_push, buf6_elems. cbn [app].
           f_equal.
           unfold cad_to_list_base.
           rewrite cad_to_list_single, triple_to_list_only.
           unfold buf6_flatten, buf6_elems.
           rewrite cad_to_list_empty.
           cbn [flat_concat].
           rewrite (flat_concat_singleton_id X suf_xs). reflexivity.
        -- (* pre non-empty: direct match against cad_push_seq *)
           apply (cad_push_seq X x (CSingle
             (TOnly (mkBuf6 (p :: ps)) CEmpty (mkBuf6 suf_xs)))).
      * (* CSingle: same as cad_push *)
        cbn [cad_push_op].
        apply (cad_push_seq X x (CSingle (TOnly pre (CSingle ct) suf))).
      * (* CDouble: same as cad_push *)
        cbn [cad_push_op].
        apply (cad_push_seq X x (CSingle (TOnly pre (CDouble ctL ctR) suf))).
    + (* TLeft *)
      cbn [cad_push_op].
      apply (cad_push_seq X x (CSingle (TLeft pre c suf))).
    + (* TRight *)
      cbn [cad_push_op].
      apply (cad_push_seq X x (CSingle (TRight pre c suf))).
  - (* CDouble *)
    cbn [cad_push_op].
    apply (cad_push_seq X x (CDouble tL tR)).
Qed.

(** ** Preservation: push from CEmpty.

    Trivial: the result is the regular singleton triple. *)

Lemma cad_push_op_preserves_regular_empty :
  forall (X : Type) (x : X),
    regular_cad (cad_push_op x (@CEmpty X)).
Proof.
  intros X x. cbn [cad_push_op]. apply regular_cad_push_to_empty.
Qed.

(** ** Preservation: push when normalize fires.

    [cad_push_op] dispatches to [normalize_only_empty_child] when
    the input is [CSingle (TOnly buf6_empty CEmpty suf)] (pre is
    syntactically empty).  The result is regular by
    [normalize_only_empty_child_regular] -- regardless of the
    input shape, the normalize result is always regular. *)

Lemma cad_push_op_preserves_regular_normalize :
  forall (X : Type) (x : X) (suf : Buf6 X),
    regular_cad (cad_push_op x (CSingle (TOnly buf6_empty CEmpty suf))).
Proof.
  intros X x suf. cbn [cad_push_op buf6_elems buf6_empty].
  apply normalize_only_empty_child_regular.
Qed.

(** ** Preservation of the structural conjuncts (well_sized +
    top_kinds_well_formed) without the harder semantic conjuncts
    (semiregular + top_level_paths_green).

    The structural conjuncts depend only on shape and sizes, not
    on colour or preferred-path behaviour, so they're more
    tractable to prove case-by-case.  The semantic conjuncts
    require colour-shift reasoning and are deferred to a focused
    session.

    We prove preservation for each `cad_push_op` case that
    delegates to the abstract `triple_push_prefix`, plus the
    CDouble case. *)

Lemma cad_push_op_well_sized_when_TOnly_only :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    well_sized_cad (CSingle (TOnly pre c suf)) ->
    (buf6_elems pre <> [] \/ c <> CEmpty) ->
    well_sized_cad (cad_push_op x (CSingle (TOnly pre c suf))).
Proof.
  intros X x [pre_xs] c [suf_xs] Hws Hpre.
  cbn in Hws. destruct Hws as [Hwscad Hws].
  cbn [cad_push_op].
  destruct c as [|ct|tL tR].
  - (* CEmpty: pre must be nonempty per Hpre *)
    destruct Hpre as [Hpre_nonempty | Hcontra]; [|exfalso; apply Hcontra; reflexivity].
    cbn [buf6_elems] in Hpre_nonempty.
    destruct pre_xs as [|p ps]; [contradiction|].
    cbn [buf6_elems].
    cbn. split; [exact Hwscad |].
    (* well_sized_triple new: TOnly with empty child + pre' = (x::p::ps) *)
    cbn in Hws.
    destruct Hws as [[Hp Hs] | [[Hs Hp] | [Hp Hs]]].
    + (* original: pre=0, suf>0 -- but pre_xs = p::ps, so size > 0, contradiction *)
      cbn in Hp. discriminate.
    + (* original: suf=0, pre>0 *)
      right; left.
      unfold buf6_size, buf6_push, buf6_elems. cbn.
      split; [exact Hs | lia].
    + (* original: both >= 5 *)
      right; right.
      unfold buf6_size, buf6_push, buf6_elems. cbn.
      cbn in Hp, Hs. lia.
  - (* CSingle ct: triple has non-empty child, OT1 *)
    cbn. split; [exact Hwscad |].
    cbn in Hws.
    unfold buf6_size, buf6_push, buf6_elems. cbn.
    cbn in Hws. lia.
  - (* CDouble ctL ctR: same OT1 *)
    cbn. split; [exact Hwscad |].
    cbn in Hws.
    unfold buf6_size, buf6_push, buf6_elems. cbn.
    cbn in Hws. lia.
Qed.

Lemma cad_push_op_well_sized_double :
  forall (X : Type) (x : X) (tL tR : Triple X),
    well_sized_cad (CDouble tL tR) ->
    triple_kind tL = KLeft ->
    well_sized_cad (cad_push_op x (CDouble tL tR)).
Proof.
  intros X x tL tR Hws HtL.
  cbn in Hws. destruct Hws as [HwsL HwsR].
  cbn [cad_push_op].
  destruct tL as [pre c suf | pre c suf | pre c suf];
    cbn in HtL; try discriminate.
  cbn in HwsL. destruct HwsL as [Hwscad [Hpre Hsuf]].
  cbn. split; [|exact HwsR].
  cbn. split; [exact Hwscad |].
  cbn. split.
  - unfold buf6_size, buf6_push, buf6_elems in *. cbn in Hpre. cbn. lia.
  - exact Hsuf.
Qed.

Lemma cad_push_op_top_kinds_preserved :
  forall (X : Type) (x : X) (q : Cadeque X),
    top_kinds_well_formed q ->
    top_kinds_well_formed (cad_push_op x q).
Proof.
  intros X x q Htk.
  destruct q as [|t|tL tR]; cbn [cad_push_op].
  - (* CEmpty: result is CSingle (TOnly ...), top_kinds = KOnly. *)
    cbn. reflexivity.
  - (* CSingle t: t must be TOnly per Htk. *)
    cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|tcL tcR].
    + (* CEmpty: dispatch on pre *)
      destruct pre as [pre_xs].
      destruct pre_xs as [|p ps]; cbn [buf6_elems].
      * (* pre empty: normalize -- always returns CEmpty or CSingle TOnly *)
        apply normalize_only_empty_child_top_kinds.
      * (* pre non-empty: CSingle (TOnly _ CEmpty _), kind = KOnly *)
        cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - (* CDouble: tL becomes (push x tL) which preserves kind *)
    cbn in Htk. destruct Htk as [HtL HtR].
    cbn. split; [|exact HtR].
    destruct tL as [pre c suf | pre c suf | pre c suf];
      cbn in HtL; try discriminate;
      cbn; reflexivity.
Qed.

(** * [cad_inject_op]: operational inject (symmetric to push).

    Mirrors [cad_push_op]: differs from the abstract [cad_inject]
    only when input is [CSingle (TOnly pre CEmpty suf)] with [suf]
    empty -- naive inject would create an OT2-violating shape.
    Normalizes by merging into one prefix buffer. *)

Definition cad_inject_op {X : Type} (q : Cadeque X) (x : X) : Cadeque X :=
  match q with
  | CEmpty => CSingle (TOnly buf6_empty CEmpty (buf6_singleton x))
  | CSingle t =>
      match t with
      | TOnly pre c suf =>
          match c with
          | CEmpty =>
              match buf6_elems suf with
              | [] => normalize_only_empty_child pre (buf6_inject suf x)
              | _  => CSingle (TOnly pre CEmpty (buf6_inject suf x))
              end
          | _ => CSingle (TOnly pre c (buf6_inject suf x))
          end
      | _ => CSingle (triple_inject_suffix t x)
      end
  | CDouble tL tR => CDouble tL (triple_inject_suffix tR x)
  end.

(** ** Sequence law: [cad_inject_op] appends [x] to the abstract sequence. *)

Theorem cad_inject_op_seq :
  forall (X : Type) (q : Cadeque X) (x : X),
    cad_to_list_base (cad_inject_op q x) = cad_to_list_base q ++ [x].
Proof.
  intros X q x. destruct q as [|t|tL tR].
  - reflexivity.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + (* TOnly *)
      destruct c as [|ct|ctL ctR].
      * (* CEmpty: pivot on suf_xs *)
        destruct pre as [pre_xs]. destruct suf as [suf_xs].
        destruct suf_xs as [|s ss]; cbn [cad_inject_op buf6_elems].
        -- (* suf empty: use normalize *)
           rewrite normalize_only_empty_child_seq.
           unfold buf6_to_list, buf6_inject, buf6_elems. cbn [app].
           f_equal.
           unfold cad_to_list_base.
           rewrite cad_to_list_single, triple_to_list_only.
           unfold buf6_flatten, buf6_elems.
           rewrite cad_to_list_empty.
           rewrite (flat_concat_singleton_id X pre_xs).
           cbn [flat_concat]. rewrite app_nil_r. reflexivity.
        -- (* suf non-empty: direct match against cad_inject_seq *)
           apply (cad_inject_seq X (CSingle
             (TOnly (mkBuf6 pre_xs) CEmpty (mkBuf6 (s :: ss)))) x).
      * (* CSingle: same as cad_inject *)
        cbn [cad_inject_op].
        apply (cad_inject_seq X (CSingle (TOnly pre (CSingle ct) suf)) x).
      * (* CDouble: same as cad_inject *)
        cbn [cad_inject_op].
        apply (cad_inject_seq X (CSingle (TOnly pre (CDouble ctL ctR) suf)) x).
    + (* TLeft *)
      cbn [cad_inject_op].
      apply (cad_inject_seq X (CSingle (TLeft pre c suf)) x).
    + (* TRight *)
      cbn [cad_inject_op].
      apply (cad_inject_seq X (CSingle (TRight pre c suf)) x).
  - (* CDouble *)
    cbn [cad_inject_op].
    apply (cad_inject_seq X (CDouble tL tR) x).
Qed.

(** ** Preservation: trivial cases.

    Inject from CEmpty: by [regular_cad_inject_to_empty].
    Normalize-fired case: by [normalize_only_empty_child_regular]. *)

Lemma cad_inject_op_preserves_regular_empty :
  forall (X : Type) (x : X),
    regular_cad (cad_inject_op (@CEmpty X) x).
Proof.
  intros X x. cbn [cad_inject_op]. apply regular_cad_inject_to_empty.
Qed.

Lemma cad_inject_op_preserves_regular_normalize :
  forall (X : Type) (pre : Buf6 X) (x : X),
    regular_cad (cad_inject_op (CSingle (TOnly pre CEmpty buf6_empty)) x).
Proof.
  intros X pre x. cbn [cad_inject_op buf6_elems buf6_empty].
  apply normalize_only_empty_child_regular.
Qed.

(** ** Top-kinds preservation: unconditional. *)

Lemma cad_inject_op_top_kinds_preserved :
  forall (X : Type) (q : Cadeque X) (x : X),
    top_kinds_well_formed q ->
    top_kinds_well_formed (cad_inject_op q x).
Proof.
  intros X q x Htk.
  destruct q as [|t|tL tR]; cbn [cad_inject_op].
  - cbn. reflexivity.
  - cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|tcL tcR].
    + destruct suf as [suf_xs].
      destruct suf_xs as [|s ss]; cbn [buf6_elems].
      * apply normalize_only_empty_child_top_kinds.
      * cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
  - cbn in Htk. destruct Htk as [HtL HtR].
    cbn. split; [exact HtL |].
    destruct tR as [pre c suf | pre c suf | pre c suf];
      cbn in HtR; try discriminate;
      cbn; reflexivity.
Qed.

(** * Refinement: operational ops observationally equal abstract ops.

    The operational [cad_push_op] / [cad_inject_op] preserve
    [regular_cad] (under appropriate preconditions, partially
    proven), while the abstract [cad_push] / [cad_inject] preserve
    [to_list] (proven completely in [OpsAbstract.v]).  The
    operational and abstract versions agree at the [to_list]
    level: this is the *refinement* theorem connecting the two
    layers, mirroring Section 4's pattern (where [push_chain]
    is the abstract spec and [exec_push_C] is the cost-bounded
    operational form).

    Once Phase 5.6's full preservation theorem lands, the
    public-facing OCaml extraction will use the operational
    versions, with sequence correctness inherited via these
    refinement theorems. *)

Theorem cad_push_op_refines_cad_push :
  forall (X : Type) (x : X) (q : Cadeque X),
    cad_to_list_base (cad_push_op x q) = cad_to_list_base (cad_push x q).
Proof.
  intros X x q. rewrite cad_push_op_seq, cad_push_seq. reflexivity.
Qed.

Theorem cad_inject_op_refines_cad_inject :
  forall (X : Type) (q : Cadeque X) (x : X),
    cad_to_list_base (cad_inject_op q x) = cad_to_list_base (cad_inject q x).
Proof.
  intros X q x. rewrite cad_inject_op_seq, cad_inject_seq. reflexivity.
Qed.

(** * Top-level-paths-Green preservation for the child-empty cases.

    The simpler half of [top_level_paths_green] preservation: when
    the top triple's child is [CEmpty], the triple's colour is
    Green by §10.6 (regardless of buffer sizes), so the preferred
    path tail is the triple itself, Green.  Push doesn't change
    that the child is empty (push only modifies the prefix), so
    the new triple is also Green-by-empty-child. *)

Lemma cad_push_op_top_paths_green_when_top_child_empty :
  forall (X : Type) (x : X) (pre suf : Buf6 X),
    top_level_paths_green (cad_push_op x (CSingle (TOnly pre CEmpty suf))).
Proof.
  intros X x [pre_xs] suf.
  cbn [cad_push_op buf6_elems].
  destruct pre_xs as [|p ps].
  - (* normalize fires *)
    apply normalize_only_empty_child_top_paths_green.
  - (* direct push: result is CSingle (TOnly nonempty CEmpty suf),
       Green by §10.6 *)
    cbn. reflexivity.
Qed.

Lemma cad_inject_op_top_paths_green_when_top_child_empty :
  forall (X : Type) (pre suf : Buf6 X) (x : X),
    top_level_paths_green (cad_inject_op (CSingle (TOnly pre CEmpty suf)) x).
Proof.
  intros X pre [suf_xs] x.
  cbn [cad_inject_op buf6_elems].
  destruct suf_xs as [|s ss].
  - apply normalize_only_empty_child_top_paths_green.
  - cbn. reflexivity.
Qed.

(** * Top-level-paths-Green preservation for CDouble.

    For [CDouble tL tR], push touches tL only.  By
    [top_kinds_well_formed], tL is a TLeft.  The relevant question
    is whether [preferred_path_tail (push tL)] is Green when
    [preferred_path_tail tL] was Green originally.

    For a TLeft, the preferred-path descent depends on
    [buf6_color pre] (its colour-determining buffer).  Push grows
    pre.  We've already proved (in [Regularity.v]):

    - [preferred_path_tail_TLeft_after_push_green] : when pre size
      ≥ 8 (true Green), the new path tail is Green.

    The general case (pre size 5/6/7) requires the colour-shift
    argument.  That is the next chunk; this lemma handles the
    Green-stays-Green case as a starting point. *)

Lemma cad_push_op_top_paths_green_double_when_top_pre_8 :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (tR : Triple X),
    buf6_size pre >= 8 ->
    triple_color (preferred_path_tail tR) = Green4 ->
    top_level_paths_green (cad_push_op x (CDouble (TLeft pre c suf) tR)).
Proof.
  intros X x pre c suf tR Hpre HR.
  cbn [cad_push_op]. cbn.
  split.
  - apply preferred_path_tail_TLeft_after_push_green. exact Hpre.
  - exact HR.
Qed.

(** * Bundled well_sized preservation for [cad_push_op].

    Combines the per-case structural lemmas plus the trivial CEmpty
    and normalize-fired cases into a single full preservation
    theorem for the [well_sized_cad] conjunct. *)

Theorem cad_push_op_preserves_well_sized :
  forall (X : Type) (x : X) (q : Cadeque X),
    regular_cad q ->
    well_sized_cad (cad_push_op x q).
Proof.
  intros X x q [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - (* CEmpty: trivial *)
    cbn [cad_push_op]. cbn.
    split; [exact I |].
    right; left. cbn. split; [reflexivity | lia].
  - (* CSingle t: t must be TOnly per top_kinds. *)
    cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|ctL ctR].
    + (* CEmpty: dispatch on pre *)
      destruct pre as [pre_xs].
      destruct pre_xs as [|p ps].
      * (* normalize fires *)
        cbn [cad_push_op buf6_elems].
        apply normalize_only_empty_child_well_sized.
      * (* direct push *)
        apply cad_push_op_well_sized_when_TOnly_only.
        -- exact Hws.
        -- left. cbn [buf6_elems]. discriminate.
    + (* CSingle ct: c non-empty *)
      apply cad_push_op_well_sized_when_TOnly_only.
      * exact Hws.
      * right. discriminate.
    + (* CDouble: c non-empty *)
      apply cad_push_op_well_sized_when_TOnly_only.
      * exact Hws.
      * right. discriminate.
  - (* CDouble tL tR *)
    apply cad_push_op_well_sized_double; [exact Hws|].
    cbn in Htk. destruct Htk as [HtL _]. exact HtL.
Qed.

(** ** Bundled top_kinds preservation: already unconditional. *)

Theorem cad_push_op_preserves_top_kinds :
  forall (X : Type) (x : X) (q : Cadeque X),
    regular_cad q ->
    top_kinds_well_formed (cad_push_op x q).
Proof.
  intros X x q [_ [_ [_ Htk]]].
  apply cad_push_op_top_kinds_preserved. exact Htk.
Qed.

(** ** Full preservation of [semiregular_cad] under [cad_push_op].

    Composes: triple_push_prefix_color_monotone_T* (push improves
    colour) with semiregular_local_relax_T* (better colour means
    weaker semiregular_local condition).

    The children of the modified triple are unchanged by push, so
    semiregular_cad of the children is inherited from the input.
    The local check at the modified triple is relaxed since its
    colour improved. *)

(** ** Helper: TOnly with non-empty CSingle child preserves top
    path Green under push at pre-size ≥ 5.

    Per-case proof for the 10 surviving (Hold, Hnew) colour pairs.
    Each case dispatched by one of three patterns:
    - [exact Htop] when path-tail target is the same (Y→Y, O→Y, O→O).
    - [cbn [triple_color]; exact Hnew] when new colour is G
      (target becomes self_new with colour Hnew = G).
    - Discriminate on [Hold] giving R while RC4 demands G
      (R-prefixed cases). *)

Lemma cad_push_op_top_paths_green_TOnly_CSingle :
  forall (X : Type) (x : X) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    top_level_paths_green (CSingle (TOnly pre (CSingle ct) suf)) ->
    top_level_paths_green (CSingle (TOnly (buf6_push x pre) (CSingle ct) suf)).
Proof.
  intros X x pre ct suf Hpre Htop.
  unfold top_level_paths_green in Htop |- *.
  rewrite preferred_path_tail_TOnly_CSingle in Htop.
  rewrite preferred_path_tail_TOnly_CSingle.
  pose proof (triple_push_prefix_color_monotone_TOnly _ x pre (CSingle ct) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color (buf6_push x pre)) (buf6_color suf)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - (* (G, G) *) cbn [triple_color]. exact Hnew.
  - (* (Y, G) *) cbn [triple_color]. exact Hnew.
  - (* (Y, Y) *) exact Htop.
  - (* (O, G) *) cbn [triple_color]. exact Hnew.
  - (* (O, Y) *) exact Htop.
  - (* (O, O) *) exact Htop.
  - (* (R, G) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, Y) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, O) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, R) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

(** ** Same for [TOnly] with [CDouble] child.  The novel case is
    (Orange, Yellow): the path tail switches from [tR] (orange's
    preferred) to [tL] (yellow's preferred).  RC3 says the
    non-preferred (tL) of an Orange triple has Green preferred
    tail -- exactly what's needed. *)

Lemma cad_push_op_top_paths_green_TOnly_CDouble :
  forall (X : Type) (x : X) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    top_level_paths_green (CSingle (TOnly pre (CDouble tL tR) suf)) ->
    semiregular_local (TOnly pre (CDouble tL tR) suf) ->
    top_level_paths_green (CSingle (TOnly (buf6_push x pre) (CDouble tL tR) suf)).
Proof.
  intros X x pre tL tR suf Hpre Htop Hloc.
  unfold top_level_paths_green in Htop |- *.
  rewrite preferred_path_tail_TOnly_CDouble in Htop.
  rewrite preferred_path_tail_TOnly_CDouble.
  pose proof (triple_push_prefix_color_monotone_TOnly _ x pre (CDouble tL tR) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color (buf6_push x pre)) (buf6_color suf)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - (* (G, G) *) cbn [triple_color]. exact Hnew.
  - (* (Y, G) *) cbn [triple_color]. exact Hnew.
  - (* (Y, Y) *) exact Htop.
  - (* (O, G) *) cbn [triple_color]. exact Hnew.
  - (* (O, Y): the orange→yellow shift, needs RC3. *)
    unfold semiregular_local in Hloc.
    cbn [triple_color] in Hloc. rewrite Hold in Hloc. exact Hloc.
  - (* (O, O) *) exact Htop.
  - (* (R, G) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, Y) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, O) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - (* (R, R) *)
    cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

(** ** TOnly path-Green preservation -- triple-level form.

    Same proof as the [cad_push_op_top_paths_green_TOnly_C*] helpers
    but stated at the triple level so they compose into the full
    theorem cleanly. *)

Lemma triple_push_TOnly_CSingle_path_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    triple_color (preferred_path_tail (TOnly pre (CSingle ct) suf)) = Green4 ->
    triple_color (preferred_path_tail (TOnly (buf6_push x pre) (CSingle ct) suf)) = Green4.
Proof.
  intros X x pre ct suf Hpre Htop.
  rewrite preferred_path_tail_TOnly_CSingle in Htop.
  rewrite preferred_path_tail_TOnly_CSingle.
  pose proof (triple_push_prefix_color_monotone_TOnly _ x pre (CSingle ct) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color (buf6_push x pre)) (buf6_color suf)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

Lemma triple_push_TOnly_CDouble_path_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    triple_color (preferred_path_tail (TOnly pre (CDouble tL tR) suf)) = Green4 ->
    semiregular_local (TOnly pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail (TOnly (buf6_push x pre) (CDouble tL tR) suf)) = Green4.
Proof.
  intros X x pre tL tR suf Hpre Htop Hloc.
  rewrite preferred_path_tail_TOnly_CDouble in Htop.
  rewrite preferred_path_tail_TOnly_CDouble.
  pose proof (triple_push_prefix_color_monotone_TOnly _ x pre (CDouble tL tR) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color (buf6_push x pre)) (buf6_color suf)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - unfold semiregular_local in Hloc.
    cbn [triple_color] in Hloc. rewrite Hold in Hloc. exact Hloc.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

(** ** TLeft path-Green preservation under prefix push.

    Same case structure as TOnly but the triple's colour is
    determined by [buf6_color pre] alone (not the meet).  Used in
    the CDouble case of the full theorem (where tL is TLeft per
    top_kinds_well_formed). *)

Lemma triple_push_TLeft_CSingle_path_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    triple_color (preferred_path_tail (TLeft pre (CSingle ct) suf)) = Green4 ->
    triple_color (preferred_path_tail (TLeft (buf6_push x pre) (CSingle ct) suf)) = Green4.
Proof.
  intros X x pre ct suf Hpre Htop.
  rewrite preferred_path_tail_TLeft_CSingle in Htop.
  rewrite preferred_path_tail_TLeft_CSingle.
  pose proof (triple_push_prefix_color_monotone_TLeft _ x pre (CSingle ct) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (buf6_color pre) eqn:Hold;
    destruct (buf6_color (buf6_push x pre)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

Lemma triple_push_TLeft_CDouble_path_green :
  forall (X : Type) (x : X) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    buf6_size pre >= 5 ->
    triple_color (preferred_path_tail (TLeft pre (CDouble tL tR) suf)) = Green4 ->
    semiregular_local (TLeft pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail (TLeft (buf6_push x pre) (CDouble tL tR) suf)) = Green4.
Proof.
  intros X x pre tL tR suf Hpre Htop Hloc.
  rewrite preferred_path_tail_TLeft_CDouble in Htop.
  rewrite preferred_path_tail_TLeft_CDouble.
  pose proof (triple_push_prefix_color_monotone_TLeft _ x pre (CDouble tL tR) suf Hpre) as Hmono.
  cbn [triple_color triple_push_prefix] in Hmono.
  destruct (buf6_color pre) eqn:Hold;
    destruct (buf6_color (buf6_push x pre)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - (* (O, Y): RC3 *)
    unfold semiregular_local in Hloc.
    cbn [triple_color] in Hloc. rewrite Hold in Hloc. exact Hloc.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

(** ** FULL preservation of [top_level_paths_green] under
    [cad_push_op].

    Composes the kind-by-kind triple-level helpers above. *)

Theorem cad_push_op_preserves_top_level_paths_green :
  forall (X : Type) (x : X) (q : Cadeque X),
    regular_cad q ->
    top_level_paths_green (cad_push_op x q).
Proof.
  intros X x q [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - cbn [cad_push_op]. cbn. reflexivity.
  - cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    cbn [cad_push_op].
    destruct c as [|ct|ctL ctR].
    + (* CEmpty child *)
      destruct pre as [pre_xs].
      destruct pre_xs as [|p ps]; cbn [buf6_elems].
      * apply normalize_only_empty_child_top_paths_green.
      * cbn. reflexivity.
    + (* CSingle ct *)
      cbn in Hws. destruct Hws as [_ [Hpre _]].
      cbn. apply triple_push_TOnly_CSingle_path_green; assumption.
    + (* CDouble ctL ctR *)
      cbn in Hws. destruct Hws as [_ [Hpre _]].
      cbn in Hsr. destruct Hsr as [_ Hloc].
      cbn. apply triple_push_TOnly_CDouble_path_green; assumption.
  - (* CDouble tL tR *)
    cbn in Htk. destruct Htk as [HtL HtR].
    cbn [cad_push_op].
    cbn in Htop. destruct Htop as [HtopL HtopR].
    cbn. split; [|exact HtopR].
    destruct tL as [pre c suf | pre c suf | pre c suf];
      cbn in HtL; try discriminate.
    cbn in Hws. destruct Hws as [HwsL _].
    cbn in HwsL. destruct HwsL as [_ [Hpre _]].
    cbn in Hsr. destruct Hsr as [HsrL _].
    cbn in HsrL. destruct HsrL as [_ Hloc].
    destruct c as [|ct|ctL ctR].
    + cbn. reflexivity.
    + apply triple_push_TLeft_CSingle_path_green; assumption.
    + apply triple_push_TLeft_CDouble_path_green; assumption.
Qed.

Theorem cad_push_op_preserves_semiregular :
  forall (X : Type) (x : X) (q : Cadeque X),
    regular_cad q ->
    semiregular_cad (cad_push_op x q).
Proof.
  intros X x q [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - (* CEmpty: cad_push_op produces CSingle (TOnly singleton CEmpty empty),
       which is semiregular trivially (CEmpty child, Green colour). *)
    cbn [cad_push_op]. cbn. split; [exact I | cbn; exact I].
  - (* CSingle t: t is TOnly per top_kinds. *)
    cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|ctL ctR].
    + (* CEmpty child: dispatch on pre *)
      destruct pre as [pre_xs].
      destruct pre_xs as [|p ps]; cbn [cad_push_op buf6_elems].
      * apply normalize_only_empty_child_semiregular.
      * (* Direct push, c=CEmpty: result is CSingle (TOnly _ CEmpty _),
           triple_color = Green by §10.6, semiregular_local True. *)
        cbn. split; [exact I | cbn; exact I].
    + (* Non-empty child CSingle ct: relax + monotone. *)
      cbn [cad_push_op]. cbn.
      cbn in Hsr. destruct Hsr as [Hwc Hloc].
      split; [exact Hwc |].
      cbn in Hws. destruct Hws as [_ [Hpre _]].
      apply (semiregular_local_relax_TOnly _ pre suf
                                            (buf6_push x pre) suf
                                            (CSingle ct)).
      * apply triple_push_prefix_color_monotone_TOnly. exact Hpre.
      * exact Hloc.
    + (* Non-empty child CDouble ctL ctR: same. *)
      cbn [cad_push_op]. cbn.
      cbn in Hsr. destruct Hsr as [Hwc Hloc].
      split; [exact Hwc |].
      cbn in Hws. destruct Hws as [_ [Hpre _]].
      apply (semiregular_local_relax_TOnly _ pre suf
                                            (buf6_push x pre) suf
                                            (CDouble ctL ctR)).
      * apply triple_push_prefix_color_monotone_TOnly. exact Hpre.
      * exact Hloc.
  - (* CDouble tL tR: tL is TLeft per top_kinds, tR unchanged. *)
    cbn in Htk. destruct Htk as [HtL HtR].
    cbn [cad_push_op]. cbn.
    cbn in Hsr. destruct Hsr as [HsrL HsrR].
    split; [|exact HsrR].
    destruct tL as [pre c suf | pre c suf | pre c suf];
      cbn in HtL; try discriminate.
    cbn in HsrL. destruct HsrL as [Hwc Hloc].
    cbn. split; [exact Hwc |].
    cbn in Hws. destruct Hws as [HwsL _].
    cbn in HwsL. destruct HwsL as [_ [Hpre _]].
    apply (semiregular_local_relax_TLeft _ pre suf
                                          (buf6_push x pre) suf c).
    + apply triple_push_prefix_color_monotone_TLeft. exact Hpre.
    + exact Hloc.
Qed.

(** * Headline: full [regular_cad] preservation under [cad_push_op].

    Bundles the four per-conjunct preservation theorems into the
    public-facing statement: cad_push_op preserves regular_cad. *)

Theorem cad_push_op_preserves_regular_cad :
  forall (X : Type) (x : X) (q : Cadeque X),
    regular_cad q ->
    regular_cad (cad_push_op x q).
Proof.
  intros X x q Hreg.
  split; [|split; [|split]].
  - apply cad_push_op_preserves_semiregular. exact Hreg.
  - apply cad_push_op_preserves_top_level_paths_green. exact Hreg.
  - apply cad_push_op_preserves_well_sized. exact Hreg.
  - apply cad_push_op_preserves_top_kinds. exact Hreg.
Qed.

(** * Symmetric bundled preservation for [cad_inject_op]. *)

Lemma cad_inject_op_well_sized_when_TOnly_only :
  forall (X : Type) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (x : X),
    well_sized_cad (CSingle (TOnly pre c suf)) ->
    (buf6_elems suf <> [] \/ c <> CEmpty) ->
    well_sized_cad (cad_inject_op (CSingle (TOnly pre c suf)) x).
Proof.
  intros X [pre_xs] c [suf_xs] x Hws Hsuf.
  cbn in Hws. destruct Hws as [Hwscad Hws].
  cbn [cad_inject_op].
  destruct c as [|ct|tL tR].
  - (* CEmpty: suf must be nonempty per Hsuf *)
    destruct Hsuf as [Hsuf_nonempty | Hcontra]; [|exfalso; apply Hcontra; reflexivity].
    cbn [buf6_elems] in Hsuf_nonempty.
    destruct suf_xs as [|s ss]; [contradiction|].
    cbn [buf6_elems].
    cbn. split; [exact Hwscad |].
    cbn in Hws.
    destruct Hws as [[Hp Hs] | [[Hs Hp] | [Hp Hs]]].
    + (* original: pre=0, suf>0 *)
      left.
      unfold buf6_size, buf6_inject, buf6_elems. cbn.
      split; [exact Hp | rewrite length_app; cbn; lia].
    + (* original: suf=0, pre>0 -- but suf_xs = s::ss, contradiction *)
      cbn in Hs. discriminate.
    + (* original: both >= 5 *)
      right; right.
      unfold buf6_size, buf6_inject, buf6_elems. cbn.
      cbn in Hp, Hs. rewrite length_app; cbn. lia.
  - (* CSingle ct *)
    cbn. split; [exact Hwscad |].
    cbn in Hws.
    unfold buf6_size, buf6_inject, buf6_elems. cbn.
    cbn in Hws. rewrite length_app; cbn. lia.
  - (* CDouble *)
    cbn. split; [exact Hwscad |].
    cbn in Hws.
    unfold buf6_size, buf6_inject, buf6_elems. cbn.
    cbn in Hws. rewrite length_app; cbn. lia.
Qed.

Lemma cad_inject_op_well_sized_double :
  forall (X : Type) (tL tR : Triple X) (x : X),
    well_sized_cad (CDouble tL tR) ->
    triple_kind tR = KRight ->
    well_sized_cad (cad_inject_op (CDouble tL tR) x).
Proof.
  intros X tL tR x Hws HtR.
  cbn in Hws. destruct Hws as [HwsL HwsR].
  cbn [cad_inject_op].
  destruct tR as [pre c suf | pre c suf | pre c suf];
    cbn in HtR; try discriminate.
  cbn in HwsR. destruct HwsR as [Hwscad [Hpre Hsuf]].
  cbn. split; [exact HwsL |].
  cbn. split; [exact Hwscad |].
  cbn. split.
  - exact Hpre.
  - unfold buf6_size, buf6_inject, buf6_elems in *. cbn in Hsuf. cbn.
    rewrite length_app. cbn. lia.
Qed.

Theorem cad_inject_op_preserves_well_sized :
  forall (X : Type) (q : Cadeque X) (x : X),
    regular_cad q ->
    well_sized_cad (cad_inject_op q x).
Proof.
  intros X q x [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - cbn [cad_inject_op]. cbn.
    split; [exact I |].
    left. cbn. split; [reflexivity | lia].
  - cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|ctL ctR].
    + destruct suf as [suf_xs].
      destruct suf_xs as [|s ss].
      * cbn [cad_inject_op buf6_elems].
        apply normalize_only_empty_child_well_sized.
      * apply cad_inject_op_well_sized_when_TOnly_only;
          [exact Hws|].
        left. cbn [buf6_elems]. discriminate.
    + apply cad_inject_op_well_sized_when_TOnly_only;
        [exact Hws|]. right. discriminate.
    + apply cad_inject_op_well_sized_when_TOnly_only;
        [exact Hws|]. right. discriminate.
  - apply cad_inject_op_well_sized_double; [exact Hws|].
    cbn in Htk. destruct Htk as [_ HtR]. exact HtR.
Qed.

Theorem cad_inject_op_preserves_top_kinds :
  forall (X : Type) (q : Cadeque X) (x : X),
    regular_cad q ->
    top_kinds_well_formed (cad_inject_op q x).
Proof.
  intros X q x [_ [_ [_ Htk]]].
  apply cad_inject_op_top_kinds_preserved. exact Htk.
Qed.

(** ** Triple-level path-Green preservation helpers for inject. *)

Lemma triple_inject_TOnly_CSingle_path_green :
  forall (X : Type) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 5 ->
    triple_color (preferred_path_tail (TOnly pre (CSingle ct) suf)) = Green4 ->
    triple_color (preferred_path_tail (TOnly pre (CSingle ct) (buf6_inject suf x))) = Green4.
Proof.
  intros X pre ct suf x Hsuf Htop.
  rewrite preferred_path_tail_TOnly_CSingle in Htop.
  rewrite preferred_path_tail_TOnly_CSingle.
  pose proof (triple_inject_suffix_color_monotone_TOnly _ pre (CSingle ct) suf x Hsuf) as Hmono.
  cbn [triple_color triple_inject_suffix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color pre) (buf6_color (buf6_inject suf x))) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

Lemma triple_inject_TOnly_CDouble_path_green :
  forall (X : Type) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 5 ->
    triple_color (preferred_path_tail (TOnly pre (CDouble tL tR) suf)) = Green4 ->
    semiregular_local (TOnly pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail (TOnly pre (CDouble tL tR) (buf6_inject suf x))) = Green4.
Proof.
  intros X pre tL tR suf x Hsuf Htop Hloc.
  rewrite preferred_path_tail_TOnly_CDouble in Htop.
  rewrite preferred_path_tail_TOnly_CDouble.
  pose proof (triple_inject_suffix_color_monotone_TOnly _ pre (CDouble tL tR) suf x Hsuf) as Hmono.
  cbn [triple_color triple_inject_suffix] in Hmono.
  destruct (color4_meet (buf6_color pre) (buf6_color suf)) eqn:Hold;
    destruct (color4_meet (buf6_color pre) (buf6_color (buf6_inject suf x))) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - unfold semiregular_local in Hloc.
    cbn [triple_color] in Hloc. rewrite Hold in Hloc. exact Hloc.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

Lemma preferred_path_tail_TRight_CSingle :
  forall (X : Type) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    preferred_path_tail (TRight pre (CSingle ct) suf) =
    match buf6_color suf with
    | Green4 | Red4 => TRight pre (CSingle ct) suf
    | _             => preferred_path_tail ct
    end.
Proof. intros. reflexivity. Qed.

Lemma preferred_path_tail_TRight_CDouble :
  forall (X : Type) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X),
    preferred_path_tail (TRight pre (CDouble tL tR) suf) =
    match buf6_color suf with
    | Green4 | Red4 => TRight pre (CDouble tL tR) suf
    | Yellow4       => preferred_path_tail tL
    | Orange4       => preferred_path_tail tR
    end.
Proof. intros. reflexivity. Qed.

Lemma triple_inject_TRight_CSingle_path_green :
  forall (X : Type) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 5 ->
    triple_color (preferred_path_tail (TRight pre (CSingle ct) suf)) = Green4 ->
    triple_color (preferred_path_tail (TRight pre (CSingle ct) (buf6_inject suf x))) = Green4.
Proof.
  intros X pre ct suf x Hsuf Htop.
  rewrite preferred_path_tail_TRight_CSingle in Htop.
  rewrite preferred_path_tail_TRight_CSingle.
  pose proof (triple_inject_suffix_color_monotone_TRight _ pre (CSingle ct) suf x Hsuf) as Hmono.
  cbn [triple_color triple_inject_suffix] in Hmono.
  destruct (buf6_color suf) eqn:Hold;
    destruct (buf6_color (buf6_inject suf x)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

Lemma triple_inject_TRight_CDouble_path_green :
  forall (X : Type) (pre : Buf6 X) (tL tR : Triple X) (suf : Buf6 X) (x : X),
    buf6_size suf >= 5 ->
    triple_color (preferred_path_tail (TRight pre (CDouble tL tR) suf)) = Green4 ->
    semiregular_local (TRight pre (CDouble tL tR) suf) ->
    triple_color (preferred_path_tail (TRight pre (CDouble tL tR) (buf6_inject suf x))) = Green4.
Proof.
  intros X pre tL tR suf x Hsuf Htop Hloc.
  rewrite preferred_path_tail_TRight_CDouble in Htop.
  rewrite preferred_path_tail_TRight_CDouble.
  pose proof (triple_inject_suffix_color_monotone_TRight _ pre (CDouble tL tR) suf x Hsuf) as Hmono.
  cbn [triple_color triple_inject_suffix] in Hmono.
  destruct (buf6_color suf) eqn:Hold;
    destruct (buf6_color (buf6_inject suf x)) eqn:Hnew;
    rewrite ?Hold, ?Hnew in Hmono;
    unfold color4_le, color4_rank in Hmono; cbn in Hmono; try lia;
    cbn match in Htop |- *.
  - cbn [triple_color]. exact Hnew.
  - cbn [triple_color]. exact Hnew.
  - exact Htop.
  - cbn [triple_color]. exact Hnew.
  - unfold semiregular_local in Hloc.
    cbn [triple_color] in Hloc. rewrite Hold in Hloc. exact Hloc.
  - exact Htop.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
  - cbn [triple_color] in Htop. rewrite Hold in Htop. discriminate.
Qed.

(** ** Full inject preservation theorems for the remaining conjuncts. *)

Theorem cad_inject_op_preserves_top_level_paths_green :
  forall (X : Type) (q : Cadeque X) (x : X),
    regular_cad q ->
    top_level_paths_green (cad_inject_op q x).
Proof.
  intros X q x [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - cbn [cad_inject_op]. cbn. reflexivity.
  - cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    cbn [cad_inject_op].
    destruct c as [|ct|ctL ctR].
    + (* CEmpty child *)
      destruct suf as [suf_xs].
      destruct suf_xs as [|s ss]; cbn [buf6_elems].
      * apply normalize_only_empty_child_top_paths_green.
      * cbn. reflexivity.
    + (* CSingle ct *)
      cbn in Hws. destruct Hws as [_ [_ Hsuf]].
      cbn. apply triple_inject_TOnly_CSingle_path_green; assumption.
    + (* CDouble ctL ctR *)
      cbn in Hws. destruct Hws as [_ [_ Hsuf]].
      cbn in Hsr. destruct Hsr as [_ Hloc].
      cbn. apply triple_inject_TOnly_CDouble_path_green; assumption.
  - (* CDouble tL tR *)
    cbn in Htk. destruct Htk as [HtL HtR].
    cbn [cad_inject_op].
    cbn in Htop. destruct Htop as [HtopL HtopR].
    cbn. split; [exact HtopL |].
    destruct tR as [pre c suf | pre c suf | pre c suf];
      cbn in HtR; try discriminate.
    cbn in Hws. destruct Hws as [_ HwsR].
    cbn in HwsR. destruct HwsR as [_ [_ Hsuf]].
    cbn in Hsr. destruct Hsr as [_ HsrR].
    cbn in HsrR. destruct HsrR as [_ Hloc].
    destruct c as [|ct|ctL ctR].
    + cbn. reflexivity.
    + apply triple_inject_TRight_CSingle_path_green; assumption.
    + apply triple_inject_TRight_CDouble_path_green; assumption.
Qed.

Theorem cad_inject_op_preserves_semiregular :
  forall (X : Type) (q : Cadeque X) (x : X),
    regular_cad q ->
    semiregular_cad (cad_inject_op q x).
Proof.
  intros X q x [Hsr [Htop [Hws Htk]]].
  destruct q as [|t|tL tR].
  - cbn [cad_inject_op]. cbn. split; [exact I | cbn; exact I].
  - cbn in Htk.
    destruct t as [pre c suf | pre c suf | pre c suf];
      cbn in Htk; try discriminate.
    destruct c as [|ct|ctL ctR].
    + destruct suf as [suf_xs].
      destruct suf_xs as [|s ss]; cbn [cad_inject_op buf6_elems].
      * apply normalize_only_empty_child_semiregular.
      * cbn. split; [exact I | cbn; exact I].
    + cbn [cad_inject_op]. cbn.
      cbn in Hsr. destruct Hsr as [Hwc Hloc].
      split; [exact Hwc |].
      cbn in Hws. destruct Hws as [_ [_ Hsuf]].
      apply (semiregular_local_relax_TOnly _ pre suf
                                            pre (buf6_inject suf x)
                                            (CSingle ct)).
      * apply triple_inject_suffix_color_monotone_TOnly. exact Hsuf.
      * exact Hloc.
    + cbn [cad_inject_op]. cbn.
      cbn in Hsr. destruct Hsr as [Hwc Hloc].
      split; [exact Hwc |].
      cbn in Hws. destruct Hws as [_ [_ Hsuf]].
      apply (semiregular_local_relax_TOnly _ pre suf
                                            pre (buf6_inject suf x)
                                            (CDouble ctL ctR)).
      * apply triple_inject_suffix_color_monotone_TOnly. exact Hsuf.
      * exact Hloc.
  - cbn in Htk. destruct Htk as [HtL HtR].
    cbn [cad_inject_op]. cbn.
    cbn in Hsr. destruct Hsr as [HsrL HsrR].
    split; [exact HsrL |].
    destruct tR as [pre c suf | pre c suf | pre c suf];
      cbn in HtR; try discriminate.
    cbn in HsrR. destruct HsrR as [Hwc Hloc].
    cbn. split; [exact Hwc |].
    cbn in Hws. destruct Hws as [_ HwsR].
    cbn in HwsR. destruct HwsR as [_ [_ Hsuf]].
    apply (semiregular_local_relax_TRight _ pre suf
                                           pre (buf6_inject suf x) c).
    + apply triple_inject_suffix_color_monotone_TRight. exact Hsuf.
    + exact Hloc.
Qed.

(** * Headline: full [regular_cad] preservation under [cad_inject_op]. *)

Theorem cad_inject_op_preserves_regular_cad :
  forall (X : Type) (q : Cadeque X) (x : X),
    regular_cad q ->
    regular_cad (cad_inject_op q x).
Proof.
  intros X q x Hreg.
  split; [|split; [|split]].
  - apply cad_inject_op_preserves_semiregular. exact Hreg.
  - apply cad_inject_op_preserves_top_level_paths_green. exact Hreg.
  - apply cad_inject_op_preserves_well_sized. exact Hreg.
  - apply cad_inject_op_preserves_top_kinds. exact Hreg.
Qed.
