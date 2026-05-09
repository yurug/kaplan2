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

(** ** Helper: flatten of a TOnly with empty child = pre ++ suf. *)

Lemma cad_to_list_base_TOnly_CEmpty :
  forall (X : Type) (pre suf : Buf6 X),
    cad_to_list_base (CSingle (TOnly pre CEmpty suf))
    = buf6_to_list pre ++ buf6_to_list suf.
Proof.
  intros X [pre_xs] [suf_xs].
  unfold cad_to_list_base, buf6_to_list, buf6_elems.
  rewrite cad_to_list_single, triple_to_list_only.
  unfold buf6_flatten, buf6_elems.
  rewrite cad_to_list_empty.
  rewrite (flat_concat_singleton_id X pre_xs).
  rewrite (flat_concat_singleton_id X suf_xs).
  cbn [app]. reflexivity.
Qed.

(** * [cad_pop_op]: operational pop.

    More complex than push because:
    1. Returns [option] (cadeque might be empty).
    2. Pop can shrink the leftmost outer prefix below the OT
       threshold; the algorithm needs to reshape.
    3. The abstract [cad_pop] returns [None] when [pre] is empty
       even if elements exist in [suf]; the operational version
       must handle that.

    For [CSingle (TOnly pre CEmpty suf)] (the empty-child case),
    we can fully handle pop:
    - try [buf6_pop pre] first;
    - if [pre] is empty, pop the suffix instead;
    - normalize the result into a well-sized shape.

    For other cases (non-empty child, CDouble) the cascade
    primitives are needed; we delegate to abstract [cad_pop].
    Full preservation for those cases awaits the [make_small] /
    cascade work. *)

Definition cad_pop_op {X : Type} (q : Cadeque X) : option (X * Cadeque X) :=
  match q with
  | CEmpty => None
  | CSingle (TOnly pre c suf) =>
      match c with
      | CEmpty =>
          match buf6_pop pre with
          | Some (x, pre') => Some (x, normalize_only_empty_child pre' suf)
          | None =>
              match buf6_pop suf with
              | Some (x, suf') => Some (x, normalize_only_empty_child buf6_empty suf')
              | None => None
              end
          end
      | _ => cad_pop q
      end
  | _ => cad_pop q
  end.

(** ** Sequence law: when [cad_pop_op] returns [Some], the original
    sequence is the popped element followed by the result's sequence. *)

Theorem cad_pop_op_seq :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop_op q = Some (x, q') ->
    cad_to_list_base q = x :: cad_to_list_base q'.
Proof.
  intros X q x q' Hp.
  destruct q as [|t|tL tR].
  - cbn in Hp. discriminate.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + destruct c as [|ct|ctL ctR].
      * (* CSingle (TOnly _ CEmpty _) *)
        cbn [cad_pop_op] in Hp.
        destruct (buf6_pop pre) as [[y pre']|] eqn:Hpre.
        -- (* pop pre succeeded *)
           injection Hp as Hxy Hq'. subst y q'.
           rewrite normalize_only_empty_child_seq.
           apply buf6_pop_seq_some in Hpre.
           rewrite cad_to_list_base_TOnly_CEmpty.
           rewrite Hpre. reflexivity.
        -- (* pop pre failed: pre empty *)
           destruct (buf6_pop suf) as [[y suf']|] eqn:Hsuf.
           ++ injection Hp as Hxy Hq'. subst y q'.
              rewrite normalize_only_empty_child_seq.
              apply buf6_pop_seq_none in Hpre.
              apply buf6_pop_seq_some in Hsuf.
              rewrite cad_to_list_base_TOnly_CEmpty.
              rewrite Hpre, Hsuf. cbn.
              unfold buf6_to_list, buf6_empty, buf6_elems. cbn.
              reflexivity.
           ++ discriminate.
      * (* CSingle ct: delegate *)
        cbn [cad_pop_op] in Hp. apply cad_pop_seq. exact Hp.
      * (* CDouble ctL ctR: delegate *)
        cbn [cad_pop_op] in Hp. apply cad_pop_seq. exact Hp.
    + (* TLeft *)
      cbn [cad_pop_op] in Hp. apply cad_pop_seq. exact Hp.
    + (* TRight *)
      cbn [cad_pop_op] in Hp. apply cad_pop_seq. exact Hp.
  - (* CDouble *)
    cbn [cad_pop_op] in Hp. apply cad_pop_seq. exact Hp.
Qed.

(** ** [cad_eject_op]: operational eject (symmetric to pop).

    Mirror of cad_pop_op for the back end:
    - try buf6_eject suf first;
    - if suf is empty, fall through to buf6_eject pre;
    - normalize_only_empty_child to keep the result well-sized. *)

Definition cad_eject_op {X : Type} (q : Cadeque X)
                      : option (Cadeque X * X) :=
  match q with
  | CEmpty => None
  | CSingle (TOnly pre c suf) =>
      match c with
      | CEmpty =>
          match buf6_eject suf with
          | Some (suf', x) => Some (normalize_only_empty_child pre suf', x)
          | None =>
              match buf6_eject pre with
              | Some (pre', x) => Some (normalize_only_empty_child pre' buf6_empty, x)
              | None => None
              end
          end
      | _ => cad_eject q
      end
  | _ => cad_eject q
  end.

Theorem cad_eject_op_seq :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject_op q = Some (q', x) ->
    cad_to_list_base q = cad_to_list_base q' ++ [x].
Proof.
  intros X q q' x He.
  destruct q as [|t|tL tR].
  - cbn in He. discriminate.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + destruct c as [|ct|ctL ctR].
      * (* CSingle (TOnly _ CEmpty _) *)
        cbn [cad_eject_op] in He.
        destruct (buf6_eject suf) as [[suf' y]|] eqn:Hsuf.
        -- injection He as Hq' Hxy. subst q' y.
           rewrite normalize_only_empty_child_seq.
           apply buf6_eject_seq_some in Hsuf.
           rewrite cad_to_list_base_TOnly_CEmpty.
           rewrite Hsuf. rewrite app_assoc. reflexivity.
        -- destruct (buf6_eject pre) as [[pre' y]|] eqn:Hpre.
           ++ injection He as Hq' Hxy. subst q' y.
              rewrite normalize_only_empty_child_seq.
              apply buf6_eject_seq_none in Hsuf.
              apply buf6_eject_seq_some in Hpre.
              rewrite cad_to_list_base_TOnly_CEmpty.
              rewrite Hpre, Hsuf.
              unfold buf6_to_list, buf6_empty, buf6_elems. cbn [app].
              rewrite app_nil_r, app_nil_r. reflexivity.
           ++ discriminate.
      * cbn [cad_eject_op] in He. apply cad_eject_seq. exact He.
      * cbn [cad_eject_op] in He. apply cad_eject_seq. exact He.
    + cbn [cad_eject_op] in He. apply cad_eject_seq. exact He.
    + cbn [cad_eject_op] in He. apply cad_eject_seq. exact He.
  - cbn [cad_eject_op] in He. apply cad_eject_seq. exact He.
Qed.

(** ** Partial preservation for pop/eject: empty-child case.

    When the input is [CSingle (TOnly pre CEmpty suf)], the
    operational pop/eject's reshape via [normalize_only_empty_child]
    yields a regular result.  Cases with non-empty child or CDouble
    require the cascade machinery (deferred). *)

Theorem cad_pop_op_preserves_regular_TOnly_CEmpty :
  forall (X : Type) (pre suf : Buf6 X) (x : X) (q' : Cadeque X),
    cad_pop_op (CSingle (TOnly pre CEmpty suf)) = Some (x, q') ->
    regular_cad q'.
Proof.
  intros X pre suf x q' Hp.
  cbn [cad_pop_op] in Hp.
  destruct (buf6_pop pre) as [[y pre']|] eqn:Hpre.
  - injection Hp as Hxy Hq'. subst y q'.
    apply normalize_only_empty_child_regular.
  - destruct (buf6_pop suf) as [[y suf']|] eqn:Hsuf.
    + injection Hp as Hxy Hq'. subst y q'.
      apply normalize_only_empty_child_regular.
    + discriminate.
Qed.

Theorem cad_eject_op_preserves_regular_TOnly_CEmpty :
  forall (X : Type) (pre suf : Buf6 X) (x : X) (q' : Cadeque X),
    cad_eject_op (CSingle (TOnly pre CEmpty suf)) = Some (q', x) ->
    regular_cad q'.
Proof.
  intros X pre suf x q' He.
  cbn [cad_eject_op] in He.
  destruct (buf6_eject suf) as [[suf' y]|] eqn:Hsuf.
  - injection He as Hq' Hxy. subst q' y.
    apply normalize_only_empty_child_regular.
  - destruct (buf6_eject pre) as [[pre' y]|] eqn:Hpre.
    + injection He as Hq' Hxy. subst q' y.
      apply normalize_only_empty_child_regular.
    + discriminate.
Qed.

(** ** Sequence-None law for the empty-child cases.

    When the empty-child cad_pop_op returns None, both buffers
    are empty (so the cadeque's flattened sequence is empty too). *)

Theorem cad_pop_op_TOnly_CEmpty_none_iff_buffers_empty :
  forall (X : Type) (pre suf : Buf6 X),
    cad_pop_op (CSingle (TOnly pre CEmpty suf)) = None ->
    buf6_to_list pre = [] /\ buf6_to_list suf = [].
Proof.
  intros X pre suf Hp.
  cbn [cad_pop_op] in Hp.
  destruct (buf6_pop pre) as [[y pre']|] eqn:Hpre; [discriminate|].
  destruct (buf6_pop suf) as [[y suf']|] eqn:Hsuf; [discriminate|].
  apply buf6_pop_seq_none in Hpre.
  apply buf6_pop_seq_none in Hsuf.
  split; assumption.
Qed.

(** * [cad_concat_op]: operational concat with trivial-case
    handling.

    The full operational concat needs all five repair cases per
    manual §12.4 and the [adopt6] shortcut machinery; that is the
    headline pending work for Phase 5.6+.

    For now, [cad_concat_op] handles the trivial cases (one side
    empty) directly and delegates to abstract [cad_concat] for
    the substantive case.  In the trivial cases, the result equals
    the non-empty side, so regularity is inherited. *)

Definition cad_concat_op {X : Type} (a b : Cadeque X) : Cadeque X :=
  match a, b with
  | CEmpty, _ => b
  | _, CEmpty => a
  | _, _ => cad_concat a b
  end.

Theorem cad_concat_op_seq :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_concat_op a b)
    = cad_to_list_base a ++ cad_to_list_base b.
Proof.
  intros X a b. destruct a as [|ta|aL aR]; destruct b as [|tb|bL bR];
    cbn [cad_concat_op]; try (apply cad_concat_seq);
    try (cbn; rewrite ?app_nil_r; reflexivity).
Qed.

Theorem cad_concat_op_refines_cad_concat :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_concat_op a b) = cad_to_list_base (cad_concat a b).
Proof.
  intros X a b. rewrite cad_concat_op_seq, cad_concat_seq. reflexivity.
Qed.

(** ** Trivial-case preservation: when one side is empty, the
    result equals the other side, so regularity is inherited. *)

Theorem cad_concat_op_preserves_regular_left_empty :
  forall (X : Type) (b : Cadeque X),
    regular_cad b ->
    regular_cad (cad_concat_op (@CEmpty X) b).
Proof.
  intros X b Hb. cbn [cad_concat_op]. exact Hb.
Qed.

Theorem cad_concat_op_preserves_regular_right_empty :
  forall (X : Type) (a : Cadeque X),
    regular_cad a ->
    regular_cad (cad_concat_op a (@CEmpty X)).
Proof.
  intros X a Ha. destruct a; cbn [cad_concat_op]; exact Ha.
Qed.

(** * [cad_from_list_op] / [cad_normalize]: rebuild via [cad_push_op].

    [cad_from_list_op xs] folds [cad_push_op] over [xs] starting from
    [CEmpty].  Each push step applies [cad_push_op] which is fully
    regularity-preserving (proven in [cad_push_op_preserves_regular_cad]).
    Hence [cad_from_list_op xs] is regular for any [xs].

    [cad_normalize q := cad_from_list_op (cad_to_list_base q)] takes any
    [Cadeque X] and produces an observably-equal [Cadeque X] that is
    [regular_cad].  This lets us close [regular_cad] preservation for
    operations that would otherwise deliver an irregular result, by
    composing them with [cad_normalize].

    Cost note: [cad_normalize] is [O(n)] in the abstract sequence
    length.  This is acceptable for the abstract-spec layer, which
    targets correctness rather than cost.  Phase 4 (cost bounds) will
    refine to a level-typed cascade with [O(1)] reshape; that
    refinement is a separate enterprise sketched in
    [kb/plan-catenable.md]. *)

Fixpoint cad_from_list_op {X : Type} (xs : list X) : Cadeque X :=
  match xs with
  | []      => CEmpty
  | y :: ys => cad_push_op y (cad_from_list_op ys)
  end.

Lemma cad_from_list_op_seq :
  forall (X : Type) (xs : list X),
    cad_to_list_base (cad_from_list_op xs) = xs.
Proof.
  intros X xs. induction xs as [|y ys IH].
  - reflexivity.
  - cbn [cad_from_list_op].
    rewrite cad_push_op_seq, IH. reflexivity.
Qed.

Lemma cad_from_list_op_regular :
  forall (X : Type) (xs : list X),
    regular_cad (cad_from_list_op xs).
Proof.
  intros X xs. induction xs as [|y ys IH]; cbn.
  - apply regular_cad_empty.
  - apply cad_push_op_preserves_regular_cad. exact IH.
Qed.

Definition cad_normalize {X : Type} (q : Cadeque X) : Cadeque X :=
  cad_from_list_op (cad_to_list_base q).

Lemma cad_normalize_seq :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_normalize q) = cad_to_list_base q.
Proof.
  intros X q. unfold cad_normalize. apply cad_from_list_op_seq.
Qed.

Lemma cad_normalize_regular :
  forall (X : Type) (q : Cadeque X),
    regular_cad (cad_normalize q).
Proof.
  intros X q. unfold cad_normalize. apply cad_from_list_op_regular.
Qed.

(** * [cad_pop_op_full] / [cad_eject_op_full] / [cad_concat_op_full]:
    fully regularity-preserving variants.

    Each composes its underlying op with [cad_normalize] on the
    residue.  Sequence laws are inherited via [cad_normalize_seq];
    full [regular_cad] preservation is by [cad_normalize_regular]. *)

Definition cad_pop_op_full {X : Type} (q : Cadeque X)
                         : option (X * Cadeque X) :=
  match cad_pop_op q with
  | None         => None
  | Some (x, q') => Some (x, cad_normalize q')
  end.

Definition cad_eject_op_full {X : Type} (q : Cadeque X)
                           : option (Cadeque X * X) :=
  match cad_eject_op q with
  | None         => None
  | Some (q', x) => Some (cad_normalize q', x)
  end.

Definition cad_concat_op_full {X : Type} (a b : Cadeque X) : Cadeque X :=
  match a, b with
  | CEmpty, _ => b
  | _, CEmpty => a
  | _, _      => cad_normalize (cad_concat a b)
  end.

(** ** Sequence laws. *)

Theorem cad_pop_op_full_seq :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop_op_full q = Some (x, q') ->
    cad_to_list_base q = x :: cad_to_list_base q'.
Proof.
  intros X q x q' Hp. unfold cad_pop_op_full in Hp.
  destruct (cad_pop_op q) as [[y q'']|] eqn:Hpop; [|discriminate].
  injection Hp as Hxy Hq'. subst y q'.
  rewrite cad_normalize_seq.
  apply (cad_pop_op_seq X q x q''). exact Hpop.
Qed.

Theorem cad_eject_op_full_seq :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject_op_full q = Some (q', x) ->
    cad_to_list_base q = cad_to_list_base q' ++ [x].
Proof.
  intros X q q' x He. unfold cad_eject_op_full in He.
  destruct (cad_eject_op q) as [[q'' y]|] eqn:Hej; [|discriminate].
  injection He as Hq' Hxy. subst q' y.
  rewrite cad_normalize_seq.
  apply (cad_eject_op_seq X q q'' x). exact Hej.
Qed.

Theorem cad_concat_op_full_seq :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_concat_op_full a b)
    = cad_to_list_base a ++ cad_to_list_base b.
Proof.
  intros X a b. unfold cad_concat_op_full.
  destruct a as [|ta|aL aR]; destruct b as [|tb|bL bR];
    try reflexivity;
    try (cbn [cad_to_list_base cad_to_list]; rewrite app_nil_r; reflexivity);
    rewrite cad_normalize_seq, cad_concat_seq; reflexivity.
Qed.

(** ** Full [regular_cad] preservation. *)

Theorem cad_pop_op_full_preserves_regular_cad :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop_op_full q = Some (x, q') ->
    regular_cad q'.
Proof.
  intros X q x q' Hp. unfold cad_pop_op_full in Hp.
  destruct (cad_pop_op q) as [[y q'']|] eqn:Hpop; [|discriminate].
  injection Hp as _ Hq'. subst q'.
  apply cad_normalize_regular.
Qed.

Theorem cad_eject_op_full_preserves_regular_cad :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject_op_full q = Some (q', x) ->
    regular_cad q'.
Proof.
  intros X q q' x He. unfold cad_eject_op_full in He.
  destruct (cad_eject_op q) as [[q'' y]|] eqn:Hej; [|discriminate].
  injection He as Hq' _. subst q'.
  apply cad_normalize_regular.
Qed.

Theorem cad_concat_op_full_preserves_regular_cad :
  forall (X : Type) (a b : Cadeque X),
    regular_cad a ->
    regular_cad b ->
    regular_cad (cad_concat_op_full a b).
Proof.
  intros X a b Ha Hb. unfold cad_concat_op_full.
  destruct a as [|ta|aL aR]; destruct b as [|tb|bL bR];
    try exact Hb; try exact Ha;
    apply cad_normalize_regular.
Qed.

(** ** Refinement: [_full] variants are observationally equivalent to
    the abstract ops at the [cad_to_list_base] level (already given by
    [cad_pop_op_full_seq] etc.).  We do not state a constructor-level
    refinement: [cad_pop_op] and [cad_pop] can disagree on which
    constructor witnesses the [Some] result (different residue
    shape), and the [_full] form additionally normalizes via
    [cad_from_list_op].  Sequence-level equivalence is the relevant
    correctness statement. *)

(** ** Algebra of the [_full] ops.

    A coherent set of laws connecting the [_full] operations with
    [cad_size], the round-trip identities (push/pop, inject/eject),
    associativity / identity for concat, totality on non-empty
    inputs, and the [cad_normalize] idempotence law.

    All proofs reduce to the existing sequence laws plus the abstract
    [cad_*] laws, so the cost is essentially the boilerplate
    plumbing. *)

(** *** Size laws. *)

Lemma cad_normalize_size :
  forall (X : Type) (q : Cadeque X),
    cad_size (cad_normalize q) = cad_size q.
Proof.
  intros X q. unfold cad_size. rewrite cad_normalize_seq. reflexivity.
Qed.

Theorem cad_pop_op_full_size :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop_op_full q = Some (x, q') ->
    cad_size q = S (cad_size q').
Proof.
  intros X q x q' Hp. unfold cad_size.
  apply cad_pop_op_full_seq in Hp.
  rewrite Hp. cbn. reflexivity.
Qed.

Theorem cad_eject_op_full_size :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject_op_full q = Some (q', x) ->
    cad_size q = S (cad_size q').
Proof.
  intros X q q' x He. unfold cad_size.
  apply cad_eject_op_full_seq in He.
  rewrite He, length_app. cbn. lia.
Qed.

Theorem cad_concat_op_full_size :
  forall (X : Type) (a b : Cadeque X),
    cad_size (cad_concat_op_full a b) = cad_size a + cad_size b.
Proof.
  intros X a b. unfold cad_size.
  rewrite cad_concat_op_full_seq, length_app. reflexivity.
Qed.

(** *** Totality on [cad_nonempty] inputs.

    A [cad_nonempty] cadeque admits both [cad_pop_op_full] and
    [cad_eject_op_full]; equivalently, the front and back endpoints
    are observable.  The proof reduces to the abstract totality
    theorems already proven in [Regularity.v].

    The [cad_pop_op] / [cad_eject_op] succeed whenever the abstract
    [cad_pop] / [cad_eject] succeed (the two cases that delegate to
    abstract are clear; the [TOnly + CEmpty] case falls through to
    [buf6_pop] of the prefix, which the [cad_nonempty] precondition
    guarantees succeeds for the prefix half — the [TOnly + CEmpty]
    nonempty case has a nonempty prefix by definition). *)

(** Helper: [cad_pop_op] succeeds whenever [cad_pop] succeeds.

    Proof by case analysis on the cadeque shape.  In four out of
    five branches, [cad_pop_op] delegates to [cad_pop] (the
    [TOnly + non-empty-child], [TLeft], [TRight], and [CDouble]
    cases).  In the [TOnly + CEmpty] case, [cad_pop_op] uses its own
    [buf6_pop pre] dispatch -- which agrees with the abstract
    [cad_pop]'s [triple_pop_prefix] dispatch on the same buffer. *)

Lemma cad_pop_op_succeeds_when_cad_pop_does :
  forall (X : Type) (q : Cadeque X) (x : X) (q'' : Cadeque X),
    cad_pop q = Some (x, q'') ->
    exists q''', cad_pop_op q = Some (x, q''').
Proof.
  intros X q x q'' Hp.
  destruct q as [|t|tL tR].
  - cbn in Hp. discriminate.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + destruct c as [|ct|ctL ctR].
      * (* CSingle (TOnly _ CEmpty _): cad_pop dispatches on
           triple_pop_prefix which dispatches on buf6_pop pre.
           cad_pop_op also dispatches on buf6_pop pre. *)
        cbn [cad_pop triple_pop_prefix] in Hp.
        destruct (buf6_pop pre) as [[y pre']|] eqn:Hpop; [|discriminate].
        injection Hp as Hxy _. subst y.
        cbn [cad_pop_op]. rewrite Hpop. eauto.
      * cbn [cad_pop_op]. rewrite Hp. eauto.
      * cbn [cad_pop_op]. rewrite Hp. eauto.
    + cbn [cad_pop_op]. rewrite Hp. eauto.
    + cbn [cad_pop_op]. rewrite Hp. eauto.
  - cbn [cad_pop_op]. rewrite Hp. eauto.
Qed.

Lemma cad_eject_op_succeeds_when_cad_eject_does :
  forall (X : Type) (q : Cadeque X) (q'' : Cadeque X) (x : X),
    cad_eject q = Some (q'', x) ->
    exists q''', cad_eject_op q = Some (q''', x).
Proof.
  intros X q q'' x He.
  destruct q as [|t|tL tR].
  - cbn in He. discriminate.
  - destruct t as [pre c suf | pre c suf | pre c suf].
    + destruct c as [|ct|ctL ctR].
      * cbn [cad_eject triple_eject_suffix] in He.
        destruct (buf6_eject suf) as [[suf' y]|] eqn:Hej; [|discriminate].
        injection He as _ Hxy. subst y.
        cbn [cad_eject_op]. rewrite Hej. eauto.
      * cbn [cad_eject_op]. rewrite He. eauto.
      * cbn [cad_eject_op]. rewrite He. eauto.
    + cbn [cad_eject_op]. rewrite He. eauto.
    + cbn [cad_eject_op]. rewrite He. eauto.
  - cbn [cad_eject_op]. rewrite He. eauto.
Qed.

Theorem cad_pop_op_full_total_on_nonempty :
  forall (X : Type) (q : Cadeque X),
    cad_nonempty q ->
    exists x q', cad_pop_op_full q = Some (x, q').
Proof.
  intros X q Hq.
  destruct (cad_pop_total_on_nonempty X q Hq) as [x [q'' Hp]].
  destruct (cad_pop_op_succeeds_when_cad_pop_does X q x q'' Hp) as [q''' Hpop].
  unfold cad_pop_op_full. rewrite Hpop. eauto.
Qed.

Theorem cad_eject_op_full_total_on_nonempty :
  forall (X : Type) (q : Cadeque X),
    cad_nonempty q ->
    exists q' x, cad_eject_op_full q = Some (q', x).
Proof.
  intros X q Hq.
  destruct (cad_eject_total_on_nonempty X q Hq) as [q'' [x He]].
  destruct (cad_eject_op_succeeds_when_cad_eject_does X q q'' x He) as [q''' Hej].
  unfold cad_eject_op_full. rewrite Hej. eauto.
Qed.

(** *** Concat algebra at the [cad_to_list_base] level. *)

Theorem cad_concat_op_full_assoc :
  forall (X : Type) (a b c : Cadeque X),
    cad_to_list_base (cad_concat_op_full (cad_concat_op_full a b) c)
    = cad_to_list_base (cad_concat_op_full a (cad_concat_op_full b c)).
Proof.
  intros X a b c.
  rewrite !cad_concat_op_full_seq, app_assoc. reflexivity.
Qed.

Theorem cad_concat_op_full_left_id :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_concat_op_full CEmpty q) = cad_to_list_base q.
Proof.
  intros X q. rewrite cad_concat_op_full_seq. reflexivity.
Qed.

Theorem cad_concat_op_full_right_id :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_concat_op_full q CEmpty) = cad_to_list_base q.
Proof.
  intros X q. rewrite cad_concat_op_full_seq, app_nil_r. reflexivity.
Qed.

(** *** [cad_normalize] is observably idempotent. *)

Theorem cad_normalize_idempotent :
  forall (X : Type) (q : Cadeque X),
    cad_to_list_base (cad_normalize (cad_normalize q))
    = cad_to_list_base (cad_normalize q).
Proof.
  intros X q. rewrite !cad_normalize_seq. reflexivity.
Qed.

Theorem cad_concat_op_full_refines_cad_concat :
  forall (X : Type) (a b : Cadeque X),
    cad_to_list_base (cad_concat_op_full a b) = cad_to_list_base (cad_concat a b).
Proof.
  intros X a b. rewrite cad_concat_op_full_seq, cad_concat_seq. reflexivity.
Qed.

(** *** Pop / Eject refinement (asymmetric).

    [cad_pop_op] is *strictly stronger* than [cad_pop]: it succeeds
    in some shapes where [cad_pop] returns [None] (e.g. when the
    [TOnly + CEmpty] front buffer is empty but the back buffer is
    not).  The refinement is therefore one-directional: whenever
    [cad_pop] succeeds, so does [cad_pop_op] with the same popped
    element and an observably-equal residue. *)

Theorem cad_pop_refines_into_cad_pop_op :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') ->
    exists q'',
      cad_pop_op q = Some (x, q'')
      /\ cad_to_list_base q'' = cad_to_list_base q'.
Proof.
  intros X q x q' Hp.
  destruct (cad_pop_op_succeeds_when_cad_pop_does X q x q' Hp) as [q'' Hpop].
  exists q''. split; [exact Hpop |].
  pose proof (cad_pop_seq X q x q' Hp) as Hseq_abs.
  pose proof (cad_pop_op_seq X q x q'' Hpop) as Hseq_op.
  rewrite Hseq_abs in Hseq_op.
  injection Hseq_op as Heq. exact (eq_sym Heq).
Qed.

Theorem cad_eject_refines_into_cad_eject_op :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) ->
    exists q'',
      cad_eject_op q = Some (q'', x)
      /\ cad_to_list_base q'' = cad_to_list_base q'.
Proof.
  intros X q q' x He.
  destruct (cad_eject_op_succeeds_when_cad_eject_does X q q' x He) as [q'' Hej].
  exists q''. split; [exact Hej |].
  pose proof (cad_eject_seq X q q' x He) as Hseq_abs.
  pose proof (cad_eject_op_seq X q q'' x Hej) as Hseq_op.
  rewrite Hseq_abs in Hseq_op.
  apply app_inj_tail in Hseq_op as [Heq _]. exact (eq_sym Heq).
Qed.

(** *** Sequence-level refinement of the [_full] variants to abstract.

    Whenever the abstract [cad_pop] succeeds, so does
    [cad_pop_op_full] with an observably-equal residue (after
    [cad_normalize]). *)

Theorem cad_pop_refines_into_cad_pop_op_full :
  forall (X : Type) (q : Cadeque X) (x : X) (q' : Cadeque X),
    cad_pop q = Some (x, q') ->
    exists q'',
      cad_pop_op_full q = Some (x, q'')
      /\ cad_to_list_base q'' = cad_to_list_base q'.
Proof.
  intros X q x q' Hp.
  destruct (cad_pop_refines_into_cad_pop_op X q x q' Hp) as [q'' [Hpop Hseq]].
  exists (cad_normalize q''). split.
  - unfold cad_pop_op_full. rewrite Hpop. reflexivity.
  - rewrite cad_normalize_seq. exact Hseq.
Qed.

Theorem cad_eject_refines_into_cad_eject_op_full :
  forall (X : Type) (q : Cadeque X) (q' : Cadeque X) (x : X),
    cad_eject q = Some (q', x) ->
    exists q'',
      cad_eject_op_full q = Some (q'', x)
      /\ cad_to_list_base q'' = cad_to_list_base q'.
Proof.
  intros X q q' x He.
  destruct (cad_eject_refines_into_cad_eject_op X q q' x He) as [q'' [Hej Hseq]].
  exists (cad_normalize q''). split.
  - unfold cad_eject_op_full. rewrite Hej. reflexivity.
  - rewrite cad_normalize_seq. exact Hseq.
Qed.
