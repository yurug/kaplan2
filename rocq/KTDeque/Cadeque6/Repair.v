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
