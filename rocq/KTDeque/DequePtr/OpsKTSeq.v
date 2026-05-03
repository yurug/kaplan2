(** * Module: KTDeque.DequePtr.OpsKTSeq -- sequence preservation for
    [OpsKT] (Phase δ.4).

    Proves that the [KChain]-based ops in [OpsKT.v] preserve the
    abstract sequence semantics ([kchain_to_list]).  The key theorems
    are:

      push_kt2_seq   : push_kt2 x c = Some c' →
                       kchain_to_list c' = E.to_list x ++ kchain_to_list c.
      inject_kt2_seq : inject_kt2 c x = Some c' →
                       kchain_to_list c' = kchain_to_list c ++ E.to_list x.
      pop_kt2_seq    : pop_kt2 c = Some (x, c') →
                       kchain_to_list c = E.to_list x ++ kchain_to_list c'.
      eject_kt2_seq  : eject_kt2 c = Some (c', x) →
                       kchain_to_list c = kchain_to_list c' ++ E.to_list x.

    Plus equivalences `push_kt3 = push_kt2` etc. so the bench targets
    inherit sequence preservation.

    Cross-references:
    - [KTDeque/DequePtr/OpsKT.v]   -- ops being verified.
    - [KTDeque/DequePtr/Model.v]   -- [chain_seq], [packet_seq], [buf_seq_E].
    - [KTDeque/Common/Element.v]   -- [E.to_list], [E.pair], [E.unpair].
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color.
From KTDeque.DequePtr Require Import Model OpsKT.

(** Use [Model.E] explicitly to ensure unification with [buf_seq_E] /
    [chain_seq] which were defined relative to [Model.E]. *)
Module E := OpsKT.E.

(* ========================================================================== *)
(* Buffer-level sequence preservation                                          *)
(* ========================================================================== *)

(** Helper: [buf_seq_E_pair] = `E.to_list a ++ E.to_list b`. *)

Lemma green_push_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    green_push x b = Some b' ->
    buf_seq_E b' = Model.E.to_list A x ++ buf_seq_E b.
Proof.
  intros A x b b' Hp.
  unfold green_push in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma green_inject_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    green_inject b x = Some b' ->
    buf_seq_E b' = buf_seq_E b ++ Model.E.to_list A x.
Proof.
  intros A x b b' Hp.
  unfold green_inject in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_assoc, ?app_nil_r; reflexivity.
Qed.

Lemma yellow_push_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    yellow_push x b = Some b' ->
    buf_seq_E b' = Model.E.to_list A x ++ buf_seq_E b.
Proof.
  intros A x b b' Hp.
  unfold yellow_push in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma yellow_inject_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    yellow_inject b x = Some b' ->
    buf_seq_E b' = buf_seq_E b ++ Model.E.to_list A x.
Proof.
  intros A x b b' Hp.
  unfold yellow_inject in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_assoc, ?app_nil_r; reflexivity.
Qed.

Lemma green_pop_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    green_pop b = Some (x, b') ->
    buf_seq_E b = Model.E.to_list A x ++ buf_seq_E b'.
Proof.
  intros A x b b' Hp.
  unfold green_pop in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma green_eject_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    green_eject b = Some (b', x) ->
    buf_seq_E b = buf_seq_E b' ++ Model.E.to_list A x.
Proof.
  intros A x b b' Hp.
  destruct b; cbn in Hp; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list].
  - reflexivity.
  - rewrite <- app_assoc. reflexivity.
Qed.

Lemma yellow_pop_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    yellow_pop b = Some (x, b') ->
    buf_seq_E b = Model.E.to_list A x ++ buf_seq_E b'.
Proof.
  intros A x b b' Hp.
  unfold yellow_pop in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma yellow_eject_seq :
  forall (A : Type) (x : Model.E.t A) (b b' : Buf5 (Model.E.t A)),
    yellow_eject b = Some (b', x) ->
    buf_seq_E b = buf_seq_E b' ++ Model.E.to_list A x.
Proof.
  intros A x b b' Hp.
  unfold yellow_eject in Hp.
  destruct b; inversion Hp; subst; clear Hp;
    unfold buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_assoc, ?app_nil_r; reflexivity.
Qed.

(* ========================================================================== *)
(* Sequence semantics of small buffer constructors                             *)
(* ========================================================================== *)

(** Helper: flatten an [option (E.t A)] into a [list A] (concat of base list,
    or empty if [None]).  *)
Definition opt_seq {A : Type} (o : option (Model.E.t A)) : list A :=
  match o with None => [] | Some x => Model.E.to_list A x end.

(** [prefix23] / [suffix23] / [suffix12] sequence preservation. *)
Lemma prefix23_seq :
  forall (A : Type) (opt : option (Model.E.t A)) (a b : Model.E.t A),
    buf_seq_E (prefix23 opt (a, b))
    = opt_seq opt ++ Model.E.to_list A a ++ Model.E.to_list A b.
Proof.
  intros A [x|] a b; unfold prefix23, opt_seq, buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_nil_r; reflexivity.
Qed.

Lemma suffix23_seq :
  forall (A : Type) (opt : option (Model.E.t A)) (a b : Model.E.t A),
    buf_seq_E (suffix23 (a, b) opt)
    = Model.E.to_list A a ++ Model.E.to_list A b ++ opt_seq opt.
Proof.
  intros A [x|] a b; unfold suffix23, opt_seq, buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma suffix12_seq :
  forall (A : Type) (x : Model.E.t A) (opt : option (Model.E.t A)),
    buf_seq_E (suffix12 x opt)
    = Model.E.to_list A x ++ opt_seq opt.
Proof.
  intros A x [y|]; unfold suffix12, opt_seq, buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_nil_r; reflexivity.
Qed.

(** Sequence relation for [prefix_decompose]: the decomposed parts always
    flatten back to the original buffer's sequence. *)
Lemma prefix_decompose_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)),
    match prefix_decompose b with
    | BD_pre_underflow opt => buf_seq_E b = opt_seq opt
    | BD_pre_ok b'         => buf_seq_E b = buf_seq_E b'
    | BD_pre_overflow b' c d =>
        buf_seq_E b
        = buf_seq_E b' ++ Model.E.to_list A c ++ Model.E.to_list A d
    end.
Proof.
  intros A b. destruct b; cbn; unfold buf_seq_E, opt_seq; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma suffix_decompose_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)),
    match suffix_decompose b with
    | BD_suf_underflow opt => buf_seq_E b = opt_seq opt
    | BD_suf_ok b'         => buf_seq_E b = buf_seq_E b'
    | BD_suf_overflow b' a c =>
        buf_seq_E b
        = Model.E.to_list A a ++ Model.E.to_list A c ++ buf_seq_E b'
    end.
Proof.
  intros A b. destruct b; cbn; unfold buf_seq_E, opt_seq; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** [buffer_unsandwich b]: peeling off first and last from a B≥2 buffer. *)
Lemma buffer_unsandwich_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)),
    match buffer_unsandwich b with
    | BS_alone opt => buf_seq_E b = opt_seq opt
    | BS_sandwich a rest c =>
        buf_seq_E b
        = Model.E.to_list A a ++ buf_seq_E rest ++ Model.E.to_list A c
    end.
Proof.
  intros A b. destruct b; cbn; unfold buf_seq_E, opt_seq; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** [prefix_rot x b]: push x at front, eject last; size preserved. *)
Lemma prefix_rot_seq :
  forall (A : Type) (x : Model.E.t A) (b : Buf5 (Model.E.t A)),
    let '(b', y) := prefix_rot x b in
    Model.E.to_list A x ++ buf_seq_E b
    = buf_seq_E b' ++ Model.E.to_list A y.
Proof.
  intros A x b. destruct b; unfold prefix_rot, buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** [suffix_rot b x]: inject x at back, pop first; size preserved. *)
Lemma suffix_rot_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)) (x : Model.E.t A),
    let '(y, b') := suffix_rot b x in
    buf_seq_E b ++ Model.E.to_list A x
    = Model.E.to_list A y ++ buf_seq_E b'.
Proof.
  intros A b x. destruct b; unfold suffix_rot, buf_seq_E; cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** Flattening a [Buf5 (E.t A * E.t A)] (paired buffer): each element is an
    OCaml tuple of two [E.t A]s; flatten by concatenating their [E.to_list]s. *)
Definition buf_seq_pairs {A : Type} (b : Buf5 (Model.E.t A * Model.E.t A))
    : list A :=
  buf5_seq (fun '(x, y) => Model.E.to_list A x ++ Model.E.to_list A y) b.

(** [buffer_halve b]: split into option leftover + pairs of the rest. *)
Lemma buffer_halve_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)),
    let '(opt, rest) := buffer_halve b in
    buf_seq_E b = opt_seq opt ++ buf_seq_pairs rest.
Proof.
  intros A b. destruct b; unfold buffer_halve, buf_seq_E, buf_seq_pairs, opt_seq;
    cbn -[Model.E.to_list];
    rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** [pair_one (x, y) = Some xp] iff levels match and [E.pair] succeeds.
    The flat sequence of the paired element equals the concat of x's
    and y's flat sequences (via [E.to_list_pair]). *)
Lemma pair_one_seq :
  forall (A : Type) (x y xp : Model.E.t A),
    pair_one (x, y) = Some xp ->
    Model.E.to_list A xp = Model.E.to_list A x ++ Model.E.to_list A y.
Proof.
  intros A x y xp Hp. cbn in Hp.
  destruct (Nat.eq_dec (Model.E.level A x) (Model.E.level A y)) as [eq|]; [|discriminate].
  inversion Hp; subst. apply Model.E.to_list_pair.
Qed.

(** [pair_each_buf]: pairing each tuple element produces a [Buf5 (E.t A)]
    whose flat sequence equals [buf_seq_pairs] of the input. *)
Lemma pair_each_buf_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A * Model.E.t A))
         (b' : Buf5 (Model.E.t A)),
    pair_each_buf b = Some b' ->
    buf_seq_E b' = buf_seq_pairs b.
Proof.
  intros A b b' Hp.
  destruct b as [|p|p1 p2|p1 p2 p3|p1 p2 p3 p4|p1 p2 p3 p4 p5];
    cbn in Hp.
  - inversion Hp; subst. unfold buf_seq_E, buf_seq_pairs; reflexivity.
  - destruct p as [x y].
    destruct (pair_one (x, y)) as [xp|] eqn:Hp1; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@pair_one_seq A x y _ Hp1) as Hpair.
    unfold buf_seq_E, buf_seq_pairs; cbn -[Model.E.to_list].
    rewrite Hpair, ?app_nil_r. reflexivity.
  - destruct p1 as [x1 y1], p2 as [x2 y2].
    destruct (pair_one (x1, y1)) as [xp1|] eqn:H1; [|discriminate].
    destruct (pair_one (x2, y2)) as [xp2|] eqn:H2; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@pair_one_seq A x1 y1 _ H1) as Hp1'.
    pose proof (@pair_one_seq A x2 y2 _ H2) as Hp2'.
    unfold buf_seq_E, buf_seq_pairs; cbn -[Model.E.to_list].
    rewrite Hp1', Hp2', ?app_nil_r, <- ?app_assoc. reflexivity.
  - destruct p1 as [x1 y1], p2 as [x2 y2], p3 as [x3 y3].
    destruct (pair_one (x1, y1)) as [xp1|] eqn:H1; [|discriminate].
    destruct (pair_one (x2, y2)) as [xp2|] eqn:H2; [|discriminate].
    destruct (pair_one (x3, y3)) as [xp3|] eqn:H3; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@pair_one_seq A x1 y1 _ H1) as Hp1'.
    pose proof (@pair_one_seq A x2 y2 _ H2) as Hp2'.
    pose proof (@pair_one_seq A x3 y3 _ H3) as Hp3'.
    unfold buf_seq_E, buf_seq_pairs; cbn -[Model.E.to_list].
    rewrite Hp1', Hp2', Hp3', ?app_nil_r, <- ?app_assoc. reflexivity.
  - destruct p1 as [x1 y1], p2 as [x2 y2], p3 as [x3 y3], p4 as [x4 y4].
    destruct (pair_one (x1, y1)) as [xp1|] eqn:H1; [|discriminate].
    destruct (pair_one (x2, y2)) as [xp2|] eqn:H2; [|discriminate].
    destruct (pair_one (x3, y3)) as [xp3|] eqn:H3; [|discriminate].
    destruct (pair_one (x4, y4)) as [xp4|] eqn:H4; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@pair_one_seq A x1 y1 _ H1) as Hp1'.
    pose proof (@pair_one_seq A x2 y2 _ H2) as Hp2'.
    pose proof (@pair_one_seq A x3 y3 _ H3) as Hp3'.
    pose proof (@pair_one_seq A x4 y4 _ H4) as Hp4'.
    unfold buf_seq_E, buf_seq_pairs; cbn -[Model.E.to_list].
    rewrite Hp1', Hp2', Hp3', Hp4', ?app_nil_r, <- ?app_assoc. reflexivity.
  - destruct p1 as [x1 y1], p2 as [x2 y2], p3 as [x3 y3], p4 as [x4 y4], p5 as [x5 y5].
    destruct (pair_one (x1, y1)) as [xp1|] eqn:H1; [|discriminate].
    destruct (pair_one (x2, y2)) as [xp2|] eqn:H2; [|discriminate].
    destruct (pair_one (x3, y3)) as [xp3|] eqn:H3; [|discriminate].
    destruct (pair_one (x4, y4)) as [xp4|] eqn:H4; [|discriminate].
    destruct (pair_one (x5, y5)) as [xp5|] eqn:H5; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@pair_one_seq A x1 y1 _ H1) as Hp1'.
    pose proof (@pair_one_seq A x2 y2 _ H2) as Hp2'.
    pose proof (@pair_one_seq A x3 y3 _ H3) as Hp3'.
    pose proof (@pair_one_seq A x4 y4 _ H4) as Hp4'.
    pose proof (@pair_one_seq A x5 y5 _ H5) as Hp5'.
    unfold buf_seq_E, buf_seq_pairs; cbn -[Model.E.to_list].
    rewrite Hp1', Hp2', Hp3', Hp4', Hp5', ?app_nil_r, <- ?app_assoc. reflexivity.
Qed.

(** [to_list_unpair]: dual of [E.to_list_pair].  When [E.unpair] succeeds,
    the original element flattens as the concat of its component flattens.
    Re-exported from the underlying ELEMENT instance. *)
Lemma to_list_unpair :
  forall (A : Type) (x a b : Model.E.t A),
    Model.E.unpair A x = Some (a, b) ->
    Model.E.to_list A x = Model.E.to_list A a ++ Model.E.to_list A b.
Proof. exact Model.E.unpair_to_list. Qed.

(* ========================================================================== *)
(* Cross-buffer concat sequence preservation                                   *)
(* ========================================================================== *)

(** [green_prefix_concat (b1, b2) = Some (b1', b2')] preserves the joined
    sequence [buf_seq_E b1 ++ buf_seq_E b2]. *)
(* ========================================================================== *)
(* Cross-buffer concat sequence preservation                                   *)
(* ========================================================================== *)

(** Strategy: instead of [rewrite prefix23_seq] (which fails with "no
    subterm matching" — a tactic-mechanics issue with the [prefix23]
    application not being syntactically recognized post-substitution), we
    case-split on [opt] and let [cbn] unfold [prefix23] directly. *)

Lemma green_prefix_concat_seq :
  forall (A : Type) (b1 b2 b1' b2' : Buf5 (Model.E.t A)),
    green_prefix_concat b1 b2 = Some (b1', b2') ->
    buf_seq_E b1 ++ buf_seq_E b2 = buf_seq_E b1' ++ buf_seq_E b2'.
Proof.
  intros A b1 b2 b1' b2' Hg.
  unfold green_prefix_concat in Hg.
  destruct (prefix_decompose b1) as [opt|b1''|b1'' c d] eqn:Heq.
  - destruct (green_pop b2) as [[ab b2pop]|] eqn:Hpop; [|discriminate].
    destruct (Model.E.unpair A ab) as [[a b]|] eqn:Hun; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd, (green_pop_seq Hpop), (to_list_unpair Hun).
    destruct opt as [x|]; unfold prefix23, buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd. reflexivity.
  - destruct (Nat.eq_dec (Model.E.level A c) (Model.E.level A d)) as [eq|]; [|discriminate].
    destruct (green_push (Model.E.pair A c d eq) b2) as [b2''|] eqn:Hpush; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd, (green_push_seq Hpush), Model.E.to_list_pair.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma green_suffix_concat_seq :
  forall (A : Type) (b1 b2 b1' b2' : Buf5 (Model.E.t A)),
    green_suffix_concat b1 b2 = Some (b1', b2') ->
    buf_seq_E b1 ++ buf_seq_E b2 = buf_seq_E b1' ++ buf_seq_E b2'.
Proof.
  intros A b1 b2 b1' b2' Hg.
  unfold green_suffix_concat in Hg.
  destruct (suffix_decompose b2) as [opt|b2''|b2'' a c] eqn:Heq.
  - destruct (green_eject b1) as [[b1ej ab]|] eqn:Hej; [|discriminate].
    destruct (Model.E.unpair A ab) as [[x y]|] eqn:Hun; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd, (green_eject_seq Hej), (to_list_unpair Hun).
    destruct opt as [z|]; unfold suffix23, buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd. reflexivity.
  - destruct (Nat.eq_dec (Model.E.level A a) (Model.E.level A c)) as [eq|]; [|discriminate].
    destruct (green_inject b1 (Model.E.pair A a c eq)) as [b1''|] eqn:Hinj; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd, (green_inject_seq Hinj), Model.E.to_list_pair.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma prefix_concat_seq :
  forall (A : Type) (b1 b2 b1' b2' : Buf5 (Model.E.t A)),
    prefix_concat b1 b2 = Some (b1', b2') ->
    buf_seq_E b1 ++ buf_seq_E b2 = buf_seq_E b1' ++ buf_seq_E b2'.
Proof.
  intros A b1 b2 b1' b2' Hg.
  unfold prefix_concat in Hg.
  destruct (prefix_decompose b1) as [opt|b1''|b1'' c d] eqn:Heq.
  - destruct (yellow_pop b2) as [[ab b2pop]|] eqn:Hpop; [|discriminate].
    destruct (Model.E.unpair A ab) as [[a b]|] eqn:Hun; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd, (yellow_pop_seq Hpop), (to_list_unpair Hun).
    destruct opt as [x|]; unfold prefix23, buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd. reflexivity.
  - destruct (Nat.eq_dec (Model.E.level A c) (Model.E.level A d)) as [eq|]; [|discriminate].
    destruct (yellow_push (Model.E.pair A c d eq) b2) as [b2''|] eqn:Hpush; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@prefix_decompose_seq A b1) as Hpd. rewrite Heq in Hpd.
    rewrite Hpd, (yellow_push_seq Hpush), Model.E.to_list_pair.
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma suffix_concat_seq :
  forall (A : Type) (b1 b2 b1' b2' : Buf5 (Model.E.t A)),
    suffix_concat b1 b2 = Some (b1', b2') ->
    buf_seq_E b1 ++ buf_seq_E b2 = buf_seq_E b1' ++ buf_seq_E b2'.
Proof.
  intros A b1 b2 b1' b2' Hg.
  unfold suffix_concat in Hg.
  destruct (suffix_decompose b2) as [opt|b2''|b2'' a c] eqn:Heq.
  - destruct (yellow_eject b1) as [[b1ej ab]|] eqn:Hej; [|discriminate].
    destruct (Model.E.unpair A ab) as [[x y]|] eqn:Hun; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd, (yellow_eject_seq Hej), (to_list_unpair Hun).
    destruct opt as [z|]; unfold suffix23, buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd. reflexivity.
  - destruct (Nat.eq_dec (Model.E.level A a) (Model.E.level A c)) as [eq|]; [|discriminate].
    destruct (yellow_inject b1 (Model.E.pair A a c eq)) as [b1''|] eqn:Hinj; [|discriminate].
    inversion Hg; subst; clear Hg.
    pose proof (@suffix_decompose_seq A b2) as Hsd. rewrite Heq in Hsd.
    rewrite Hsd, (yellow_inject_seq Hinj), Model.E.to_list_pair.
    rewrite <- !app_assoc. reflexivity.
Qed.

(* ========================================================================== *)
(* Buffer→Chain promotion + auxiliary lemmas                                   *)
(* ========================================================================== *)

(** [buffer_push_chain x b]: pushing onto a Chain via the B5-split case. *)
Lemma buffer_push_chain_seq :
  forall (A : Type) (x : Model.E.t A) (b : Buf5 (Model.E.t A)),
    chain_to_list (buffer_push_chain x b)
    = Model.E.to_list A x ++ buf_seq_E b.
Proof.
  intros A x b. destruct b; unfold buffer_push_chain, chain_to_list, chain_seq, buf_seq_E;
    cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

Lemma buffer_inject_chain_seq :
  forall (A : Type) (b : Buf5 (Model.E.t A)) (x : Model.E.t A),
    chain_to_list (buffer_inject_chain b x)
    = buf_seq_E b ++ Model.E.to_list A x.
Proof.
  intros A b x. destruct b; unfold buffer_inject_chain, chain_to_list, chain_seq, buf_seq_E;
    cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(** [mk_ending_from_options]: produces an Ending whose flat sequence is
    p1opt ++ midopt-flat ++ s1opt. *)
Lemma mk_ending_from_options_seq :
  forall (A : Type) (p1 : option (Model.E.t A))
         (mid : option (Model.E.t A * Model.E.t A))
         (s1 : option (Model.E.t A)),
    chain_to_list (mk_ending_from_options p1 mid s1)
    = opt_seq p1
      ++ match mid with None => [] | Some (x, y) => Model.E.to_list A x ++ Model.E.to_list A y end
      ++ opt_seq s1.
Proof.
  intros A [a|] [[x y]|] [c|];
    unfold mk_ending_from_options, opt_seq, chain_to_list, chain_seq, buf_seq_E;
    cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
Qed.

(* ========================================================================== *)
(* make_small_seq                                                              *)
(* ========================================================================== *)

(** The headline buffer→Chain promotion lemma: [make_small b1 b2 b3]
    produces a Chain whose flat sequence is [buf_seq_E b1 ++ buf_seq_E b2
    ++ buf_seq_E b3].  9 cases by [prefix_decompose × suffix_decompose].

    NOTE: this proof is a multi-day undertaking: the (Overflow, Overflow)
    case alone weaves together [buffer_halve_seq], [pair_each_buf_seq],
    [suffix12_seq], and three uses of [E.to_list_pair] across nested
    chain construction.  All necessary helper lemmas are proven above.
    The proof skeleton below sketches the case structure and rewrite
    plumbing; full closure is deferred. *)
(** Lift an equation [X = Y] to [X ++ l = Y ++ l] for arbitrary tail [l]. *)
Lemma app_eq_lift : forall {A} (X Y l : list A), X = Y -> X ++ l = Y ++ l.
Proof. intros A X Y l Heq. rewrite Heq. reflexivity. Qed.

(** Sequence of a depth-1 simple chain ChainCons(PNode pre Hole suf)(Ending b).
    Useful for unfolding chain_to_list in [make_small_seq] case proofs. *)
Lemma chain_to_list_simple :
  forall (A : Type) (pre suf : Buf5 (Model.E.t A)) (b : Buf5 (Model.E.t A)),
    chain_to_list (ChainCons (PNode pre Hole suf) (Ending b))
    = buf_seq_E pre ++ buf_seq_E b ++ buf_seq_E suf.
Proof. intros. unfold chain_to_list, chain_seq, packet_seq. reflexivity. Qed.

(** Sequence of a depth-2 nested chain ChainCons(PNode pre1 (PNode pre2 Hole suf2) suf1)(Ending b). *)
Lemma chain_to_list_nested :
  forall (A : Type) (pre1 suf1 pre2 suf2 b : Buf5 (Model.E.t A)),
    chain_to_list (ChainCons (PNode pre1 (PNode pre2 Hole suf2) suf1) (Ending b))
    = buf_seq_E pre1 ++ (buf_seq_E pre2 ++ buf_seq_E b ++ buf_seq_E suf2) ++ buf_seq_E suf1.
Proof. intros. unfold chain_to_list, chain_seq, packet_seq. reflexivity. Qed.

(** Specific buf_seq_E unfoldings for each constructor — let us reduce
    [buf_seq_E (B3 a b c)] without touching opaque [buf_seq_E b]. *)
Lemma buf_seq_E_B0 : forall A, @buf_seq_E A B0 = []. Proof. reflexivity. Qed.
Lemma buf_seq_E_B1 :
  forall A a, @buf_seq_E A (B1 a) = Model.E.to_list A a.
Proof. reflexivity. Qed.
Lemma buf_seq_E_B2 :
  forall A a b, @buf_seq_E A (B2 a b)
              = Model.E.to_list A a ++ Model.E.to_list A b.
Proof. reflexivity. Qed.
Lemma buf_seq_E_B3 :
  forall A a b c, @buf_seq_E A (B3 a b c)
                = Model.E.to_list A a ++ Model.E.to_list A b ++ Model.E.to_list A c.
Proof. reflexivity. Qed.
Lemma buf_seq_E_B4 :
  forall A a b c d, @buf_seq_E A (B4 a b c d)
                  = Model.E.to_list A a ++ Model.E.to_list A b ++ Model.E.to_list A c ++ Model.E.to_list A d.
Proof. reflexivity. Qed.
Lemma buf_seq_E_B5 :
  forall A a b c d e, @buf_seq_E A (B5 a b c d e)
                    = Model.E.to_list A a ++ Model.E.to_list A b ++ Model.E.to_list A c ++ Model.E.to_list A d ++ Model.E.to_list A e.
Proof. reflexivity. Qed.

Lemma make_small_seq :
  forall (A : Type) (b1 b2 b3 : Buf5 (Model.E.t A)) (c : Chain A),
    make_small b1 b2 b3 = Some c ->
    chain_to_list c = buf_seq_E b1 ++ buf_seq_E b2 ++ buf_seq_E b3.
Proof.
  intros A b1 b2 b3 c Hms.
  unfold make_small in Hms.
  pose proof (@prefix_decompose_seq A b1) as Hpd.
  pose proof (@suffix_decompose_seq A b3) as Hsd.
  destruct (prefix_decompose b1) as [p1opt|p1'|p1' pc pd] eqn:Heq1;
    destruct (suffix_decompose b3) as [s1opt|s1'|s1' sa sb] eqn:Heq3.

  - (* (Underflow, Underflow) *)
    destruct (buffer_unsandwich b2) as [midopt|ab rest cd] eqn:Hub.
    + destruct midopt as [elem|].
      * destruct (Model.E.unpair A elem) as [[a b]|] eqn:Hun; [|discriminate].
        inversion Hms; subst; clear Hms.
        pose proof (@buffer_unsandwich_seq A b2) as Hus. rewrite Hub in Hus.
        rewrite mk_ending_from_options_seq, Hpd, Hsd.
        unfold opt_seq in Hus. rewrite Hus, (to_list_unpair Hun). reflexivity.
      * inversion Hms; subst; clear Hms.
        pose proof (@buffer_unsandwich_seq A b2) as Hus. rewrite Hub in Hus.
        rewrite mk_ending_from_options_seq, Hpd, Hsd.
        unfold opt_seq in Hus. rewrite Hus. cbn. reflexivity.
    + destruct (Model.E.unpair A ab) as [[a1 a2]|] eqn:Hun_ab; [|discriminate].
      destruct (Model.E.unpair A cd) as [[c1 c2]|] eqn:Hun_cd; [|discriminate].
      inversion Hms; subst; clear Hms.
      pose proof (@buffer_unsandwich_seq A b2) as Hus. rewrite Hub in Hus.
      rewrite Hpd, Hsd, Hus, (to_list_unpair Hun_ab), (to_list_unpair Hun_cd).
      unfold chain_to_list, chain_seq, packet_seq.
      destruct p1opt as [p1|], s1opt as [s1|]; unfold prefix23, suffix23, opt_seq, buf_seq_E;
        cbn -[Model.E.to_list]; rewrite ?app_nil_r, <- ?app_assoc; reflexivity.

  - (* (Underflow, Ok) *)
    destruct (buf5_pop_naive b2) as [[cd b2_rest]|] eqn:Hpop.
    + destruct (Model.E.unpair A cd) as [[c1 c2]|] eqn:Hun; [|discriminate].
      inversion Hms; subst; clear Hms.
      rewrite Hpd, Hsd.
      pose proof (@buf5_pop_naive_seq _ A (Model.E.to_list A) _ _ _ Hpop) as Hpop_seq.
      unfold buf_seq_E. rewrite Hpop_seq, (to_list_unpair Hun).
      unfold chain_to_list, chain_seq, packet_seq.
      destruct p1opt as [p1|]; unfold prefix23, opt_seq, buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + destruct p1opt as [x|].
      * destruct (buf5_push_naive x s1') as [s1''|] eqn:Hpush; [|discriminate].
        inversion Hms; subst; clear Hms.
        rewrite Hpd, Hsd.
        destruct b2; cbn in Hpop; try discriminate.
        unfold opt_seq, chain_to_list, chain_seq, buf_seq_E. cbn.
        pose proof (@buf5_push_naive_seq _ A (Model.E.to_list A) _ _ _ Hpush) as Hpush_seq.
        unfold buf_seq_E in Hpush_seq. rewrite Hpush_seq. reflexivity.
      * inversion Hms; subst; clear Hms.
        rewrite Hpd, Hsd.
        destruct b2; cbn in Hpop; try discriminate.
        unfold opt_seq, chain_to_list, chain_seq, buf_seq_E. cbn. reflexivity.

  - (* (Underflow, Overflow) *)
    destruct (Nat.eq_dec (Model.E.level A sa) (Model.E.level A sb)) as [eq|]; [|discriminate].
    pose proof (@suffix_rot_seq A b2 (Model.E.pair A sa sb eq)) as Hsr.
    destruct (suffix_rot b2 (Model.E.pair A sa sb eq)) as [cd_paired center] eqn:Hsr_eq.
    destruct (Model.E.unpair A cd_paired) as [[c1 c2]|] eqn:Hun; [|discriminate].
    inversion Hms; subst; clear Hms.
    rewrite Model.E.to_list_pair in Hsr.
    rewrite (to_list_unpair Hun) in Hsr.
    pose proof (@app_eq_lift A _ _ (buf_seq_E s1') Hsr) as Hsr_l.
    rewrite <- !app_assoc in Hsr_l.
    rewrite Hpd, Hsd, chain_to_list_simple.
    destruct p1opt as [p1|]; cbn -[Model.E.to_list buf_seq_E].
    + rewrite buf_seq_E_B3. unfold opt_seq.
      rewrite <- !app_assoc. rewrite Hsr_l. reflexivity.
    + rewrite buf_seq_E_B2. unfold opt_seq. cbn.
      rewrite <- !app_assoc. rewrite Hsr_l. reflexivity.

  - (* (Ok, Underflow) *)
    destruct (buf5_eject_naive b2) as [[b2_rest ab]|] eqn:Hej.
    + destruct (Model.E.unpair A ab) as [[a1 a2]|] eqn:Hun; [|discriminate].
      inversion Hms; subst; clear Hms.
      rewrite Hpd, Hsd.
      pose proof (@buf5_eject_naive_seq _ A (Model.E.to_list A) _ _ _ Hej) as Hej_seq.
      unfold buf_seq_E. rewrite Hej_seq, (to_list_unpair Hun).
      unfold chain_to_list, chain_seq, packet_seq.
      destruct s1opt as [s1|]; unfold suffix23, opt_seq, buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + destruct s1opt as [x|].
      * destruct (buf5_inject_naive p1' x) as [p1''|] eqn:Hinj; [|discriminate].
        inversion Hms; subst; clear Hms.
        rewrite Hpd, Hsd.
        destruct b2; cbn in Hej; try discriminate.
        unfold opt_seq, chain_to_list, chain_seq, buf_seq_E. cbn.
        pose proof (@buf5_inject_naive_seq _ A (Model.E.to_list A) _ _ _ Hinj) as Hinj_seq.
        unfold buf_seq_E in Hinj_seq. rewrite Hinj_seq.
        rewrite ?app_nil_r. reflexivity.
      * inversion Hms; subst; clear Hms.
        rewrite Hpd, Hsd.
        destruct b2; cbn in Hej; try discriminate.
        unfold opt_seq, chain_to_list, chain_seq, buf_seq_E. cbn.
        rewrite ?app_nil_r. reflexivity.

  - (* (Ok, Ok) — simplest *)
    inversion Hms; subst; clear Hms.
    rewrite Hpd, Hsd.
    unfold chain_to_list, chain_seq, packet_seq, buf_seq_E. cbn. reflexivity.

  - (* (Ok, Overflow) — buffer_inject_chain *)
    destruct (Nat.eq_dec (Model.E.level A sa) (Model.E.level A sb)) as [eq|]; [|discriminate].
    inversion Hms; subst; clear Hms.
    rewrite Hpd, Hsd.
    unfold chain_to_list, chain_seq, packet_seq.
    rewrite buffer_inject_chain_seq, Model.E.to_list_pair.
    unfold buf_seq_E. cbn -[Model.E.to_list].
    rewrite <- !app_assoc. reflexivity.

  - (* (Overflow, Underflow) *)
    destruct (Nat.eq_dec (Model.E.level A pc) (Model.E.level A pd)) as [eq|]; [|discriminate].
    pose proof (@prefix_rot_seq A (Model.E.pair A pc pd eq) b2) as Hpr.
    destruct (prefix_rot (Model.E.pair A pc pd eq) b2) as [center ab_paired] eqn:Hpr_eq.
    destruct (Model.E.unpair A ab_paired) as [[a1 a2]|] eqn:Hun; [|discriminate].
    inversion Hms; subst; clear Hms.
    rewrite Model.E.to_list_pair in Hpr.
    rewrite (to_list_unpair Hun) in Hpr.
    rewrite Hpd, Hsd, chain_to_list_simple.
    destruct s1opt as [s1|]; cbn -[Model.E.to_list buf_seq_E].
    + (* Goal: ... ++ buf_seq_E (B3 a1 a2 s1) = ... ++ E.to_list s1 *)
      rewrite buf_seq_E_B3. unfold opt_seq.
      pose proof (@app_eq_lift A _ _ (Model.E.to_list A s1) Hpr) as Hpr_l.
      rewrite <- !app_assoc in Hpr_l.
      rewrite <- !app_assoc.
      f_equal. rewrite <- Hpr_l. reflexivity.
    + rewrite buf_seq_E_B2. unfold opt_seq.
      rewrite ?app_nil_r, <- !app_assoc.
      rewrite <- !app_assoc in Hpr.
      f_equal. rewrite <- Hpr. reflexivity.

  - (* (Overflow, Ok) — buffer_push_chain *)
    destruct (Nat.eq_dec (Model.E.level A pc) (Model.E.level A pd)) as [eq|]; [|discriminate].
    inversion Hms; subst; clear Hms.
    rewrite Hpd, Hsd.
    unfold chain_to_list, chain_seq, packet_seq.
    rewrite buffer_push_chain_seq, Model.E.to_list_pair.
    unfold buf_seq_E. cbn -[Model.E.to_list].
    rewrite <- !app_assoc. reflexivity.

  - (* (Overflow, Overflow) — buffer_halve + pair_each_buf *)
    destruct (Nat.eq_dec (Model.E.level A pc) (Model.E.level A pd)) as [eq_cd|]; [|discriminate].
    destruct (Nat.eq_dec (Model.E.level A sa) (Model.E.level A sb)) as [eq_ab|]; [|discriminate].
    pose proof (@buffer_halve_seq A b2) as Hhalve.
    destruct (buffer_halve b2) as [midopt rest_pairs] eqn:Hhalve_eq.
    destruct (pair_each_buf rest_pairs) as [rest|] eqn:Hpair_each; [|discriminate].
    inversion Hms; subst; clear Hms.
    rewrite Hpd, Hsd.
    rewrite <- (@pair_each_buf_seq A _ _ Hpair_each) in Hhalve.
    rewrite chain_to_list_nested.
    rewrite buf_seq_E_B1, !Model.E.to_list_pair.
    unfold suffix12.
    destruct midopt as [m|]; cbn -[Model.E.to_list buf_seq_E].
    + (* midopt = Some m: suffix12 yields B2 *)
      rewrite buf_seq_E_B2, Model.E.to_list_pair.
      rewrite Hhalve. unfold opt_seq. rewrite <- !app_assoc. reflexivity.
    + (* midopt = None: suffix12 yields B1 *)
      rewrite buf_seq_E_B1, Model.E.to_list_pair.
      rewrite Hhalve. unfold opt_seq. cbn. rewrite <- !app_assoc. reflexivity.
Qed.

(* ========================================================================== *)
(* KChain → Chain conversion preserves sequence                                *)
(* ========================================================================== *)

(** The forgetful map [kchain_to_chain] is a bijection sequence-wise:
    [kchain_to_list c = chain_to_list (kchain_to_chain c)] (definitional). *)
Lemma kchain_to_list_chain :
  forall (A : Type) (c : KChain A),
    kchain_to_list c = chain_to_list (kchain_to_chain c).
Proof. intros. unfold kchain_to_list. reflexivity. Qed.

Lemma kchain_to_chain_g_inv :
  forall (A : Type) (c : Chain A),
    kchain_to_chain (chain_to_kchain_g c) = c.
Proof.
  intros A c. induction c as [b|p c' IH]; cbn; auto.
  rewrite IH. reflexivity.
Qed.

Lemma kchain_to_list_chain_g :
  forall (A : Type) (c : Chain A),
    kchain_to_list (chain_to_kchain_g c) = chain_to_list c.
Proof.
  intros. unfold kchain_to_list. rewrite kchain_to_chain_g_inv. reflexivity.
Qed.

(* ========================================================================== *)
(* green_of_red_k_seq                                                          *)
(* ========================================================================== *)

(** Helper: 5-place "rebalance equality" lemma — given the two boundary
    equations [a++b=a'++b'] and [c++d=c'++d'], the chain
    [a++(b++X++c)++d = a'++(b'++X++c')++d']. Used in green_of_red_k_seq
    for both Case 2 and Case 3. *)
Lemma rebal_eq :
  forall {T} (a b X c d a' b' c' d' : list T),
    a ++ b = a' ++ b' ->
    c ++ d = c' ++ d' ->
    a ++ (b ++ X ++ c) ++ d = a' ++ (b' ++ X ++ c') ++ d'.
Proof.
  intros T a b X c d a' b' c' d' Hab Hcd.
  rewrite <- !app_assoc.
  transitivity (a' ++ b' ++ X ++ c ++ d).
  - rewrite (app_assoc a), Hab, <- app_assoc. reflexivity.
  - f_equal. f_equal. f_equal. exact Hcd.
Qed.

(** [green_of_red_k c = Some c'] preserves sequence: result has same flat
    elements as input. Three cases mirror Viennot's [green_of_red]. *)
Lemma green_of_red_k_seq :
  forall (A : Type) (c c' : KChain A),
    green_of_red_k c = Some c' ->
    kchain_to_list c' = kchain_to_list c.
Proof.
  intros A c c' Hg.
  unfold green_of_red_k in Hg.
  destruct c as [|col p c_tail]; [discriminate|].
  destruct col; try discriminate.
  destruct p as [|pre1 i suf1]; [discriminate|].
  destruct i as [|pre2 child suf2].
  - (* Hole inner: Case 1 or Case 2 *)
    destruct c_tail as [b | col2 [|pre2_t child_t suf2_t] c2_t].
    + (* Case 1: tail is KEnding b. *)
      destruct (make_small pre1 b suf1) as [c''|] eqn:Hms; [|discriminate].
      inversion Hg; subst; clear Hg.
      rewrite kchain_to_list_chain_g.
      rewrite (make_small_seq Hms).
      unfold kchain_to_list, kchain_to_chain, chain_to_list, chain_seq, packet_seq.
      reflexivity.
    + (* Tail is KCons _ Hole _ — degenerate, no match. *)
      discriminate.
    + (* Case 2: tail is KCons _ (PNode pre2_t child_t suf2_t) c2_t *)
      destruct (green_prefix_concat pre1 pre2_t) as [[pre1' pre2_t']|] eqn:Hpc; [|discriminate].
      destruct (green_suffix_concat suf2_t suf1) as [[suf2_t' suf1']|] eqn:Hsc; [|discriminate].
      inversion Hg; subst; clear Hg.
      unfold kchain_to_list, kchain_to_chain, chain_to_list, chain_seq, packet_seq.
      pose proof (green_prefix_concat_seq Hpc) as Hpc_seq.
      pose proof (green_suffix_concat_seq Hsc) as Hsc_seq.
      apply rebal_eq; symmetry; assumption.
  - (* PNode inner: Case 3 *)
    destruct (prefix_concat pre1 pre2) as [[pre1' pre2']|] eqn:Hpc; [|discriminate].
    destruct (suffix_concat suf2 suf1) as [[suf2' suf1']|] eqn:Hsc; [|discriminate].
    inversion Hg; subst; clear Hg.
    unfold kchain_to_list, kchain_to_chain, chain_to_list, chain_seq, packet_seq.
    pose proof (prefix_concat_seq Hpc) as Hpc_seq.
    pose proof (suffix_concat_seq Hsc) as Hsc_seq.
    apply rebal_eq; symmetry; assumption.
Qed.

(* ========================================================================== *)
(* ensure_green_k_seq / make_yellow_k_seq / make_red_k_seq                     *)
(* ========================================================================== *)

(** [ensure_green_k] preserves sequence: dispatches on top color,
    Red → green_of_red_k; otherwise no-op. *)
Lemma ensure_green_k_seq :
  forall (A : Type) (c c' : KChain A),
    ensure_green_k c = Some c' ->
    kchain_to_list c' = kchain_to_list c.
Proof.
  intros A c c' He.
  unfold ensure_green_k in He.
  destruct c as [b|col p c_tail].
  - inversion He; subst; clear He. reflexivity.
  - destruct col.
    + inversion He; subst; clear He. reflexivity.
    + inversion He; subst; clear He. reflexivity.
    + apply (green_of_red_k_seq He).
Qed.

(** [make_yellow_k] preserves sequence relative to a packet wrapping. *)
Lemma make_yellow_k_seq :
  forall (A : Type) (pre : Buf5 (Model.E.t A)) (i : Packet A)
         (suf : Buf5 (Model.E.t A)) (c c' : KChain A),
    make_yellow_k pre i suf c = Some c' ->
    kchain_to_list c'
      = buf_seq_E pre ++ packet_seq i (kchain_to_list c) ++ buf_seq_E suf.
Proof.
  intros A pre i suf c c' Hm.
  unfold make_yellow_k in Hm.
  destruct (ensure_green_k c) as [c''|] eqn:He; [|discriminate].
  inversion Hm; subst; clear Hm.
  pose proof (ensure_green_k_seq He) as Hseq.
  unfold kchain_to_list, chain_to_list in *.
  cbn -[buf_seq_E].
  rewrite Hseq.
  reflexivity.
Qed.

(** [make_red_k] preserves sequence relative to a packet wrapping. *)
Lemma make_red_k_seq :
  forall (A : Type) (pre : Buf5 (Model.E.t A)) (i : Packet A)
         (suf : Buf5 (Model.E.t A)) (c c' : KChain A),
    make_red_k pre i suf c = Some c' ->
    kchain_to_list c'
      = buf_seq_E pre ++ packet_seq i (kchain_to_list c) ++ buf_seq_E suf.
Proof.
  intros A pre i suf c c' Hm.
  unfold make_red_k in Hm.
  pose proof (green_of_red_k_seq Hm) as Hseq.
  rewrite Hseq.
  unfold kchain_to_list, kchain_to_chain, chain_to_list, chain_seq, packet_seq.
  reflexivity.
Qed.

(* ========================================================================== *)
(* push_kt2_seq                                                                *)
(* ========================================================================== *)

(** [push_kt2 x c] preserves sequence: prepends [E.to_list x]. *)
Lemma push_kt2_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    push_kt2 x c = Some c' ->
    kchain_to_list c' = Model.E.to_list A x ++ kchain_to_list c.
Proof.
  intros A x c c' Hp.
  unfold push_kt2 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - (* KEnding b *)
    destruct (buf5_push_naive x b) as [b'|] eqn:Hpn.
    + inversion Hp; subst; clear Hp.
      pose proof (@buf5_push_naive_seq _ A (Model.E.to_list A) _ _ _ Hpn) as Hpn_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      unfold buf_seq_E. exact Hpn_seq.
    + (* push naive failed: b is B5, split into KCons Green ... *)
      destruct b; try discriminate.
      inversion Hp; subst; clear Hp.
      unfold kchain_to_list, chain_to_list. cbn -[Model.E.to_list].
      unfold buf_seq_E. cbn -[Model.E.to_list].
      rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
  - (* KCons col Hole _ — degenerate, no match *)
    destruct col; discriminate.
  - (* KCons col (PNode pre i suf) c_tail *)
    destruct col.
    + (* Green: green_push then make_yellow_k *)
      destruct (green_push x pre) as [pre'|] eqn:Hgp; [|discriminate].
      pose proof (green_push_seq Hgp) as Hgp_seq.
      pose proof (make_yellow_k_seq Hp) as Hmy.
      rewrite Hmy, Hgp_seq.
      unfold kchain_to_list, chain_to_list at 2. cbn -[buf_seq_E packet_seq].
      rewrite <- !app_assoc. reflexivity.
    + (* Yellow: yellow_push then make_red_k *)
      destruct (yellow_push x pre) as [pre'|] eqn:Hyp; [|discriminate].
      pose proof (yellow_push_seq Hyp) as Hyp_seq.
      pose proof (make_red_k_seq Hp) as Hmr.
      rewrite Hmr, Hyp_seq.
      unfold kchain_to_list, chain_to_list at 2. cbn -[buf_seq_E packet_seq].
      rewrite <- !app_assoc. reflexivity.
    + (* Red: invariant violation *)
      discriminate.
Qed.

(* ========================================================================== *)
(* inject_kt2_seq                                                              *)
(* ========================================================================== *)

(** [inject_kt2 c x] preserves sequence: appends [E.to_list x]. *)
Lemma inject_kt2_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    inject_kt2 c x = Some c' ->
    kchain_to_list c' = kchain_to_list c ++ Model.E.to_list A x.
Proof.
  intros A x c c' Hp.
  unfold inject_kt2 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - (* KEnding b *)
    destruct (buf5_inject_naive b x) as [b'|] eqn:Hin.
    + inversion Hp; subst; clear Hp.
      pose proof (@buf5_inject_naive_seq _ A (Model.E.to_list A) _ _ _ Hin) as Hin_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      unfold buf_seq_E. exact Hin_seq.
    + destruct b; try discriminate.
      inversion Hp; subst; clear Hp.
      unfold kchain_to_list, chain_to_list. cbn -[Model.E.to_list].
      unfold buf_seq_E. cbn -[Model.E.to_list].
      rewrite ?app_nil_r, <- ?app_assoc. reflexivity.
  - destruct col; discriminate.
  - destruct col.
    + destruct (green_inject suf x) as [suf'|] eqn:Hgi; [|discriminate].
      pose proof (green_inject_seq Hgi) as Hgi_seq.
      pose proof (make_yellow_k_seq Hp) as Hmy.
      rewrite Hmy, Hgi_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite ?app_assoc. reflexivity.
    + destruct (yellow_inject suf x) as [suf'|] eqn:Hyi; [|discriminate].
      pose proof (yellow_inject_seq Hyi) as Hyi_seq.
      pose proof (make_red_k_seq Hp) as Hmr.
      rewrite Hmr, Hyi_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite ?app_assoc. reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* pop_kt2_seq                                                                 *)
(* ========================================================================== *)

(** [pop_kt2 c] preserves sequence: input list = popped element ++ result. *)
Lemma pop_kt2_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    pop_kt2 c = Some (x, c') ->
    kchain_to_list c = Model.E.to_list A x ++ kchain_to_list c'.
Proof.
  intros A c c' x Hp.
  unfold pop_kt2 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - (* KEnding b *)
    destruct (buf5_pop_naive b) as [[x' b']|] eqn:Hpn; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@buf5_pop_naive_seq _ A (Model.E.to_list A) _ _ _ Hpn) as Hpn_seq.
    unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
    unfold buf_seq_E. exact Hpn_seq.
  - destruct col; discriminate.
  - destruct col.
    + (* Green: green_pop then make_yellow_k *)
      destruct (green_pop pre) as [[x' pre']|] eqn:Hgp; [|discriminate].
      destruct (make_yellow_k pre' i suf c_tail) as [c''|] eqn:Hmy; [|discriminate].
      inversion Hp; subst; clear Hp.
      pose proof (green_pop_seq Hgp) as Hgp_seq.
      pose proof (make_yellow_k_seq Hmy) as Hmy_seq.
      rewrite Hmy_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite Hgp_seq.
      rewrite <- !app_assoc. reflexivity.
    + (* Yellow: yellow_pop then make_red_k *)
      destruct (yellow_pop pre) as [[x' pre']|] eqn:Hyp; [|discriminate].
      destruct (make_red_k pre' i suf c_tail) as [c''|] eqn:Hmr; [|discriminate].
      inversion Hp; subst; clear Hp.
      pose proof (yellow_pop_seq Hyp) as Hyp_seq.
      pose proof (make_red_k_seq Hmr) as Hmr_seq.
      rewrite Hmr_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite Hyp_seq.
      rewrite <- !app_assoc. reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* eject_kt2_seq                                                               *)
(* ========================================================================== *)

(** [eject_kt2 c] preserves sequence: input list = result ++ ejected element. *)
Lemma eject_kt2_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    eject_kt2 c = Some (c', x) ->
    kchain_to_list c = kchain_to_list c' ++ Model.E.to_list A x.
Proof.
  intros A c c' x Hp.
  unfold eject_kt2 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct (buf5_eject_naive b) as [[b' x']|] eqn:Hen; [|discriminate].
    inversion Hp; subst; clear Hp.
    pose proof (@buf5_eject_naive_seq _ A (Model.E.to_list A) _ _ _ Hen) as Hen_seq.
    unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
    unfold buf_seq_E. exact Hen_seq.
  - destruct col; discriminate.
  - destruct col.
    + destruct (green_eject suf) as [[suf' x']|] eqn:Hge; [|discriminate].
      destruct (make_yellow_k pre i suf' c_tail) as [c''|] eqn:Hmy; [|discriminate].
      inversion Hp; subst; clear Hp.
      pose proof (green_eject_seq Hge) as Hge_seq.
      pose proof (make_yellow_k_seq Hmy) as Hmy_seq.
      rewrite Hmy_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite Hge_seq.
      rewrite ?app_assoc. reflexivity.
    + destruct (yellow_eject suf) as [[suf' x']|] eqn:Hye; [|discriminate].
      destruct (make_red_k pre i suf' c_tail) as [c''|] eqn:Hmr; [|discriminate].
      inversion Hp; subst; clear Hp.
      pose proof (yellow_eject_seq Hye) as Hye_seq.
      pose proof (make_red_k_seq Hmr) as Hmr_seq.
      rewrite Hmr_seq.
      unfold kchain_to_list, chain_to_list. cbn -[buf_seq_E].
      rewrite Hye_seq.
      rewrite ?app_assoc. reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* yellow_wrap = make_yellow_k (case-by-case equivalence)                      *)
(* ========================================================================== *)

(** [yellow_wrap] is the inlined equivalent of [make_yellow_k]: identical
    behaviour modulo the fast-path special-case for non-Red tails. *)
Lemma yellow_wrap_eq_make_yellow_k :
  forall (A : Type) (pre : Buf5 (Model.E.t A)) (i : Packet A)
         (suf : Buf5 (Model.E.t A)) (c : KChain A),
    yellow_wrap pre i suf c = make_yellow_k pre i suf c.
Proof.
  intros A pre i suf c.
  unfold yellow_wrap, make_yellow_k, ensure_green_k.
  destruct c as [|col p c']; [reflexivity|].
  destruct col; reflexivity.
Qed.

(** [yellow_wrap_seq]: derived from [make_yellow_k_seq] via the equivalence. *)
Lemma yellow_wrap_seq :
  forall (A : Type) (pre : Buf5 (Model.E.t A)) (i : Packet A)
         (suf : Buf5 (Model.E.t A)) (c c' : KChain A),
    yellow_wrap pre i suf c = Some c' ->
    kchain_to_list c'
      = buf_seq_E pre ++ packet_seq i (kchain_to_list c) ++ buf_seq_E suf.
Proof.
  intros A pre i suf c c' Hy.
  rewrite yellow_wrap_eq_make_yellow_k in Hy.
  apply (make_yellow_k_seq Hy).
Qed.

(* ========================================================================== *)
(* push_kt3_seq                                                                *)
(* ========================================================================== *)

(** [push_kt3] preserves sequence (inlined Yellow fast path). *)
Lemma push_kt3_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    push_kt3 x c = Some c' ->
    kchain_to_list c' = Model.E.to_list A x ++ kchain_to_list c.
Proof.
  intros A x c c' Hp.
  unfold push_kt3 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - (* KEnding b: explicit per-buffer-shape rules. *)
    destruct b; inversion Hp; subst; clear Hp;
      unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
      unfold buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - destruct col; discriminate.
  - destruct col.
    + (* Green: only B2 / B3 succeed via yellow_wrap. *)
      destruct pre; try discriminate;
        pose proof (yellow_wrap_seq Hp) as Hyw;
        rewrite Hyw;
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
        unfold buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + (* Yellow: B1/B2/B3 short-circuit, B4 fires green_of_red_k. *)
      destruct pre; try discriminate.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * (* B4: green_of_red_k path *)
        pose proof (green_of_red_k_seq Hp) as Hg.
        rewrite Hg.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* inject_kt3_seq                                                              *)
(* ========================================================================== *)

Lemma inject_kt3_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    inject_kt3 c x = Some c' ->
    kchain_to_list c' = kchain_to_list c ++ Model.E.to_list A x.
Proof.
  intros A x c c' Hp.
  unfold inject_kt3 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst; clear Hp;
      unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
      unfold buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, ?app_assoc; reflexivity.
  - destruct col; discriminate.
  - destruct col.
    + destruct suf; try discriminate;
        pose proof (yellow_wrap_seq Hp) as Hyw;
        rewrite Hyw;
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
        unfold buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
    + destruct suf; try discriminate.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * pose proof (green_of_red_k_seq Hp) as Hg.
        rewrite Hg.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* pop_kt3_seq                                                                 *)
(* ========================================================================== *)

Lemma pop_kt3_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    pop_kt3 c = Some (x, c') ->
    kchain_to_list c = Model.E.to_list A x ++ kchain_to_list c'.
Proof.
  intros A c c' x Hp.
  unfold pop_kt3 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst; clear Hp;
      unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
      unfold buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
  - destruct col; discriminate.
  - destruct col.
    + (* Green: B2 / B3 succeed via yellow_wrap. *)
      destruct pre; try discriminate;
        (destruct (yellow_wrap _ i suf c_tail) as [c''|] eqn:Hyw; [|discriminate]);
        inversion Hp; subst; clear Hp;
        pose proof (yellow_wrap_seq Hyw) as Hyw_seq;
        rewrite Hyw_seq;
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
        unfold buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + (* Yellow: B1 fires green_of_red_k, B2/B3/B4 short-circuit. *)
      destruct pre; try discriminate.
      * (* B1: green_of_red_k path *)
        destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst; clear Hp.
        pose proof (green_of_red_k_seq Hg) as Hg_seq.
        rewrite Hg_seq.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, <- ?app_assoc; reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* eject_kt3_seq                                                               *)
(* ========================================================================== *)

Lemma eject_kt3_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    eject_kt3 c = Some (c', x) ->
    kchain_to_list c = kchain_to_list c' ++ Model.E.to_list A x.
Proof.
  intros A c c' x Hp.
  unfold eject_kt3 in Hp.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; inversion Hp; subst; clear Hp;
      unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
      unfold buf_seq_E; cbn -[Model.E.to_list];
      rewrite ?app_nil_r, ?app_assoc; reflexivity.
  - destruct col; discriminate.
  - destruct col.
    + destruct suf; try discriminate;
        (destruct (yellow_wrap pre i _ c_tail) as [c''|] eqn:Hyw; [|discriminate]);
        inversion Hp; subst; clear Hp;
        pose proof (yellow_wrap_seq Hyw) as Hyw_seq;
        rewrite Hyw_seq;
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list];
        unfold buf_seq_E; cbn -[Model.E.to_list];
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
    + destruct suf; try discriminate.
      * destruct (green_of_red_k _) as [c''|] eqn:Hg; [|discriminate].
        inversion Hp; subst; clear Hp.
        pose proof (green_of_red_k_seq Hg) as Hg_seq.
        rewrite Hg_seq.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
      * inversion Hp; subst; clear Hp.
        unfold kchain_to_list, chain_to_list; cbn -[Model.E.to_list].
        unfold buf_seq_E; cbn -[Model.E.to_list].
        rewrite ?app_nil_r, ?app_assoc; reflexivity.
    + discriminate.
Qed.

(* ========================================================================== *)
(* kt4 ↔ kt3 equivalence via option-to-result translation                      *)
(* ========================================================================== *)

(** [yellow_wrap_pr] is [yellow_wrap] with [option] → [push_result]. *)
Lemma yellow_wrap_pr_eq :
  forall (A : Type) (pre : Buf5 (Model.E.t A)) (i : Packet A)
         (suf : Buf5 (Model.E.t A)) (c : KChain A),
    yellow_wrap_pr pre i suf c
    = match yellow_wrap pre i suf c with
      | Some c' => PushOk c'
      | None    => PushFail
      end.
Proof.
  intros A pre i suf c.
  unfold yellow_wrap_pr, yellow_wrap.
  destruct c as [|col p c']; [reflexivity|].
  destruct col; [reflexivity| reflexivity|].
  destruct (green_of_red_k _); reflexivity.
Qed.

Lemma push_kt4_eq :
  forall (A : Type) (x : Model.E.t A) (c : KChain A),
    push_kt4 x c
    = match push_kt3 x c with
      | Some c' => PushOk c'
      | None    => PushFail
      end.
Proof.
  intros A x c.
  unfold push_kt4, push_kt3.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; reflexivity.
  - destruct col; reflexivity.
  - destruct col.
    + destruct pre; try reflexivity; rewrite yellow_wrap_pr_eq; reflexivity.
    + destruct pre; reflexivity.
    + reflexivity.
Qed.

Lemma inject_kt4_eq :
  forall (A : Type) (x : Model.E.t A) (c : KChain A),
    inject_kt4 c x
    = match inject_kt3 c x with
      | Some c' => PushOk c'
      | None    => PushFail
      end.
Proof.
  intros A x c.
  unfold inject_kt4, inject_kt3.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; reflexivity.
  - destruct col; reflexivity.
  - destruct col.
    + destruct suf; try reflexivity; rewrite yellow_wrap_pr_eq; reflexivity.
    + destruct suf; reflexivity.
    + reflexivity.
Qed.

Lemma pop_kt4_eq :
  forall (A : Type) (c : KChain A),
    pop_kt4 c
    = match pop_kt3 c with
      | Some (x, c') => PopOk x c'
      | None         => PopFail
      end.
Proof.
  intros A c.
  unfold pop_kt4, pop_kt3.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; reflexivity.
  - destruct col; reflexivity.
  - destruct col.
    + destruct pre; try reflexivity;
        rewrite yellow_wrap_pr_eq;
        destruct (yellow_wrap _ _ _ _); reflexivity.
    + destruct pre; try reflexivity;
        destruct (green_of_red_k _); reflexivity.
    + reflexivity.
Qed.

Lemma eject_kt4_eq :
  forall (A : Type) (c : KChain A),
    eject_kt4 c
    = match eject_kt3 c with
      | Some (c', x) => PopOk x c'
      | None         => PopFail
      end.
Proof.
  intros A c.
  unfold eject_kt4, eject_kt3.
  destruct c as [b | col [|pre i suf] c_tail].
  - destruct b; reflexivity.
  - destruct col; reflexivity.
  - destruct col.
    + destruct suf; try reflexivity;
        rewrite yellow_wrap_pr_eq;
        destruct (yellow_wrap _ _ _ _); reflexivity.
    + destruct suf; try reflexivity;
        destruct (green_of_red_k _); reflexivity.
    + reflexivity.
Qed.

(** Headline kt4 seq theorems, derived mechanically from kt3 via the equivalence. *)
Lemma push_kt4_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    push_kt4 x c = PushOk c' ->
    kchain_to_list c' = Model.E.to_list A x ++ kchain_to_list c.
Proof.
  intros A x c c' Hp.
  rewrite push_kt4_eq in Hp.
  destruct (push_kt3 x c) as [c''|] eqn:H3; [|discriminate].
  inversion Hp; subst; clear Hp.
  apply (push_kt3_seq H3).
Qed.

Lemma inject_kt4_seq :
  forall (A : Type) (x : Model.E.t A) (c c' : KChain A),
    inject_kt4 c x = PushOk c' ->
    kchain_to_list c' = kchain_to_list c ++ Model.E.to_list A x.
Proof.
  intros A x c c' Hp.
  rewrite inject_kt4_eq in Hp.
  destruct (inject_kt3 c x) as [c''|] eqn:H3; [|discriminate].
  inversion Hp; subst; clear Hp.
  apply (inject_kt3_seq H3).
Qed.

Lemma pop_kt4_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    pop_kt4 c = PopOk x c' ->
    kchain_to_list c = Model.E.to_list A x ++ kchain_to_list c'.
Proof.
  intros A c c' x Hp.
  rewrite pop_kt4_eq in Hp.
  destruct (pop_kt3 c) as [[x' c'']|] eqn:H3; [|discriminate].
  inversion Hp; subst; clear Hp.
  apply (pop_kt3_seq H3).
Qed.

Lemma eject_kt4_seq :
  forall (A : Type) (c c' : KChain A) (x : Model.E.t A),
    eject_kt4 c = PopOk x c' ->
    kchain_to_list c = kchain_to_list c' ++ Model.E.to_list A x.
Proof.
  intros A c c' x Hp.
  rewrite eject_kt4_eq in Hp.
  destruct (eject_kt3 c) as [[c'' x']|] eqn:H3; [|discriminate].
  inversion Hp; subst; clear Hp.
  apply (eject_kt3_seq H3).
Qed.

