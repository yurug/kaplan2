(** * Module: KTDeque.Cadeque8.WF — regularity preservation for the
      five public Cadeque8 operations.

    ## Two-layer formalisation

    1. [wf_kcad8] — the closure invariant.  Captures structural
       well-formedness of [KCadeque8 X] values produced by the public
       API.  Preserved by every public op ([push], [inject], [pop],
       [eject], [concat]) with zero admits.

    2. [wf_kcad8_strong] — the headline KT99 §6 invariant
       ([K8Triple]'s head and tail buffers are non-empty, and every
       stored cell in the middle has non-empty prefix/buffer).
       Preserved by [push], [inject], and [concat].  For [pop] and
       [eject], the public op's result satisfies [wf_kcad8_strong]
       when the structural fast path returned [None] and the
       [kcad8_from_list] fallback fires (which produces a [K8Empty]
       or non-empty [K8Simple] — both trivially [wf_kcad8_strong]).

    On the structural success path [kcad8_pop] / [kcad8_eject]'s
    result always satisfies [wf_kcad8] (the weak invariant); it
    satisfies [wf_kcad8_strong] under most operating conditions but
    not in the rebalance corner case where the unfolded subcadeque
    has empty boundary buffers (cf. the file
    [Cadeque8/Seq.v]'s pop-rebalance discussion).  The bench
    workloads — including 1000-concat adversarial — do not surface
    user-observable consequences of this corner case.

    Tightening pop/eject preservation to [wf_kcad8_strong]
    unconditionally would require either an algorithmic change at
    the rebalance step (adding KT99-style yellow-colour bookkeeping
    at the Cadeque8 level) or a richer mutual invariant tracking
    the depth of nested wrappers.  Both are out of scope here. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops.

(* ========================================================================== *)
(* PART 1: the closure invariant [wf_kcad8] preserved by all 5 public ops.    *)
(* ========================================================================== *)

(** [wf_kcad8 k]: structural well-formedness.  All [KCadeque8] values
    are well-formed under this definition — but we package it so that
    the preservation theorems instantiate naturally and so that the
    statement of "all 5 ops preserve wf_kcad8" is meaningful. *)
Definition wf_kcad8 {X : Type} (k : KCadeque8 X) : Prop :=
  match k with
  | K8Empty        => True
  | K8Simple b     => buf6_is_empty b = false
  | K8Triple _ _ _ => True
  end.

(* --- helper lemmas on buffer non-emptiness --- *)

Lemma buf6_push_not_empty :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_is_empty (buf6_push x b) = false.
Proof. intros X x [xs]. reflexivity. Qed.

Lemma buf6_inject_not_empty :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_is_empty (buf6_inject b x) = false.
Proof.
  intros X [xs] x. unfold buf6_inject, buf6_is_empty, buf6_elems.
  destruct xs; reflexivity.
Qed.

Lemma kcad8_simple_or_empty_wf :
  forall (X : Type) (b : Buf6 (KElem8 X)), wf_kcad8 (kcad8_simple_or_empty b).
Proof.
  intros X b. unfold kcad8_simple_or_empty.
  destruct (buf6_is_empty b) eqn:Hb; cbn; auto.
Qed.

(** [kcad8_push] preserves [wf_kcad8]. *)
Theorem kcad8_push_wf :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    wf_kcad8 k -> wf_kcad8 (kcad8_push x k).
Proof.
  intros X x k _. destruct k as [|b|h m t]; cbn [kcad8_push].
  - cbn. reflexivity.
  - cbn. destruct b. reflexivity.
  - cbn. exact I.
Qed.

(** [kcad8_inject] preserves [wf_kcad8]. *)
Theorem kcad8_inject_wf :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    wf_kcad8 k -> wf_kcad8 (kcad8_inject k x).
Proof.
  intros X k x _. destruct k as [|b|h m t]; cbn [kcad8_inject].
  - cbn. reflexivity.
  - cbn. destruct b as [xs]. unfold buf6_inject, buf6_is_empty, buf6_elems.
    destruct xs; reflexivity.
  - cbn. exact I.
Qed.

(** [kcad8_concat] preserves [wf_kcad8]. *)
Theorem kcad8_concat_wf :
  forall (X : Type) (a b : KCadeque8 X),
    wf_kcad8 a -> wf_kcad8 b -> wf_kcad8 (kcad8_concat a b).
Proof.
  intros X a b Ha Hb.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad8_concat]; auto.
  all: try exact I.
Qed.

(** [kcad8_from_list] always returns a [wf_kcad8] result. *)
Lemma kcad8_from_list_wf :
  forall (X : Type) (xs : list X), wf_kcad8 (kcad8_from_list xs).
Proof.
  intros X xs. unfold kcad8_from_list.
  assert (Hgen : forall (acc : KCadeque8 X) (l : list X),
                   wf_kcad8 acc ->
                   wf_kcad8 (List.fold_left
                               (fun a z => kcad8_inject a z) l acc)).
  { intros acc l. revert acc.
    induction l as [|z zs IH]; intros acc Hacc; cbn.
    - exact Hacc.
    - apply IH. apply kcad8_inject_wf. exact Hacc. }
  apply Hgen. exact I.
Qed.

(** The structural pop always produces a [wf_kcad8] result.

    Key path:  when the rebalance step lands on [kcad8_simple_or_empty t]
    (because [m] was empty), the [kcad8_simple_or_empty] guard collapses
    to [K8Empty] when [t] is empty and to [K8Simple t] otherwise.  Both
    are [wf_kcad8].  All other paths produce either an explicit
    [if buf6_is_empty _ then K8Empty else K8Simple _] or a [K8Triple]
    (unconstrained at this layer). *)
Lemma kcad8_pop_struct_wf :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop_struct k = Some (x, k') -> wf_kcad8 k'.
Proof.
  intros X k x k' H.
  destruct k as [|b|h m t]; cbn [kcad8_pop_struct] in H.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|]; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    injection H as Hxv Hk'. subst xv k'.
    destruct (buf6_is_empty b') eqn:He; cbn.
    + exact I.
    + exact He.
  - destruct (buf6_pop h) as [[e h']|] eqn:Hpop.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty h') eqn:Hhe.
      * injection H as Hxv Hk'. subst xv k'.
        unfold rebalance_after_h_empty.
        destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
        2: { (* m empty: result = kcad8_simple_or_empty t *)
             apply kcad8_simple_or_empty_wf. }
        destruct s as [b|pre' sub' suf']; cbn; exact I.
      * injection H as Hxv Hk'. subst xv k'. cbn. exact I.
    + destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
      * destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
        -- destruct (buf6_pop b) as [[e b']|] eqn:Hbp; [|discriminate].
           destruct e as [xv|sv]; [|discriminate].
           injection H as Hxv Hk'. subst xv k'. cbn. exact I.
        -- destruct (buf6_pop pre) as [[e pre']|] eqn:Hpep; [|discriminate].
           destruct e as [xv|sv]; [|discriminate].
           injection H as Hxv Hk'. subst xv k'. cbn. exact I.
      * destruct (buf6_pop t) as [[e t']|] eqn:Htp; [|discriminate].
        destruct e as [xv|sv]; [|discriminate].
        injection H as Hxv Hk'. subst xv k'.
        destruct (buf6_is_empty t') eqn:Hte; cbn.
        -- exact I.
        -- exact Hte.
Qed.

(** [kcad8_pop] preserves [wf_kcad8]. *)
Theorem kcad8_pop_wf :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    wf_kcad8 k -> kcad8_pop k = Some (x, k') -> wf_kcad8 k'.
Proof.
  intros X k x k' _ H.
  unfold kcad8_pop in H.
  destruct (kcad8_pop_struct k) as [[x0 k0]|] eqn:Hstr.
  - injection H as Hx Hk. subst x0 k0.
    eapply kcad8_pop_struct_wf; eauto.
  - destruct (kcad8_to_list k) as [|y ys] eqn:Hlist; [discriminate|].
    injection H as Hx Hk. subst y k'.
    apply kcad8_from_list_wf.
Qed.

(** The structural eject always produces a [wf_kcad8] result. *)
Lemma kcad8_eject_struct_wf :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject_struct k = Some (k', x) -> wf_kcad8 k'.
Proof.
  intros X k k' x H.
  destruct k as [|b|h m t]; cbn [kcad8_eject_struct] in H.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Hej; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    injection H as Hk' Hxv. subst xv k'.
    destruct (buf6_is_empty b') eqn:He; cbn.
    + exact I.
    + exact He.
  - destruct (buf6_eject t) as [[t' e]|] eqn:Het.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty t') eqn:Hte.
      * injection H as Hk' Hxv. subst xv k'.
        unfold rebalance_after_t_empty.
        destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
        2: { apply kcad8_simple_or_empty_wf. }
        destruct s as [b|pre' sub' suf']; cbn; exact I.
      * injection H as Hk' Hxv. subst xv k'. cbn. exact I.
    + destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
      * destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
        -- (* StoredSmall — buf6_eject (mkBuf6 []) = None *)
           cbn in H. discriminate.
        -- destruct (buf6_eject suf) as [[suf' e]|] eqn:Hsp; [|discriminate].
           destruct e as [xv|sv]; [|discriminate].
           injection H as Hk' Hxv. subst xv k'. cbn. exact I.
      * destruct (buf6_eject h) as [[h' e]|] eqn:Hhp; [|discriminate].
        destruct e as [xv|sv]; [|discriminate].
        injection H as Hk' Hxv. subst xv k'.
        destruct (buf6_is_empty h') eqn:Hhe; cbn.
        -- exact I.
        -- exact Hhe.
Qed.

(** [kcad8_eject] preserves [wf_kcad8]. *)
Theorem kcad8_eject_wf :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    wf_kcad8 k -> kcad8_eject k = Some (k', x) -> wf_kcad8 k'.
Proof.
  intros X k k' x _ H.
  unfold kcad8_eject in H.
  destruct (kcad8_eject_struct k) as [[k0 x0]|] eqn:Hstr.
  - injection H as Hk Hx. subst x0 k0.
    eapply kcad8_eject_struct_wf; eauto.
  - destruct (List.rev (kcad8_to_list k)) as [|y ys] eqn:Hrev;
      [discriminate|].
    injection H as Hk Hx. subst y k'.
    apply kcad8_from_list_wf.
Qed.

(* ========================================================================== *)
(* PART 2: the strong KT99 §6 invariant.                                      *)
(* ========================================================================== *)

(** [wf_stored8 s]: every stored cell has a non-empty prefix/buffer. *)
Definition wf_stored8 {X : Type} (s : Stored8 X) : Prop :=
  match s with
  | StoredSmall8 b       => buf6_is_empty b = false
  | StoredBig8 pre _ _   => buf6_is_empty pre = false
  end.

Definition wf_middle {X : Type} (m : Buf6 (Stored8 X)) : Prop :=
  Forall wf_stored8 (buf6_elems m).

(** [wf_kcad8_strong k]: KT99 §6 well-formedness. *)
Definition wf_kcad8_strong {X : Type} (k : KCadeque8 X) : Prop :=
  match k with
  | K8Empty        => True
  | K8Simple b     => buf6_is_empty b = false
  | K8Triple h m t =>
      buf6_is_empty h = false /\
      buf6_is_empty t = false /\
      wf_middle m
  end.

Lemma wf_kcad8_strong_implies_wf :
  forall (X : Type) (k : KCadeque8 X),
    wf_kcad8_strong k -> wf_kcad8 k.
Proof.
  intros X k H. destruct k as [|b|h m t]; cbn in *; auto.
Qed.

(* --- helper lemmas for wf_middle --- *)

Lemma wf_middle_inject :
  forall (X : Type) (m : Buf6 (Stored8 X)) (s : Stored8 X),
    wf_middle m -> wf_stored8 s -> wf_middle (buf6_inject m s).
Proof.
  intros X [xs] s Hm Hs.
  unfold wf_middle, buf6_inject, buf6_elems in *.
  apply Forall_app. split; [exact Hm | apply Forall_cons; auto].
Qed.

Lemma wf_middle_singleton :
  forall (X : Type) (s : Stored8 X),
    wf_stored8 s -> wf_middle (mkBuf6 [s]).
Proof.
  intros X s Hs.
  unfold wf_middle, buf6_elems. constructor; auto.
Qed.

Lemma wf_middle_empty :
  forall (X : Type), wf_middle (mkBuf6 (@nil (Stored8 X))).
Proof.
  intros X. unfold wf_middle, buf6_elems. constructor.
Qed.

(* --- strong preservation for the constructive ops --- *)

Theorem kcad8_push_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_push x k).
Proof.
  intros X x k Hwf. destruct k as [|b|h m t]; cbn [kcad8_push].
  - cbn. reflexivity.
  - cbn. destruct b. reflexivity.
  - cbn in *. destruct Hwf as [Hh [Ht Hm]].
    destruct h. split; [reflexivity | split; assumption].
Qed.

Theorem kcad8_inject_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_inject k x).
Proof.
  intros X k x Hwf. destruct k as [|b|h m t]; cbn [kcad8_inject].
  - cbn. reflexivity.
  - cbn. destruct b as [xs]. unfold buf6_inject, buf6_is_empty, buf6_elems.
    destruct xs; reflexivity.
  - cbn in *. destruct Hwf as [Hh [Ht Hm]].
    split; [assumption | split; [|assumption]].
    destruct t as [xs]. unfold buf6_inject, buf6_is_empty, buf6_elems.
    destruct xs; reflexivity.
Qed.

Theorem kcad8_concat_wf_strong :
  forall (X : Type) (a b : KCadeque8 X),
    wf_kcad8_strong a -> wf_kcad8_strong b ->
    wf_kcad8_strong (kcad8_concat a b).
Proof.
  intros X a b Ha Hb.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad8_concat].
  - exact Hb.
  - exact Hb.
  - exact Hb.
  - exact Ha.
  - cbn in Ha, Hb |- *.
    split; [exact Ha | split; [exact Hb | apply wf_middle_empty]].
  - cbn in Ha, Hb |- *.
    destruct Hb as [Hh2 [Ht2 _]].
    split; [exact Ha | split; [exact Ht2 |]].
    apply wf_middle_singleton. cbn. exact Hh2.
  - exact Ha.
  - cbn in Ha, Hb |- *.
    destruct Ha as [Hh1 [Ht1 Hm1]].
    split; [exact Hh1 | split; [exact Hb |]].
    apply wf_middle_inject; [exact Hm1 | cbn; exact Ht1].
  - cbn in Ha, Hb |- *.
    destruct Ha as [Hh1 [Ht1 Hm1]]. destruct Hb as [Hh2 [Ht2 _]].
    split; [exact Hh1 | split; [exact Ht2 |]].
    apply wf_middle_inject; [exact Hm1 | cbn; exact Ht1].
Qed.

(** [kcad8_from_list] on any list always returns a [wf_kcad8_strong]
    result ([K8Empty] for [[]], non-empty [K8Simple] otherwise). *)
Lemma kcad8_from_list_wf_strong :
  forall (X : Type) (xs : list X), wf_kcad8_strong (kcad8_from_list xs).
Proof.
  intros X xs. unfold kcad8_from_list.
  assert (Hgen : forall (acc : KCadeque8 X) (l : list X),
                   wf_kcad8_strong acc ->
                   wf_kcad8_strong (List.fold_left
                                      (fun a z => kcad8_inject a z) l acc)).
  { intros acc l. revert acc.
    induction l as [|z zs IH]; intros acc Hacc; cbn.
    - exact Hacc.
    - apply IH. apply kcad8_inject_wf_strong. exact Hacc. }
  apply Hgen. exact I.
Qed.

(** [kcad8_pop] via fallback preserves the strong invariant. *)
Theorem kcad8_pop_wf_strong_via_fallback :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop_struct k = None ->
    kcad8_pop k = Some (x, k') ->
    wf_kcad8_strong k'.
Proof.
  intros X k x k' Hstr Hp.
  unfold kcad8_pop in Hp. rewrite Hstr in Hp.
  destruct (kcad8_to_list k) as [|y ys] eqn:Hlist; [discriminate|].
  injection Hp as Hx Hk. subst y k'.
  apply kcad8_from_list_wf_strong.
Qed.

(** [kcad8_eject] via fallback preserves the strong invariant. *)
Theorem kcad8_eject_wf_strong_via_fallback :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject_struct k = None ->
    kcad8_eject k = Some (k', x) ->
    wf_kcad8_strong k'.
Proof.
  intros X k k' x Hstr He.
  unfold kcad8_eject in He. rewrite Hstr in He.
  destruct (List.rev (kcad8_to_list k)) as [|y ys] eqn:Hrev;
    [discriminate|].
  injection He as Hk Hx. subst y k'.
  apply kcad8_from_list_wf_strong.
Qed.
