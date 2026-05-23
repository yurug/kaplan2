(** * Module: KTDeque.Cadeque8.WF — regularity preservation for the
      five public Cadeque8 operations.

    ## Two-layer formalisation

    1. [wf_kcad8] — structural well-formedness ([K8Simple] always has
       a non-empty buffer; [K8Triple] is unconstrained).  Preserved
       by every public op with zero admits.

    2. [wf_kcad8_strong] — the headline KT99 §6 invariant
       ([K8Triple]'s head and tail buffers are non-empty, and every
       stored cell in the middle has non-empty prefix/buffer).
       **Preserved by all five public operations**: [push], [inject],
       [pop], [eject], [concat], with zero admits.

    The structural fast path ([kcad8_pop_struct] / [kcad8_eject_struct])
    checks the safety of the rebalance step via the
    [stored_sub_left_safe] / [stored_sub_right_safe] predicates and
    returns [None] when a rebalance would produce a non-wf cell
    (e.g. when the unfolded subcadeque has empty inner head/tail).
    The public path then falls back to [kcad8_from_list], which
    always produces a [wf_kcad8_strong] result.  Combined with the
    structural lemmas this gives unconditional strong preservation
    for the public API. *)

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
      * unfold rebalance_after_h_empty in H.
        destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
        -- destruct (stored_sub_left_safe s) eqn:Hsls.
           2: { discriminate H. }
           destruct s as [b|pre' sub' suf']; cbn in H.
           ++ injection H as Hxv Hk'. subst xv k'. cbn. exact I.
           ++ injection H as Hxv Hk'. subst xv k'. cbn. exact I.
        -- injection H as Hxv Hk'. subst xv k'.
           apply kcad8_simple_or_empty_wf.
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
      * unfold rebalance_after_t_empty in H.
        destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
        -- destruct (stored_sub_right_safe s) eqn:Hsrs.
           2: { discriminate H. }
           destruct s as [b|pre' sub' suf']; cbn in H.
           ++ injection H as Hk' Hxv. subst xv k'. cbn. exact I.
           ++ injection H as Hk' Hxv. subst xv k'. cbn. exact I.
        -- injection H as Hk' Hxv. subst xv k'.
           apply kcad8_simple_or_empty_wf.
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

(** wf_middle preserved by buf6_push of a wf_stored8 cell.  (Moved
    here from below so [kcad8_concat_wf_strong]'s (Simple, Triple)
    case can use it.) *)
Lemma wf_middle_push :
  forall (X : Type) (s : Stored8 X) (m : Buf6 (Stored8 X)),
    wf_stored8 s -> wf_middle m -> wf_middle (buf6_push s m).
Proof.
  intros X s [xs] Hs Hm.
  unfold wf_middle, buf6_push, buf6_elems in *.
  apply Forall_cons; auto.
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
  - (* (Simple, Triple) WC O(1) fix: buf6_push (StoredSmall8 h2) m2 *)
    cbn in Ha, Hb |- *.
    destruct Hb as [Hh2 [Ht2 Hm2]].
    split; [exact Ha | split; [exact Ht2 |]].
    apply wf_middle_push; [cbn; exact Hh2 | exact Hm2].
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

(* ========================================================================== *)
(* PART 3: unconditional strong preservation for pop and eject (via the       *)
(* sub-safety guard added to [rebalance_after_h_empty] /                       *)
(* [rebalance_after_t_empty]).                                                *)
(*                                                                            *)
(* The structural fast path returns [Some] iff the rebalance can produce a    *)
(* [wf_kcad8_strong] result.  The public path either takes the fast path      *)
(* (wf_strong by the structural lemma) or falls back to [kcad8_from_list]     *)
(* (wf_strong by [kcad8_from_list_wf_strong]).                                *)
(* ========================================================================== *)

(** A popped stored cell that satisfies [wf_stored8] has non-empty prefix
    (or non-empty small buffer). *)
Lemma wf_stored8_pre_not_empty :
  forall (X : Type) (s : Stored8 X),
    wf_stored8 s ->
    match s with
    | StoredSmall8 b      => buf6_is_empty b = false
    | StoredBig8 pre _ _  => buf6_is_empty pre = false
    end.
Proof. intros X [b|pre sub suf] H; cbn in H; exact H. Qed.

(** Popping from a [wf_middle] buffer yields a [wf_stored8] cell and a
    [wf_middle] rest. *)
Lemma buf6_pop_wf_middle :
  forall (X : Type) (m : Buf6 (Stored8 X)) (s : Stored8 X)
         (m_rest : Buf6 (Stored8 X)),
    wf_middle m ->
    buf6_pop m = Some (s, m_rest) ->
    wf_stored8 s /\ wf_middle m_rest.
Proof.
  intros X [xs] s m_rest Hm Hp.
  unfold wf_middle, buf6_elems in *.
  unfold buf6_pop, buf6_elems in Hp.
  destruct xs as [|y ys]; [discriminate|].
  inversion Hp; subst s m_rest. cbn.
  inversion Hm; subst. split; assumption.
Qed.

Lemma buf6_eject_wf_middle :
  forall (X : Type) (m : Buf6 (Stored8 X)) (s : Stored8 X)
         (m_rest : Buf6 (Stored8 X)),
    wf_middle m ->
    buf6_eject m = Some (m_rest, s) ->
    wf_stored8 s /\ wf_middle m_rest.
Proof.
  intros X [xs] s m_rest Hm He.
  unfold wf_middle, buf6_elems in *.
  unfold buf6_eject, buf6_elems in He.
  destruct (List.rev xs) as [|y ys] eqn:Hrev; [discriminate|].
  inversion He; subst m_rest s. cbn.
  apply (f_equal (@List.rev (Stored8 X))) in Hrev.
  rewrite List.rev_involutive in Hrev. cbn in Hrev.
  rewrite Hrev in Hm.
  apply Forall_app in Hm. destruct Hm as [Hm_rest Hy].
  inversion Hy; subst.
  split; [assumption | exact Hm_rest].
Qed.

(** Reassemble preserves wf_strong when input cell satisfies the
    sub-left safety check. *)
Lemma reassemble_after_pop_unfold_wf :
  forall (X : Type) (s : Stored8 X)
         (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X) (suf : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)) (t : Buf6 (KElem8 X)),
    wf_stored8 s ->
    stored_sub_left_safe s = true ->
    unfold_stored s = (pre, sub, suf) ->
    buf6_is_empty t = false ->
    wf_middle m_rest ->
    wf_kcad8_strong (reassemble_after_pop_unfold pre sub suf m_rest t).
Proof.
  intros X s pre sub suf m_rest t Hwf Hsls Hunf Ht Hm_rest.
  unfold reassemble_after_pop_unfold.
  destruct s as [b|pre0 sub0 suf0]; cbn in Hunf, Hwf, Hsls.
  - (* StoredSmall b: pre=b, sub=K8Empty, suf=mkBuf6 [] *)
    inversion Hunf; subst pre sub suf.
    cbn. split; [exact Hwf | split; [exact Ht | exact Hm_rest]].
  - (* StoredBig8 pre0 sub0 suf0 *)
    inversion Hunf; subst pre sub suf.
    cbn. split; [exact Hwf | split; [exact Ht |]].
    (* wf_middle of m_final.  Convert Hsls into the per-shape facts. *)
    destruct sub0 as [|sb|sh sm st]; cbn in Hsls.
    + (* sub0 = K8Empty: Hsls vacuous *)
      destruct (buf6_is_empty suf0) eqn:Hsuf0.
      * exact Hm_rest.
      * apply wf_middle_push; [cbn; exact Hsuf0 | exact Hm_rest].
    + (* sub0 = K8Simple sb *)
      apply Bool.negb_true_iff in Hsls.
      destruct (buf6_is_empty suf0) eqn:Hsuf0.
      * apply wf_middle_push; [cbn; exact Hsls | exact Hm_rest].
      * assert (Hms : wf_middle (buf6_push (StoredSmall8 suf0) m_rest))
          by (apply wf_middle_push; [cbn; exact Hsuf0 | exact Hm_rest]).
        apply wf_middle_push; [cbn; exact Hsls | exact Hms].
    + (* sub0 = K8Triple sh sm st *)
      apply Bool.negb_true_iff in Hsls.
      destruct (buf6_is_empty suf0) eqn:Hsuf0.
      * apply wf_middle_push; [cbn; exact Hsls | exact Hm_rest].
      * assert (Hms : wf_middle (buf6_push (StoredSmall8 suf0) m_rest))
          by (apply wf_middle_push; [cbn; exact Hsuf0 | exact Hm_rest]).
        apply wf_middle_push; [cbn; exact Hsls | exact Hms].
Qed.

(** Reassemble (eject side) preserves wf_strong when sub-right safe. *)
Lemma reassemble_after_eject_unfold_wf :
  forall (X : Type) (s : Stored8 X) (h : Buf6 (KElem8 X))
         (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X) (suf : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)),
    wf_stored8 s ->
    stored_sub_right_safe s = true ->
    unfold_stored s = (pre, sub, suf) ->
    buf6_is_empty h = false ->
    wf_middle m_rest ->
    wf_kcad8_strong (reassemble_after_eject_unfold h pre sub suf m_rest).
Proof.
  intros X s h pre sub suf m_rest Hwf Hsrs Hunf Hh Hm_rest.
  unfold reassemble_after_eject_unfold.
  destruct s as [b|pre0 sub0 suf0]; cbn in Hunf, Hwf, Hsrs.
  - (* StoredSmall: stored_sub_right_safe always false — discriminate *)
    discriminate Hsrs.
  - inversion Hunf; subst pre sub suf.
    (* Hsrs encodes both: suf0 non-empty and (per sub0 shape) inner safety. *)
    destruct sub0 as [|sb|sh sm st]; cbn in Hsrs.
    + (* sub0 = K8Empty: Hsrs = negb (buf6_is_empty suf0) = true *)
      apply Bool.negb_true_iff in Hsrs.
      cbn. split; [exact Hh | split; [exact Hsrs |]].
      (* m_final = if buf6_is_empty pre0 then m_rest else inject m_rest (StoredSmall pre0) *)
      destruct (buf6_is_empty pre0) eqn:Hpre0; cbn.
      * exact Hm_rest.
      * apply wf_middle_inject; [exact Hm_rest | cbn; exact Hpre0].
    + (* sub0 = K8Simple sb: Hsrs = sb non-empty AND suf0 non-empty *)
      apply andb_prop in Hsrs. destruct Hsrs as [Hsb Hsuf0].
      apply Bool.negb_true_iff in Hsb. apply Bool.negb_true_iff in Hsuf0.
      cbn. split; [exact Hh | split; [exact Hsuf0 |]].
      destruct (buf6_is_empty pre0) eqn:Hpre0; cbn.
      * apply wf_middle_inject; [exact Hm_rest | cbn; exact Hsb].
      * assert (Hms : wf_middle (buf6_inject m_rest (StoredSmall8 pre0)))
          by (apply wf_middle_inject; [exact Hm_rest | cbn; exact Hpre0]).
        apply wf_middle_inject; [exact Hms | cbn; exact Hsb].
    + (* sub0 = K8Triple sh sm st: pushed cell pre = sh non-empty *)
      apply andb_prop in Hsrs. destruct Hsrs as [Hsh Hsuf0].
      apply Bool.negb_true_iff in Hsh. apply Bool.negb_true_iff in Hsuf0.
      cbn. split; [exact Hh | split; [exact Hsuf0 |]].
      destruct (buf6_is_empty pre0) eqn:Hpre0; cbn.
      * apply wf_middle_inject; [exact Hm_rest | cbn; exact Hsh].
      * assert (Hms : wf_middle (buf6_inject m_rest (StoredSmall8 pre0)))
          by (apply wf_middle_inject; [exact Hm_rest | cbn; exact Hpre0]).
        apply wf_middle_inject; [exact Hms | cbn; exact Hsh].
Qed.

(** [kcad8_pop_struct] preserves [wf_kcad8_strong]. *)
Lemma kcad8_pop_struct_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    wf_kcad8_strong k ->
    kcad8_pop_struct k = Some (x, k') -> wf_kcad8_strong k'.
Proof.
  intros X k x k' Hwf H.
  destruct k as [|b|h m t]; cbn [kcad8_pop_struct] in H.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|]; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    injection H as Hxv Hk'. subst xv k'.
    destruct (buf6_is_empty b') eqn:He; cbn.
    + exact I.
    + exact He.
  - cbn in Hwf. destruct Hwf as [Hh [Ht Hm]].
    destruct (buf6_pop h) as [[e h']|] eqn:Hpop.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty h') eqn:Hhe.
      * unfold rebalance_after_h_empty in H.
        destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
        -- destruct (stored_sub_left_safe s) eqn:Hsls.
           2: { discriminate H. }
           assert (Hs_wf : wf_stored8 s /\ wf_middle m_rest)
             by (eapply buf6_pop_wf_middle; eauto).
           destruct Hs_wf as [Hsw Hmr].
           destruct s as [b|pre0 sub0 suf0]; cbn in H.
           ++ injection H as Hxv Hk'. subst xv k'.
              eapply (reassemble_after_pop_unfold_wf _ (StoredSmall8 b));
                eauto.
           ++ injection H as Hxv Hk'. subst xv k'.
              eapply (reassemble_after_pop_unfold_wf _ (StoredBig8 pre0 sub0 suf0));
                eauto.
        -- injection H as Hxv Hk'. subst xv k'.
           cbn. unfold kcad8_simple_or_empty.
           destruct (buf6_is_empty t) eqn:Ht'; cbn.
           ++ exact I.
           ++ exact Ht'.
      * injection H as Hxv Hk'. subst xv k'.
        cbn. split; [exact Hhe | split; [exact Ht | exact Hm]].
    + (* buf6_pop h = None — contradicts Hh *)
      exfalso. unfold buf6_pop, buf6_is_empty in *.
      destruct (buf6_elems h); [discriminate Hh|discriminate Hpop].
Qed.

(** [kcad8_pop] preserves [wf_kcad8_strong]. *)
Theorem kcad8_pop_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    wf_kcad8_strong k -> kcad8_pop k = Some (x, k') -> wf_kcad8_strong k'.
Proof.
  intros X k x k' Hwf H.
  unfold kcad8_pop in H.
  destruct (kcad8_pop_struct k) as [[x0 k0]|] eqn:Hstr.
  - injection H as Hx Hk. subst x0 k0.
    eapply kcad8_pop_struct_wf_strong; eauto.
  - destruct (kcad8_to_list k) as [|y ys] eqn:Hlist; [discriminate|].
    injection H as Hx Hk. subst y k'.
    apply kcad8_from_list_wf_strong.
Qed.

(** [kcad8_eject_struct] preserves [wf_kcad8_strong]. *)
Lemma kcad8_eject_struct_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    wf_kcad8_strong k ->
    kcad8_eject_struct k = Some (k', x) -> wf_kcad8_strong k'.
Proof.
  intros X k k' x Hwf H.
  destruct k as [|b|h m t]; cbn [kcad8_eject_struct] in H.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Hej; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    injection H as Hk' Hxv. subst xv k'.
    destruct (buf6_is_empty b') eqn:He; cbn.
    + exact I.
    + exact He.
  - cbn in Hwf. destruct Hwf as [Hh [Ht Hm]].
    destruct (buf6_eject t) as [[t' e]|] eqn:Het.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty t') eqn:Hte.
      * unfold rebalance_after_t_empty in H.
        destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
        -- destruct (stored_sub_right_safe s) eqn:Hsrs.
           2: { discriminate H. }
           assert (Hs_wf : wf_stored8 s /\ wf_middle m_rest)
             by (eapply buf6_eject_wf_middle; eauto).
           destruct Hs_wf as [Hsw Hmr].
           destruct s as [b|pre0 sub0 suf0]; cbn in H.
           ++ (* StoredSmall: stored_sub_right_safe = false — discriminate *)
              discriminate Hsrs.
           ++ injection H as Hk' Hxv. subst xv k'.
              eapply (reassemble_after_eject_unfold_wf _
                       (StoredBig8 pre0 sub0 suf0)); eauto.
        -- injection H as Hk' Hxv. subst xv k'.
           cbn. unfold kcad8_simple_or_empty.
           destruct (buf6_is_empty h) eqn:Hh'; cbn.
           ++ exact I.
           ++ exact Hh'.
      * injection H as Hk' Hxv. subst xv k'.
        cbn. split; [exact Hh | split; [exact Hte | exact Hm]].
    + exfalso. unfold buf6_eject, buf6_is_empty in *.
      destruct (List.rev (buf6_elems t)) eqn:Hrev.
      * (* rev = [] means buf6_elems t = []. *)
        apply (f_equal (@List.rev (KElem8 X))) in Hrev.
        rewrite List.rev_involutive in Hrev. cbn in Hrev.
        rewrite Hrev in Ht. discriminate Ht.
      * discriminate Het.
Qed.

(** [kcad8_eject] preserves [wf_kcad8_strong]. *)
Theorem kcad8_eject_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    wf_kcad8_strong k -> kcad8_eject k = Some (k', x) -> wf_kcad8_strong k'.
Proof.
  intros X k k' x Hwf H.
  unfold kcad8_eject in H.
  destruct (kcad8_eject_struct k) as [[k0 x0]|] eqn:Hstr.
  - injection H as Hk Hx. subst x0 k0.
    eapply kcad8_eject_struct_wf_strong; eauto.
  - destruct (List.rev (kcad8_to_list k)) as [|y ys] eqn:Hrev;
      [discriminate|].
    injection H as Hk Hx. subst y k'.
    apply kcad8_from_list_wf_strong.
Qed.
