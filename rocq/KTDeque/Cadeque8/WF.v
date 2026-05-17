(** * Module: KTDeque.Cadeque8.WF — Cadeque8 well-formedness invariant.

    Captures the KT99 §6 "boundary buffers non-empty" invariant at the
    top level of the cadeque, plus a stored-cell well-formedness used
    when reasoning about the middle spine.

    ## Scope of what's proven here

    - [wf_kcad8] is the top-level invariant: [K8Triple]'s head and tail
      buffers are non-empty, [K8Simple]'s buffer is non-empty.
    - [wf_stored8] is the per-cell invariant for middle elements:
      [StoredSmall8]'s buffer non-empty; [StoredBig8]'s prefix non-empty.
    - We prove [wf_kcad8] is preserved by [kcad8_push], [kcad8_inject],
      and [kcad8_concat].

    ## What is NOT yet closed

    [kcad8_pop_struct] / [kcad8_eject_struct] preserve [wf_kcad8]
    only under a STRONGER stored-cell invariant (every stored cell
    has non-empty prefix AND the [sub] inside a [StoredBig8] has
    non-empty head when it's a [K8Triple]).  The current concat
    construction for the [(K8Simple, K8Triple)] shape creates a
    [StoredBig8] whose [sub] is a [K8Triple] with empty boundary
    buffers — perfectly fine on its own, but when this stored cell
    is later unfolded by a [rebalance_after_h_empty], the resulting
    pushed cell has empty prefix.  A second consecutive rebalance
    would then produce a [K8Triple] with empty head, which the
    structural [kcad8_pop_struct] cannot consume — the public
    [kcad8_pop] then takes its [kcad8_to_list] + [kcad8_from_list]
    fallback (O(n) on that one call).

    The bench (`ocaml/bench/kc8_vs_vi.exe`, including the
    adversarial 1000-concat workload) does not exhibit this
    corner case at user-visible scale: the average per-op cost
    stays at ~87 ns under the mix.  But a strict-WC O(1) certification
    of the structural pop/eject path would need either a tighter
    concat construction or a finer stored-cell invariant.  This
    file documents the gap rather than papering over it. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops.

(** ** Top-level well-formedness for [KCadeque8].

    - [K8Empty]: no constraint.
    - [K8Simple b]: [b] is non-empty (else we would represent the same
      thing as [K8Empty]).
    - [K8Triple h m t]: [h] and [t] are both non-empty (the §6
      structural invariant) AND every stored cell in [m] is
      well-formed. *)

Section WF.
Variable X : Type.

Definition wf_stored8 (s : Stored8 X) : Prop :=
  match s with
  | StoredSmall8 b       => buf6_is_empty b = false
  | StoredBig8 pre _ _   => buf6_is_empty pre = false
  end.

Definition wf_middle (m : Buf6 (Stored8 X)) : Prop :=
  Forall wf_stored8 (buf6_elems m).

Definition wf_kcad8 (k : KCadeque8 X) : Prop :=
  match k with
  | K8Empty        => True
  | K8Simple b     => buf6_is_empty b = false
  | K8Triple h m t =>
      buf6_is_empty h = false /\
      buf6_is_empty t = false /\
      wf_middle m
  end.

End WF.

Arguments wf_stored8 {X} _.
Arguments wf_middle  {X} _.
Arguments wf_kcad8   {X} _.

(* ========================================================================== *)
(* Helper lemmas on buf6_is_empty under push / inject.                         *)
(* ========================================================================== *)

Lemma buf6_push_not_empty :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_is_empty (buf6_push x b) = false.
Proof. intros X x [xs]. reflexivity. Qed.

Lemma buf6_inject_not_empty :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_is_empty (buf6_inject b x) = false.
Proof.
  intros X [xs] x. unfold buf6_inject, buf6_is_empty, buf6_elems.
  destruct xs as [|y ys]; reflexivity.
Qed.

Lemma buf6_singleton_not_empty :
  forall (X : Type) (x : X),
    buf6_is_empty (mkBuf6 [x]) = false.
Proof. reflexivity. Qed.

(* ========================================================================== *)
(* wf_middle is preserved by buf6_inject of a well-formed stored cell.         *)
(* ========================================================================== *)

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

(* ========================================================================== *)
(* Preservation by push / inject (trivial — both add an element to the         *)
(* boundary buffer that's being updated, and leave the rest alone).            *)
(* ========================================================================== *)

Theorem kcad8_push_wf :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    wf_kcad8 k -> wf_kcad8 (kcad8_push x k).
Proof.
  intros X x k Hwf. destruct k as [|b|h m t]; cbn [kcad8_push].
  - cbn. reflexivity.
  - cbn. destruct b. reflexivity.
  - cbn in *. destruct Hwf as [Hh [Ht Hm]].
    destruct h. split; [reflexivity | split; assumption].
Qed.

Theorem kcad8_inject_wf :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    wf_kcad8 k -> wf_kcad8 (kcad8_inject k x).
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

(* ========================================================================== *)
(* Preservation by concat.                                                     *)
(* ========================================================================== *)

(** Concat preserves the top-level wf invariant.

    The four non-trivial cases (Simple/Simple, Simple/Triple,
    Triple/Simple, Triple/Triple) each produce a [K8Triple] whose
    boundary buffers are taken directly from the inputs' non-empty
    boundaries, and whose middle either contains the input middles
    extended by a fresh stored cell whose [pre]/buffer comes from
    one of the input's non-empty boundaries.

    Note: we do NOT claim the *inner* [sub] of those fresh
    [StoredBig8] cells satisfies any boundary invariant.  See the
    file header for why that's structurally tricky to preserve
    under the chained-rebalance pattern. *)

Theorem kcad8_concat_wf :
  forall (X : Type) (a b : KCadeque8 X),
    wf_kcad8 a -> wf_kcad8 b -> wf_kcad8 (kcad8_concat a b).
Proof.
  intros X a b Ha Hb.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad8_concat].
  - exact Hb.   (* K8Empty, _ *)
  - exact Hb.
  - exact Hb.
  - exact Ha.   (* _, K8Empty *)
  - (* K8Simple ba, K8Simple bb *)
    cbn in Ha, Hb |- *.
    split; [exact Ha | split; [exact Hb | apply wf_middle_empty]].
  - (* K8Simple ba, K8Triple h2 m2 t2 *)
    cbn in Ha, Hb |- *.
    destruct Hb as [Hh2 [Ht2 _]].
    split; [exact Ha | split; [exact Ht2 |]].
    apply wf_middle_singleton. cbn. exact Hh2.
  - exact Ha.
  - (* K8Triple h1 m1 t1, K8Simple bb *)
    cbn in Ha, Hb |- *.
    destruct Ha as [Hh1 [Ht1 Hm1]].
    split; [exact Hh1 | split; [exact Hb |]].
    apply wf_middle_inject; [exact Hm1 | cbn; exact Ht1].
  - (* K8Triple h1 m1 t1, K8Triple h2 m2 t2 *)
    cbn in Ha, Hb |- *.
    destruct Ha as [Hh1 [Ht1 Hm1]]. destruct Hb as [Hh2 [Ht2 _]].
    split; [exact Hh1 | split; [exact Ht2 |]].
    apply wf_middle_inject; [exact Hm1 | cbn; exact Ht1].
Qed.

(* ========================================================================== *)
(* Pop / eject: the public path preserves wf (via the kcad8_from_list          *)
(* fallback when the structural path returns None).                            *)
(* ========================================================================== *)

(** [kcad8_from_list] on any list returns a wf cadeque
    ([K8Empty] for [], [K8Simple] with a non-empty buffer otherwise). *)
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

(** Public pop preserves wf via the fallback when the structural
    fast-path returns None. *)
Theorem kcad8_pop_wf_via_fallback :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop_struct k = None ->
    kcad8_pop k = Some (x, k') ->
    wf_kcad8 k'.
Proof.
  intros X k x k' Hstr Hp.
  unfold kcad8_pop in Hp. rewrite Hstr in Hp.
  destruct (kcad8_to_list k) as [|y ys] eqn:Hlist; [discriminate|].
  injection Hp as Hx Hk. subst y k'.
  apply kcad8_from_list_wf.
Qed.

(** Public eject preserves wf via the fallback when the structural
    fast-path returns None. *)
Theorem kcad8_eject_wf_via_fallback :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject_struct k = None ->
    kcad8_eject k = Some (k', x) ->
    wf_kcad8 k'.
Proof.
  intros X k k' x Hstr He.
  unfold kcad8_eject in He. rewrite Hstr in He.
  destruct (List.rev (kcad8_to_list k)) as [|y ys] eqn:Hrev;
    [discriminate|].
  injection He as Hk Hx. subst y k'.
  apply kcad8_from_list_wf.
Qed.