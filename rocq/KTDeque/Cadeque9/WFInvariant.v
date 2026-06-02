(** * Module: KTDeque.Cadeque9.WFInvariant

    Boundary-element invariant for the current Cadeque9 extraction.

    [wf_kcad9_strong] carries the size facts needed by the §6
    shape, but it intentionally says nothing about the elements stored
    in boundary buffers.  The executable pop/eject definitions contain
    defensive [XStored9] failure branches for malformed boundaries.
    [inv_kcad9_public] rules those branches out and is the first
    Gate-D totality layer for the extracted fast catenable surface. *)

From Stdlib Require Import Bool List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque9 Require Import Model WFStrong Ops OpsFast.

Definition is_xbase9 {X : Type} (e : KElem9 X) : Prop :=
  match e with
  | XBase9 _ => True
  | XStored9 _ => False
  end.

Definition all_xbase9 {X : Type} (b : Buf6 (KElem9 X)) : Prop :=
  Forall (@is_xbase9 X) (buf6_elems b).

Fixpoint xbase_stored9 {X : Type} (s : Stored9 X) {struct s} : Prop :=
  match s with
  | StoredSmall9 b =>
      all_xbase9 b
  | StoredBig9 pre sm suf =>
      all_xbase9 pre /\
      all_xbase9 suf /\
      (fix go (l : list (Stored9 X)) : Prop :=
         match l with
         | [] => True
         | s' :: ss => xbase_stored9 s' /\ go ss
         end) (buf6_elems sm)
  | StoredMiddle9 _ =>
      False
  end.

Definition xbase_middle9 {X : Type} (m : Buf6 (Stored9 X)) : Prop :=
  Forall (@xbase_stored9 X) (buf6_elems m).

Definition inv_kcad9_public {X : Type} (k : KCadeque9 X) : Prop :=
  match k with
  | K9Empty =>
      True
  | K9Simple b =>
      buf6_size_ge 1 b /\ all_xbase9 b
  | K9Triple h m t =>
      buf6_size_ge 5 h /\
      buf6_size_ge 5 t /\
      all_xbase9 h /\
      all_xbase9 t /\
      wf_middle9 m /\
      xbase_middle9 m
  end.

Lemma inv_kcad9_public_wf_strong :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_public k -> wf_kcad9_strong k.
Proof.
  intros X [|b|h m t] Hinv; cbn in *; auto.
  - destruct Hinv as [Hsize _]. exact Hsize.
  - destruct Hinv as [Hh [Ht [_ [_ [Hmw _]]]]].
    repeat split; assumption.
Qed.

Lemma empty_kcad9_inv_public :
  forall X : Type, inv_kcad9_public (@kcad9_empty X).
Proof. intros X. exact I. Qed.

Lemma singleton_kcad9_inv_public :
  forall (X : Type) (x : X), inv_kcad9_public (kcad9_singleton x).
Proof.
  intros X x. cbn. split.
  - unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - constructor; [exact I | constructor].
Qed.

Lemma xbase_stored9_big_iff :
  forall (X : Type) (pre : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X))
         (suf : Buf6 (KElem9 X)),
    xbase_stored9 (StoredBig9 pre sm suf) <->
    (all_xbase9 pre /\ all_xbase9 suf /\ xbase_middle9 sm).
Proof.
  intros X pre [xs] suf. unfold xbase_middle9, buf6_elems. cbn.
  split.
  - intros [Hpre [Hsuf Hm]].
    repeat split; auto.
    induction xs as [|s ss IH]; cbn in Hm; [constructor|].
    destruct Hm as [Hs Hss]. constructor; auto.
  - intros [Hpre [Hsuf Hm]].
    repeat split; auto.
    induction Hm; cbn; [trivial|]. split; auto.
Qed.

Lemma all_xbase9_push_base :
  forall (X : Type) (x : X) (b : Buf6 (KElem9 X)),
    all_xbase9 b -> all_xbase9 (buf6_push (XBase9 x) b).
Proof.
  intros X x [xs] Hall. unfold all_xbase9, buf6_push, buf6_elems in *.
  constructor; [exact I | exact Hall].
Qed.

Lemma all_xbase9_inject_base :
  forall (X : Type) (b : Buf6 (KElem9 X)) (x : X),
    all_xbase9 b -> all_xbase9 (buf6_inject b (XBase9 x)).
Proof.
  intros X [xs] x Hall. unfold all_xbase9, buf6_inject, buf6_elems in *.
  apply Forall_app. split; [exact Hall | constructor; [exact I | constructor]].
Qed.

Lemma all_xbase9_concat :
  forall (X : Type) (a b : Buf6 (KElem9 X)),
    all_xbase9 a -> all_xbase9 b -> all_xbase9 (buf6_concat a b).
Proof.
  intros X [xs] [ys] Ha Hb.
  unfold all_xbase9, buf6_concat, buf6_elems in *.
  apply Forall_app. split; assumption.
Qed.

Lemma all_xbase9_pop :
  forall (X : Type) (b b' : Buf6 (KElem9 X)) (e : KElem9 X),
    all_xbase9 b ->
    buf6_pop b = Some (e, b') ->
    is_xbase9 e /\ all_xbase9 b'.
Proof.
  intros X b b' e Hall Hpop.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  unfold all_xbase9 in *. rewrite Hpop in Hall.
  inversion Hall; subst. split; assumption.
Qed.

Lemma all_xbase9_eject :
  forall (X : Type) (b b' : Buf6 (KElem9 X)) (e : KElem9 X),
    all_xbase9 b ->
    buf6_eject b = Some (b', e) ->
    all_xbase9 b' /\ is_xbase9 e.
Proof.
  intros X b b' e Hall Heject.
  apply buf6_eject_seq_some in Heject. unfold buf6_to_list in Heject.
  unfold all_xbase9 in *. rewrite Heject in Hall.
  apply Forall_app in Hall. destruct Hall as [Hb' Hlast].
  inversion Hlast; subst. split; assumption.
Qed.

Lemma buf6_pop_xbase9 :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    all_xbase9 b ->
    exists x b', buf6_pop b = Some (XBase9 x, b').
Proof.
  intros X [xs] Hsize Hall.
  unfold buf6_size_ge, buf6_size, all_xbase9, buf6_elems in *.
  destruct xs as [|e es]; [cbn in Hsize; lia|].
  inversion Hall; subst.
  destruct e as [x|s]; [|destruct H1].
  exists x, (mkBuf6 es). reflexivity.
Qed.

Lemma buf6_eject_xbase9 :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    all_xbase9 b ->
    exists b' x, buf6_eject b = Some (b', XBase9 x).
Proof.
  intros X b Hsize Hall.
  destruct (buf6_eject_of_size_ge_S (KElem9 X) 0 b Hsize)
    as [b' [e Heject]].
  destruct (all_xbase9_eject X b b' e Hall Heject) as [_ He].
  destruct e as [x|s]; [|destruct He].
  exists b', x. exact Heject.
Qed.

Lemma buf6_is_empty_false_size_ge_1 :
  forall (X : Type) (b : Buf6 X),
    buf6_is_empty b = false -> buf6_size_ge 1 b.
Proof.
  intros X [xs] H.
  unfold buf6_is_empty, buf6_size_ge, buf6_size, buf6_elems in *.
  destruct xs as [|x xs]; [discriminate|cbn; lia].
Qed.

Lemma xbase_middle9_push :
  forall (X : Type) (s : Stored9 X) (m : Buf6 (Stored9 X)),
    xbase_stored9 s -> xbase_middle9 m -> xbase_middle9 (buf6_push s m).
Proof.
  intros X s [xs] Hs Hm.
  unfold xbase_middle9, buf6_push, buf6_elems in *.
  constructor; auto.
Qed.

Lemma xbase_middle9_inject :
  forall (X : Type) (m : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9 m -> xbase_stored9 s -> xbase_middle9 (buf6_inject m s).
Proof.
  intros X [xs] s Hm Hs.
  unfold xbase_middle9, buf6_inject, buf6_elems in *.
  apply Forall_app. split; [exact Hm | constructor; auto].
Qed.

Lemma xbase_middle9_concat :
  forall (X : Type) (a b : Buf6 (Stored9 X)),
    xbase_middle9 a -> xbase_middle9 b -> xbase_middle9 (buf6_concat a b).
Proof.
  intros X [xs] [ys] Ha Hb.
  unfold xbase_middle9, buf6_concat, buf6_elems in *.
  apply Forall_app. split; assumption.
Qed.

Lemma xbase_middle9_pop :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9 m ->
    buf6_pop m = Some (s, m_rest) ->
    xbase_stored9 s /\ xbase_middle9 m_rest.
Proof.
  intros X m m_rest s Hm Hpop.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  unfold xbase_middle9 in *. rewrite Hpop in Hm.
  inversion Hm; subst. split; assumption.
Qed.

Lemma xbase_middle9_eject :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9 m ->
    buf6_eject m = Some (m_rest, s) ->
    xbase_middle9 m_rest /\ xbase_stored9 s.
Proof.
  intros X m m_rest s Hm Heject.
  apply buf6_eject_seq_some in Heject. unfold buf6_to_list in Heject.
  unfold xbase_middle9 in *. rewrite Heject in Hm.
  apply Forall_app in Hm. destruct Hm as [Hm_rest Hs].
  inversion Hs; subst. split; assumption.
Qed.

Lemma refill_h_K9Triple_inv_public :
  forall (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_size_ge 4 h' ->
    all_xbase9 h' ->
    buf6_size_ge 5 t ->
    all_xbase9 t ->
    wf_middle9 m ->
    xbase_middle9 m ->
    inv_kcad9_public (refill_h_K9Triple h' m t).
Proof.
  intros X h' m t Hh' Hxh' Ht Hxt Hmw Hmx.
  unfold refill_h_K9Triple.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - destruct (wf_middle9_pop X m m_rest cell Hmw Hpop)
      as [Hcell_wf Hm_rest_wf].
    destruct (xbase_middle9_pop X m m_rest cell Hmx Hpop)
      as [Hcell_x Hm_rest_x].
    destruct cell as [b|pre sm suf|sm].
    + cbn in Hcell_wf, Hcell_x |- *.
      repeat split.
      * eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Ht.
      * apply all_xbase9_concat; assumption.
      * exact Hxt.
      * exact Hm_rest_wf.
      * exact Hm_rest_x.
    + apply wf_stored9_big_iff in Hcell_wf.
      apply xbase_stored9_big_iff in Hcell_x.
      destruct Hcell_wf as [Hpre [Hsuf Hsm_wf]].
      destruct Hcell_x as [Hxpre [Hxsuf Hsm_x]].
      cbn [inv_kcad9_public].
      repeat split.
      * eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Ht.
      * apply all_xbase9_concat; assumption.
      * exact Hxt.
      * apply wf_middle9_concat; [exact Hsm_wf|].
        apply wf_middle9_push; [cbn; exact Hsuf|exact Hm_rest_wf].
      * apply xbase_middle9_concat; [exact Hsm_x|].
        apply xbase_middle9_push; [cbn; exact Hxsuf|exact Hm_rest_x].
    + contradiction.
  - cbn [inv_kcad9_public].
    repeat split.
    + eapply buf6_size_ge_weaken with (n := 4); [lia|].
      apply buf6_size_ge_concat_l. exact Hh'.
    + apply all_xbase9_concat; assumption.
Qed.

Lemma refill_t_K9Triple_inv_public :
  forall (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    buf6_size_ge 5 h ->
    all_xbase9 h ->
    buf6_size_ge 4 t' ->
    all_xbase9 t' ->
    wf_middle9 m ->
    xbase_middle9 m ->
    inv_kcad9_public (refill_t_K9Triple h m t').
Proof.
  intros X h m t' Hh Hxh Ht' Hxt' Hmw Hmx.
  unfold refill_t_K9Triple.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
  - destruct (wf_middle9_eject X m m_rest cell Hmw Heject)
      as [Hm_rest_wf Hcell_wf].
    destruct (xbase_middle9_eject X m m_rest cell Hmx Heject)
      as [Hm_rest_x Hcell_x].
    destruct cell as [b|pre sm suf|sm].
    + cbn in Hcell_wf, Hcell_x |- *.
      repeat split.
      * exact Hh.
      * eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Hxh.
      * apply all_xbase9_concat; assumption.
      * exact Hm_rest_wf.
      * exact Hm_rest_x.
    + apply wf_stored9_big_iff in Hcell_wf.
      apply xbase_stored9_big_iff in Hcell_x.
      destruct Hcell_wf as [Hpre [Hsuf Hsm_wf]].
      destruct Hcell_x as [Hxpre [Hxsuf Hsm_x]].
      cbn [inv_kcad9_public].
      repeat split.
      * exact Hh.
      * eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Hxh.
      * apply all_xbase9_concat; assumption.
      * apply wf_middle9_concat.
        -- apply wf_middle9_inject; [exact Hm_rest_wf|cbn; exact Hpre].
        -- exact Hsm_wf.
      * apply xbase_middle9_concat.
        -- apply xbase_middle9_inject; [exact Hm_rest_x|cbn; exact Hxpre].
        -- exact Hsm_x.
    + contradiction.
  - cbn [inv_kcad9_public].
    repeat split.
    + eapply buf6_size_ge_weaken with (n := 5); [lia|].
      apply buf6_size_ge_concat_l. exact Hh.
    + apply all_xbase9_concat; assumption.
Qed.

Theorem kcad9_push_inv_public :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    inv_kcad9_public k -> inv_kcad9_public (kcad9_push x k).
Proof.
  intros X x [|b|h m t] Hinv; cbn [kcad9_push] in *.
  - apply singleton_kcad9_inv_public.
  - destruct Hinv as [Hsize Hx].
    split.
    + apply buf6_size_ge_push_preserve. exact Hsize.
    + apply all_xbase9_push_base. exact Hx.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [Hmw Hmx]]]]].
    repeat split; auto.
    + apply buf6_size_ge_push_preserve. exact Hh.
    + apply all_xbase9_push_base. exact Hxh.
Qed.

Theorem kcad9_inject_inv_public :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    inv_kcad9_public k -> inv_kcad9_public (kcad9_inject k x).
Proof.
  intros X [|b|h m t] x Hinv; cbn [kcad9_inject] in *.
  - apply singleton_kcad9_inv_public.
  - destruct Hinv as [Hsize Hx].
    split.
    + apply buf6_size_ge_inject_preserve. exact Hsize.
    + apply all_xbase9_inject_base. exact Hx.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [Hmw Hmx]]]]].
    repeat split; auto.
    + apply buf6_size_ge_inject_preserve. exact Ht.
    + apply all_xbase9_inject_base. exact Hxt.
Qed.

Theorem kcad9_concat_inv_public :
  forall (X : Type) (a b : KCadeque9 X),
    inv_kcad9_public a ->
    inv_kcad9_public b ->
    inv_kcad9_public (kcad9_concat a b).
Proof.
  intros X [|ba|h1 m1 t1] [|bb|h2 m2 t2] Ha Hb;
    cbn [kcad9_concat] in *; auto.
  - destruct Ha as [Hba Hxba]. destruct Hb as [Hbb Hxbb].
    split.
    + apply buf6_size_ge_concat_l. exact Hba.
    + apply all_xbase9_concat; assumption.
  - destruct Ha as [Hba Hxba].
    destruct Hb as [Hh2 [Ht2 [Hxh2 [Hxt2 [Hm2w Hm2x]]]]].
    repeat split; auto.
    + apply buf6_size_ge_concat_r. exact Hh2.
    + apply all_xbase9_concat; assumption.
  - destruct Ha as [Hh1 [Ht1 [Hxh1 [Hxt1 [Hm1w Hm1x]]]]].
    destruct Hb as [Hbb Hxbb].
    repeat split; auto.
    + apply buf6_size_ge_concat_l. exact Ht1.
    + apply all_xbase9_concat; assumption.
  - destruct Ha as [Hh1 [Ht1 [Hxh1 [Hxt1 [Hm1w Hm1x]]]]].
    destruct Hb as [Hh2 [Ht2 [Hxh2 [Hxt2 [Hm2w Hm2x]]]]].
    repeat split; auto.
    + apply wf_middle9_concat.
      * apply wf_middle9_inject; [exact Hm1w|].
        cbn. eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Hm2w.
    + apply xbase_middle9_concat.
      * apply xbase_middle9_inject; [exact Hm1x|].
        cbn. apply all_xbase9_concat; assumption.
      * exact Hm2x.
Qed.

Theorem kcad9_pop_inv_public :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    inv_kcad9_public k ->
    kcad9_pop k = Some (x, k') ->
    inv_kcad9_public k'.
Proof.
  intros X [|b|h m t] x k' Hinv Hpop; cbn [kcad9_pop] in Hpop.
  - discriminate.
  - destruct Hinv as [_ Hxb].
    destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct (all_xbase9_pop X b b' e Hxb Hpb) as [He Hb'x].
    destruct e as [xv|sv]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k'; cbn [inv_kcad9_public]; auto.
    split.
    + apply buf6_is_empty_false_size_ge_1. exact Hempty.
    + exact Hb'x.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [Hmw Hmx]]]]].
    destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct (all_xbase9_pop X h h' e Hxh Hph) as [He Hh'x].
    destruct e as [xv|sv]; [|destruct He].
    assert (Hh'4 : buf6_size_ge 4 h').
    { unfold buf6_size_ge in Hh |- *.
      apply buf6_pop_size_some in Hph. lia. }
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'; cbn [inv_kcad9_public].
    + apply PeanoNat.Nat.leb_le in Hcmp.
      repeat split.
      * unfold buf6_size_ge. exact Hcmp.
      * exact Ht.
      * exact Hh'x.
      * exact Hxt.
      * exact Hmw.
      * exact Hmx.
    + apply refill_h_K9Triple_inv_public; assumption.
Qed.

Theorem kcad9_eject_inv_public :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    kcad9_eject k = Some (k', x) ->
    inv_kcad9_public k'.
Proof.
  intros X [|b|h m t] k' x Hinv Heject; cbn [kcad9_eject] in Heject.
  - discriminate.
  - destruct Hinv as [_ Hxb].
    destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct (all_xbase9_eject X b b' e Hxb Heb) as [Hb'x He].
    destruct e as [xv|sv]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k'; cbn [inv_kcad9_public]; auto.
    split.
    + apply buf6_is_empty_false_size_ge_1. exact Hempty.
    + exact Hb'x.
  - destruct Hinv as [Hh [Ht [Hxh [Hxt [Hmw Hmx]]]]].
    destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct (all_xbase9_eject X t t' e Hxt Het) as [Ht'x He].
    destruct e as [xv|sv]; [|destruct He].
    assert (Ht'4 : buf6_size_ge 4 t').
    { unfold buf6_size_ge in Ht |- *.
      apply buf6_eject_size_some in Het. lia. }
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'; cbn [inv_kcad9_public].
    + apply PeanoNat.Nat.leb_le in Hcmp.
      repeat split.
      * exact Hh.
      * unfold buf6_size_ge. exact Hcmp.
      * exact Hxh.
      * exact Ht'x.
      * exact Hmw.
      * exact Hmx.
    + apply refill_t_K9Triple_inv_public; assumption.
Qed.

Theorem kcad9_pop_total_under_inv_public :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_public k ->
    k <> K9Empty ->
    exists x k', kcad9_pop k = Some (x, k').
Proof.
  intros X [|b|h m t] Hinv Hne; [contradiction Hne; reflexivity| |].
  - destruct Hinv as [Hb Hxb].
    destruct (buf6_pop_xbase9 X b Hb Hxb) as [x [b' Hpop]].
    cbn [kcad9_pop]. rewrite Hpop.
    destruct (buf6_is_empty b'); eexists; eexists; reflexivity.
  - destruct Hinv as [Hh [_ [Hxh _]]].
    assert (Hh1 : buf6_size_ge 1 h).
    { eapply buf6_size_ge_weaken; [|exact Hh]. lia. }
    destruct (buf6_pop_xbase9 X h Hh1 Hxh) as [x [h' Hpop]].
    cbn [kcad9_pop]. rewrite Hpop.
    destruct (Nat.leb 5 (buf6_size h')); eexists; eexists; reflexivity.
Qed.

Theorem kcad9_eject_total_under_inv_public :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_public k ->
    k <> K9Empty ->
    exists k' x, kcad9_eject k = Some (k', x).
Proof.
  intros X [|b|h m t] Hinv Hne; [contradiction Hne; reflexivity| |].
  - destruct Hinv as [Hb Hxb].
    destruct (buf6_eject_xbase9 X b Hb Hxb) as [b' [x Heject]].
    cbn [kcad9_eject]. rewrite Heject.
    destruct (buf6_is_empty b'); eexists; eexists; reflexivity.
  - destruct Hinv as [_ [Ht [_ [Hxt _]]]].
    assert (Ht1 : buf6_size_ge 1 t).
    { eapply buf6_size_ge_weaken; [|exact Ht]. lia. }
    destruct (buf6_eject_xbase9 X t Ht1 Hxt) as [t' [x Heject]].
    cbn [kcad9_eject]. rewrite Heject.
    destruct (Nat.leb 5 (buf6_size t')); eexists; eexists; reflexivity.
Qed.

Theorem kcad9_push_fast_inv_public :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    inv_kcad9_public k -> inv_kcad9_public (kcad9_push_fast x k).
Proof. apply kcad9_push_inv_public. Qed.

Theorem kcad9_inject_fast_inv_public :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    inv_kcad9_public k -> inv_kcad9_public (kcad9_inject_fast k x).
Proof. apply kcad9_inject_inv_public. Qed.

Theorem kcad9_concat_fast_inv_public :
  forall (X : Type) (a b : KCadeque9 X),
    inv_kcad9_public a ->
    inv_kcad9_public b ->
    inv_kcad9_public (kcad9_concat_fast a b).
Proof. apply kcad9_concat_inv_public. Qed.

Theorem kcad9_pop_fast_inv_public :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    inv_kcad9_public k ->
    kcad9_pop_fast k = PopOk9 x k' ->
    inv_kcad9_public k'.
Proof.
  intros X k x k' Hinv Hpop.
  unfold kcad9_pop_fast in Hpop.
  destruct (kcad9_pop k) as [[y k'']|] eqn:Hp; cbn in Hpop; [|discriminate].
  injection Hpop as Hx Hk. subst y k''.
  eapply kcad9_pop_inv_public; eauto.
Qed.

Theorem kcad9_eject_fast_inv_public :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    inv_kcad9_public k ->
    kcad9_eject_fast k = EjectOk9 k' x ->
    inv_kcad9_public k'.
Proof.
  intros X k k' x Hinv Heject.
  unfold kcad9_eject_fast in Heject.
  destruct (kcad9_eject k) as [[k'' y]|] eqn:He; cbn in Heject;
    [|discriminate].
  injection Heject as Hk Hx. subst y k''.
  eapply kcad9_eject_inv_public; eauto.
Qed.

Theorem kcad9_pop_fast_total_under_inv_public :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_public k ->
    k <> K9Empty ->
    exists x k', kcad9_pop_fast k = PopOk9 x k'.
Proof.
  intros X k Hinv Hne.
  destruct (kcad9_pop_total_under_inv_public X k Hinv Hne) as [x [k' Hpop]].
  exists x, k'. unfold kcad9_pop_fast. rewrite Hpop. reflexivity.
Qed.

Theorem kcad9_eject_fast_total_under_inv_public :
  forall (X : Type) (k : KCadeque9 X),
    inv_kcad9_public k ->
    k <> K9Empty ->
    exists k' x, kcad9_eject_fast k = EjectOk9 k' x.
Proof.
  intros X k Hinv Hne.
  destruct (kcad9_eject_total_under_inv_public X k Hinv Hne) as [k' [x Heject]].
  exists k', x. unfold kcad9_eject_fast. rewrite Heject. reflexivity.
Qed.
