(** * Module: KTDeque.Cadeque9.Normalize

    Sequence contract for the hand-edited OCaml KCadeque9 normalizers.

    The OCaml implementation uses mutually recursive [k9_with_front] /
    [k9_with_back] helpers to restore a non-empty boundary by exposing
    constant-shape stored middle cells.  This file models the same equations
    with an explicit fuel parameter.  The fuel is a proof device: the theorem
    below says every finite unfolding preserves the list semantics.  The Gate-D
    cost obligation is still to prove the production invariant that supplies a
    constant fuel bound for the reachable OCaml states. *)

From Stdlib Require Import List Lia PeanoNat.
Import ListNotations.

From KTDeque.Buffer6  Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque9 Require Import Model Ops WFInvariant.

Definition inv_kcad9_ocaml_boundaries {X : Type} (k : KCadeque9 X) : Prop :=
  match k with
  | K9Empty => True
  | K9Simple b => buf6_size_ge 1 b
  | K9Triple h _ t => buf6_size_ge 1 h /\ buf6_size_ge 1 t
  end.

Fixpoint xbase_stored9_deep {X : Type} (s : Stored9 X) {struct s} : Prop :=
  match s with
  | StoredSmall9 b =>
      all_xbase9 b
  | StoredBig9 pre sm suf =>
      all_xbase9 pre /\
      all_xbase9 suf /\
      (fix go (l : list (Stored9 X)) : Prop :=
         match l with
         | [] => True
         | s' :: ss => xbase_stored9_deep s' /\ go ss
         end) (buf6_elems sm)
  | StoredMiddle9 sm =>
      (fix go (l : list (Stored9 X)) : Prop :=
         match l with
         | [] => True
         | s' :: ss => xbase_stored9_deep s' /\ go ss
         end) (buf6_elems sm)
  end.

Definition xbase_middle9_deep {X : Type} (m : Buf6 (Stored9 X)) : Prop :=
  Forall (@xbase_stored9_deep X) (buf6_elems m).

Definition inv_kcad9_ocaml_deep_xbase {X : Type} (k : KCadeque9 X) : Prop :=
  match k with
  | K9Empty => True
  | K9Simple b => all_xbase9 b
  | K9Triple h m t =>
      all_xbase9 h /\ xbase_middle9_deep m /\ all_xbase9 t
  end.

Lemma all_xbase9_empty :
  forall X : Type, all_xbase9 (@buf6_empty (KElem9 X)).
Proof. intros X. unfold all_xbase9, buf6_empty, buf6_elems. constructor. Qed.

Lemma xbase_stored9_deep_list_iff :
  forall (X : Type) (xs : list (Stored9 X)),
    (fix go (l : list (Stored9 X)) : Prop :=
       match l with
       | [] => True
       | s' :: ss => xbase_stored9_deep s' /\ go ss
       end) xs <->
    Forall (@xbase_stored9_deep X) xs.
Proof.
  intros X xs. induction xs as [|s ss IH]; cbn.
  - split; intros _; constructor.
  - split.
    + intros [Hs Hss]. constructor; [exact Hs|].
      apply IH. exact Hss.
    + intros Hall. inversion Hall; subst.
      split; [assumption|].
      apply IH. assumption.
Qed.

Lemma xbase_stored9_deep_big_iff :
  forall (X : Type) (pre : Buf6 (KElem9 X))
         (sm : Buf6 (Stored9 X)) (suf : Buf6 (KElem9 X)),
    xbase_stored9_deep (StoredBig9 pre sm suf) <->
    (all_xbase9 pre /\ all_xbase9 suf /\ xbase_middle9_deep sm).
Proof.
  intros X pre [xs] suf.
  unfold xbase_middle9_deep, buf6_elems.
  cbn [xbase_stored9_deep].
  rewrite xbase_stored9_deep_list_iff.
  reflexivity.
Qed.

Lemma xbase_stored9_deep_middle_iff :
  forall (X : Type) (sm : Buf6 (Stored9 X)),
    xbase_stored9_deep (StoredMiddle9 sm) <->
    xbase_middle9_deep sm.
Proof.
  intros X [xs].
  unfold xbase_middle9_deep, buf6_elems.
  cbn [xbase_stored9_deep].
  rewrite xbase_stored9_deep_list_iff.
  reflexivity.
Qed.

Lemma xbase_stored9_deep_big :
  forall (X : Type) (pre : Buf6 (KElem9 X))
         (sm : Buf6 (Stored9 X)) (suf : Buf6 (KElem9 X)),
    all_xbase9 pre ->
    xbase_middle9_deep sm ->
    all_xbase9 suf ->
    xbase_stored9_deep (StoredBig9 pre sm suf).
Proof.
  intros X pre sm suf Hpre Hsm Hsuf.
  apply xbase_stored9_deep_big_iff.
  repeat split; assumption.
Qed.

Lemma xbase_stored9_deep_middle :
  forall (X : Type) (sm : Buf6 (Stored9 X)),
    xbase_middle9_deep sm ->
    xbase_stored9_deep (StoredMiddle9 sm).
Proof.
  intros X sm Hsm. apply xbase_stored9_deep_middle_iff. exact Hsm.
Qed.

Lemma xbase_middle9_deep_empty :
  forall X : Type, xbase_middle9_deep (@buf6_empty (Stored9 X)).
Proof. intros X. unfold xbase_middle9_deep, buf6_empty, buf6_elems. constructor. Qed.

Lemma xbase_middle9_deep_push :
  forall (X : Type) (s : Stored9 X) (m : Buf6 (Stored9 X)),
    xbase_stored9_deep s ->
    xbase_middle9_deep m ->
    xbase_middle9_deep (buf6_push s m).
Proof.
  intros X s [xs] Hs Hm.
  unfold xbase_middle9_deep, buf6_push, buf6_elems in *.
  constructor; assumption.
Qed.

Lemma xbase_middle9_deep_inject :
  forall (X : Type) (m : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9_deep m ->
    xbase_stored9_deep s ->
    xbase_middle9_deep (buf6_inject m s).
Proof.
  intros X [xs] s Hm Hs.
  unfold xbase_middle9_deep, buf6_inject, buf6_elems in *.
  apply Forall_app. split; [exact Hm|].
  constructor; [exact Hs|constructor].
Qed.

Lemma xbase_middle9_deep_pop :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9_deep m ->
    buf6_pop m = Some (s, m_rest) ->
    xbase_stored9_deep s /\ xbase_middle9_deep m_rest.
Proof.
  intros X m m_rest s Hm Hpop.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  unfold xbase_middle9_deep in *. rewrite Hpop in Hm.
  inversion Hm; subst. split; assumption.
Qed.

Lemma xbase_middle9_deep_eject :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    xbase_middle9_deep m ->
    buf6_eject m = Some (m_rest, s) ->
    xbase_middle9_deep m_rest /\ xbase_stored9_deep s.
Proof.
  intros X m m_rest s Hm Heject.
  apply buf6_eject_seq_some in Heject. unfold buf6_to_list in Heject.
  unfold xbase_middle9_deep in *. rewrite Heject in Hm.
  apply Forall_app in Hm. destruct Hm as [Hm_rest Hs].
  inversion Hs; subst. split; assumption.
Qed.

Lemma xbase_middle9_deep_k9_middle_push :
  forall (X : Type) (sm rest : Buf6 (Stored9 X)),
    xbase_middle9_deep sm ->
    xbase_middle9_deep rest ->
    xbase_middle9_deep (k9_middle_push sm rest).
Proof.
  intros X sm rest Hsm Hrest.
  unfold k9_middle_push.
  destruct (buf6_is_empty sm).
  - exact Hrest.
  - apply xbase_middle9_deep_push; [|exact Hrest].
    apply xbase_stored9_deep_middle. exact Hsm.
Qed.

Lemma xbase_middle9_deep_k9_middle_inject :
  forall (X : Type) (rest sm : Buf6 (Stored9 X)),
    xbase_middle9_deep rest ->
    xbase_middle9_deep sm ->
    xbase_middle9_deep (k9_middle_inject rest sm).
Proof.
  intros X rest sm Hrest Hsm.
  unfold k9_middle_inject.
  destruct (buf6_is_empty sm).
  - exact Hrest.
  - apply xbase_middle9_deep_inject; [exact Hrest|].
    apply xbase_stored9_deep_middle. exact Hsm.
Qed.

Definition front_ready_stored9 {X : Type} (s : Stored9 X) : Prop :=
  match s with
  | StoredSmall9 b => buf6_size_ge 1 b
  | StoredBig9 pre _ _ => buf6_size_ge 1 pre
  | StoredMiddle9 _ => False
  end.

Definition back_ready_stored9 {X : Type} (s : Stored9 X) : Prop :=
  match s with
  | StoredSmall9 b => buf6_size_ge 1 b
  | StoredBig9 _ _ suf => buf6_size_ge 1 suf
  | StoredMiddle9 _ => False
  end.

Fixpoint front_ready_stored9_depth {X : Type}
  (depth : nat) (s : Stored9 X) {struct depth} : Prop :=
  match depth with
  | O => front_ready_stored9 s
  | S depth' =>
      match s with
      | StoredSmall9 b => buf6_size_ge 1 b
      | StoredBig9 pre _ _ => buf6_size_ge 1 pre
      | StoredMiddle9 sm =>
          exists front_cell sm_rest,
            buf6_pop sm = Some (front_cell, sm_rest) /\
            front_ready_stored9_depth depth' front_cell
      end
  end.

Fixpoint back_ready_stored9_depth {X : Type}
  (depth : nat) (s : Stored9 X) {struct depth} : Prop :=
  match depth with
  | O => back_ready_stored9 s
  | S depth' =>
      match s with
      | StoredSmall9 b => buf6_size_ge 1 b
      | StoredBig9 _ _ suf => buf6_size_ge 1 suf
      | StoredMiddle9 sm =>
          exists sm_rest back_cell,
            buf6_eject sm = Some (sm_rest, back_cell) /\
            back_ready_stored9_depth depth' back_cell
      end
  end.

Definition front_ready_middle9_depth {X : Type}
  (depth : nat) (m : Buf6 (Stored9 X)) : Prop :=
  exists cell m_rest,
    buf6_pop m = Some (cell, m_rest) /\
    front_ready_stored9_depth depth cell.

Definition back_ready_middle9_depth {X : Type}
  (depth : nat) (m : Buf6 (Stored9 X)) : Prop :=
  exists m_rest cell,
    buf6_eject m = Some (m_rest, cell) /\
    back_ready_stored9_depth depth cell.

Definition front_ready_or_empty_middle9_depth {X : Type}
  (depth : nat) (m : Buf6 (Stored9 X)) : Prop :=
  buf6_pop m = None \/ front_ready_middle9_depth depth m.

Definition back_ready_or_empty_middle9_depth {X : Type}
  (depth : nat) (m : Buf6 (Stored9 X)) : Prop :=
  buf6_eject m = None \/ back_ready_middle9_depth depth m.

Theorem stored_middle9_front_ready_depth :
  forall (depth : nat) (X : Type) (sm : Buf6 (Stored9 X)),
    front_ready_middle9_depth depth sm ->
    front_ready_stored9_depth (S depth) (StoredMiddle9 sm).
Proof.
  intros depth X sm (front_cell & sm_rest & Hpop & Hready).
  cbn. exists front_cell, sm_rest. split; assumption.
Qed.

Theorem stored_middle9_back_ready_depth :
  forall (depth : nat) (X : Type) (sm : Buf6 (Stored9 X)),
    back_ready_middle9_depth depth sm ->
    back_ready_stored9_depth (S depth) (StoredMiddle9 sm).
Proof.
  intros depth X sm (sm_rest & back_cell & Heject & Hready).
  cbn. exists sm_rest, back_cell. split; assumption.
Qed.

Theorem buf6_push_front_ready_stored9_depth :
  forall (depth : nat) (X : Type) (cell : Stored9 X)
         (rest : Buf6 (Stored9 X)),
    front_ready_stored9_depth depth cell ->
    front_ready_middle9_depth depth (buf6_push cell rest).
Proof.
  intros depth X cell rest Hready.
  exists cell, rest. split; [apply buf6_pop_push|exact Hready].
Qed.

Theorem buf6_inject_back_ready_stored9_depth :
  forall (depth : nat) (X : Type) (rest : Buf6 (Stored9 X))
         (cell : Stored9 X),
    back_ready_stored9_depth depth cell ->
    back_ready_middle9_depth depth (buf6_inject rest cell).
Proof.
  intros depth X rest cell Hready.
  exists rest, cell. split; [apply buf6_eject_inject|exact Hready].
Qed.

Theorem front_ready_stored9_depth_succ :
  forall (depth : nat) (X : Type) (s : Stored9 X),
    front_ready_stored9_depth depth s ->
    front_ready_stored9_depth (S depth) s.
Proof.
  induction depth as [|depth IH]; intros X [b|pre sm suf|sm] Hready;
    cbn [front_ready_stored9_depth front_ready_stored9] in *;
    try exact Hready; try contradiction.
  destruct Hready as (front_cell & sm_rest & Hpop & Hcell).
  exists front_cell, sm_rest. split; [exact Hpop|].
  apply IH. exact Hcell.
Qed.

Theorem back_ready_stored9_depth_succ :
  forall (depth : nat) (X : Type) (s : Stored9 X),
    back_ready_stored9_depth depth s ->
    back_ready_stored9_depth (S depth) s.
Proof.
  induction depth as [|depth IH]; intros X [b|pre sm suf|sm] Hready;
    cbn [back_ready_stored9_depth back_ready_stored9] in *;
    try exact Hready; try contradiction.
  destruct Hready as (sm_rest & back_cell & Heject & Hcell).
  exists sm_rest, back_cell. split; [exact Heject|].
  apply IH. exact Hcell.
Qed.

Theorem front_ready_middle9_depth_succ :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X)),
    front_ready_middle9_depth depth m ->
    front_ready_middle9_depth (S depth) m.
Proof.
  intros depth X m (cell & m_rest & Hpop & Hready).
  exists cell, m_rest. split; [exact Hpop|].
  apply front_ready_stored9_depth_succ. exact Hready.
Qed.

Theorem back_ready_middle9_depth_succ :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X)),
    back_ready_middle9_depth depth m ->
    back_ready_middle9_depth (S depth) m.
Proof.
  intros depth X m (m_rest & cell & Heject & Hready).
  exists m_rest, cell. split; [exact Heject|].
  apply back_ready_stored9_depth_succ. exact Hready.
Qed.

Theorem front_ready_or_empty_middle9_depth_succ :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X)),
    front_ready_or_empty_middle9_depth depth m ->
    front_ready_or_empty_middle9_depth (S depth) m.
Proof.
  intros depth X m [Hempty|Hready].
  - left. exact Hempty.
  - right. apply front_ready_middle9_depth_succ. exact Hready.
Qed.

Theorem back_ready_or_empty_middle9_depth_succ :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X)),
    back_ready_or_empty_middle9_depth depth m ->
    back_ready_or_empty_middle9_depth (S depth) m.
Proof.
  intros depth X m [Hempty|Hready].
  - left. exact Hempty.
  - right. apply back_ready_middle9_depth_succ. exact Hready.
Qed.

Theorem front_ready_stored9_depth_small :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    front_ready_stored9_depth depth (StoredSmall9 b).
Proof.
  intros [|depth] X b Hsize; cbn [front_ready_stored9_depth front_ready_stored9];
    exact Hsize.
Qed.

Theorem back_ready_stored9_depth_small :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    back_ready_stored9_depth depth (StoredSmall9 b).
Proof.
  intros [|depth] X b Hsize; cbn [back_ready_stored9_depth back_ready_stored9];
    exact Hsize.
Qed.

Theorem front_ready_stored9_depth_big :
  forall (depth : nat) (X : Type)
         (pre suf : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X)),
    buf6_size_ge 1 pre ->
    front_ready_stored9_depth depth (StoredBig9 pre sm suf).
Proof.
  intros [|depth] X pre suf sm Hsize;
    cbn [front_ready_stored9_depth front_ready_stored9]; exact Hsize.
Qed.

Theorem back_ready_stored9_depth_big :
  forall (depth : nat) (X : Type)
         (pre suf : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X)),
    buf6_size_ge 1 suf ->
    back_ready_stored9_depth depth (StoredBig9 pre sm suf).
Proof.
  intros [|depth] X pre suf sm Hsize;
    cbn [back_ready_stored9_depth back_ready_stored9]; exact Hsize.
Qed.

Theorem front_ready_middle9_depth_inject_preserve :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X))
         (cell : Stored9 X),
    front_ready_middle9_depth depth m ->
    front_ready_middle9_depth depth (buf6_inject m cell).
Proof.
  intros depth X [xs] cell (front_cell & m_rest & Hpop & Hready).
  destruct xs as [|x xs].
  - cbn [front_ready_middle9_depth buf6_pop buf6_elems] in Hpop.
    discriminate.
  - cbn [buf6_pop buf6_elems] in Hpop.
    injection Hpop as Hfront Hrest. subst front_cell m_rest.
    exists x, (mkBuf6 (xs ++ [cell])).
    cbn [buf6_inject buf6_pop buf6_elems].
    split; [reflexivity|exact Hready].
Qed.

Theorem front_ready_middle9_depth_k9_middle_inject_preserve :
  forall (depth : nat) (X : Type) (m sm : Buf6 (Stored9 X)),
    front_ready_middle9_depth depth m ->
    front_ready_middle9_depth depth (k9_middle_inject m sm).
Proof.
  intros depth X m sm Hready.
  unfold k9_middle_inject.
  destruct (buf6_is_empty sm).
  - exact Hready.
  - apply front_ready_middle9_depth_inject_preserve. exact Hready.
Qed.

Lemma buf6_eject_push_some :
  forall (X : Type) (cell : X) (m rest : Buf6 X) (last : X),
    buf6_eject m = Some (rest, last) ->
    buf6_eject (buf6_push cell m) = Some (buf6_push cell rest, last).
Proof.
  intros X cell [xs] rest last Heject.
  unfold buf6_eject, buf6_push, buf6_elems in *.
  remember (rev xs) as r eqn:Hr. symmetry in Hr.
  destruct r as [|y ys]; [discriminate|].
  injection Heject as Hrest Hlast. subst rest last.
  cbn [rev]. rewrite Hr. cbn.
  rewrite rev_app_distr. reflexivity.
Qed.

Theorem back_ready_middle9_depth_push_preserve :
  forall (depth : nat) (X : Type) (cell : Stored9 X)
         (m : Buf6 (Stored9 X)),
    back_ready_middle9_depth depth m ->
    back_ready_middle9_depth depth (buf6_push cell m).
Proof.
  intros depth X cell m (m_rest & back_cell & Heject & Hready).
  exists (buf6_push cell m_rest), back_cell.
  split; [eapply buf6_eject_push_some; exact Heject|exact Hready].
Qed.

Theorem front_ready_middle9_depth_inject_or_ready :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X))
         (cell : Stored9 X),
    front_ready_or_empty_middle9_depth depth m ->
    front_ready_stored9_depth depth cell ->
    front_ready_middle9_depth depth (buf6_inject m cell).
Proof.
  intros depth X m cell [Hempty|Hready] Hcell.
  - apply buf6_pop_seq_none in Hempty.
    unfold buf6_to_list in Hempty.
    destruct m as [xs]. cbn [buf6_elems] in Hempty. subst xs.
    exists cell, buf6_empty.
    cbn [buf6_inject buf6_pop buf6_empty buf6_elems].
    split; [reflexivity|exact Hcell].
  - apply front_ready_middle9_depth_inject_preserve. exact Hready.
Qed.

Theorem back_ready_middle9_depth_push_or_ready :
  forall (depth : nat) (X : Type) (cell : Stored9 X)
         (m : Buf6 (Stored9 X)),
    back_ready_stored9_depth depth cell ->
    back_ready_or_empty_middle9_depth depth m ->
    back_ready_middle9_depth depth (buf6_push cell m).
Proof.
  intros depth X cell m Hcell [Hempty|Hready].
  - apply buf6_eject_seq_none in Hempty.
    unfold buf6_to_list in Hempty.
    destruct m as [xs]. cbn [buf6_elems] in Hempty. subst xs.
    exists buf6_empty, cell.
    cbn [buf6_push buf6_eject buf6_empty buf6_elems].
    split; [reflexivity|exact Hcell].
  - apply back_ready_middle9_depth_push_preserve. exact Hready.
Qed.

Theorem back_ready_or_empty_middle9_depth_after_front_refill_step :
  forall (depth : nat) (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X),
    buf6_pop m = Some (cell, m_rest) ->
    back_ready_or_empty_middle9_depth depth m ->
    back_ready_or_empty_middle9_depth depth
      match cell with
      | StoredSmall9 b =>
          buf6_push (StoredSmall9 b) m_rest
      | StoredBig9 pre sm suf =>
          buf6_push (StoredSmall9 pre)
            (k9_middle_push sm
              (buf6_push (StoredSmall9 suf) m_rest))
      | StoredMiddle9 sm =>
          k9_middle_push sm m_rest
      end.
Proof.
  intros depth X [xs] m_rest cell Hpop Hback.
  destruct xs as [|front xs]; [discriminate|].
  cbn [buf6_pop buf6_elems] in Hpop.
  injection Hpop as Hcell Hrest. subst front m_rest.
  destruct xs as [|next rest].
  - destruct Hback as [Hempty|Hready].
    + cbn [back_ready_or_empty_middle9_depth buf6_eject buf6_elems] in Hempty.
      discriminate.
    + destruct Hready as (rest0 & back_cell & Heject & Hcell_ready).
      cbn [buf6_eject buf6_elems] in Heject.
      injection Heject as Hrest0 Hback_cell. subst rest0 back_cell.
      destruct cell as [b|pre sm suf|sm].
      * right. exists buf6_empty, (StoredSmall9 b).
        cbn [buf6_push buf6_empty buf6_eject buf6_elems].
        split; [reflexivity|exact Hcell_ready].
      * right.
        unfold k9_middle_push.
        destruct (buf6_is_empty sm).
        -- exists (buf6_push (StoredSmall9 pre) buf6_empty),
             (StoredSmall9 suf).
           cbn [buf6_push buf6_empty buf6_eject buf6_elems].
           split; [reflexivity|].
           destruct depth; cbn in Hcell_ready |- *; exact Hcell_ready.
        -- exists
             (buf6_push (StoredSmall9 pre)
                (buf6_push (StoredMiddle9 sm) buf6_empty)),
             (StoredSmall9 suf).
           cbn [buf6_push buf6_empty buf6_eject buf6_elems].
           split; [reflexivity|].
           destruct depth; cbn in Hcell_ready |- *; exact Hcell_ready.
      * right.
        destruct depth as [|depth']; [contradiction|].
        cbn in Hcell_ready.
        destruct Hcell_ready as (sm_rest & back_cell & Hsm & Hinner).
        destruct sm as [sm_elems].
        destruct sm_elems as [|sm_head sm_tail]; [cbn in Hsm; discriminate|].
        exists buf6_empty, (StoredMiddle9 (mkBuf6 (sm_head :: sm_tail))).
        cbn [buf6_push buf6_empty buf6_eject buf6_elems].
        split; [reflexivity|].
        cbn. exists sm_rest, back_cell. split; assumption.
  - assert (Htail_back :
              back_ready_middle9_depth depth (mkBuf6 (next :: rest))).
    { destruct Hback as [Hempty|Hready].
      - apply buf6_eject_seq_none in Hempty. unfold buf6_to_list in Hempty.
        cbn [buf6_elems] in Hempty. discriminate.
      - destruct Hready as (full_rest & last & Hfull & Hlast).
        assert (Htail_ge : buf6_size_ge 1 (mkBuf6 (next :: rest))).
        { unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia. }
        destruct (buf6_eject_of_size_ge_S
                    (Stored9 X) 0 (mkBuf6 (next :: rest)) Htail_ge)
          as (tail_rest & tail_last & Htail).
        pose proof
          (buf6_eject_push_some
             (Stored9 X) cell (mkBuf6 (next :: rest))
             tail_rest tail_last Htail)
          as Hfull_expected.
        change (buf6_eject (buf6_push cell (mkBuf6 (next :: rest))) =
                  Some (full_rest, last)) in Hfull.
        rewrite Hfull_expected in Hfull.
        injection Hfull as _ Hlast_eq. subst last.
        exists tail_rest, tail_last. split; assumption. }
    destruct cell as [b|pre sm suf|sm].
    + right. apply back_ready_middle9_depth_push_preserve. exact Htail_back.
    + right. apply back_ready_middle9_depth_push_preserve.
      unfold k9_middle_push.
      destruct (buf6_is_empty sm).
      * apply back_ready_middle9_depth_push_preserve. exact Htail_back.
      * repeat apply back_ready_middle9_depth_push_preserve. exact Htail_back.
    + unfold k9_middle_push.
      destruct (buf6_is_empty sm).
      * right. exact Htail_back.
      * right. apply back_ready_middle9_depth_push_preserve. exact Htail_back.
Qed.

Theorem front_ready_or_empty_middle9_depth_after_back_refill_step :
  forall (depth : nat) (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X),
    buf6_eject m = Some (m_rest, cell) ->
    front_ready_or_empty_middle9_depth depth m ->
    front_ready_or_empty_middle9_depth depth
      match cell with
      | StoredSmall9 b =>
          buf6_inject m_rest (StoredSmall9 b)
      | StoredBig9 pre sm suf =>
          buf6_inject
            (k9_middle_inject
              (buf6_inject m_rest (StoredSmall9 pre))
              sm)
            (StoredSmall9 suf)
      | StoredMiddle9 sm =>
          k9_middle_inject m_rest sm
      end.
Proof.
  intros depth X m m_rest cell Heject Hfront.
  destruct m as [xs]. destruct m_rest as [rs].
  apply buf6_eject_seq_some in Heject.
  unfold buf6_to_list in Heject. cbn [buf6_elems] in Heject. subst xs.
  destruct rs as [|front rest].
  - destruct Hfront as [Hempty|Hready].
    + cbn [front_ready_or_empty_middle9_depth buf6_pop buf6_elems] in Hempty.
      discriminate.
    + destruct Hready as (front_cell & rest0 & Hpop & Hcell_ready).
      cbn [buf6_pop buf6_elems] in Hpop.
      injection Hpop as Hfront_cell Hrest0. subst front_cell rest0.
      destruct cell as [b|pre sm suf|sm].
      * right. exists (StoredSmall9 b), buf6_empty.
        cbn [buf6_inject buf6_empty buf6_pop buf6_elems].
        split; [reflexivity|exact Hcell_ready].
      * right. exists (StoredSmall9 pre),
          (buf6_inject
             (k9_middle_inject buf6_empty sm)
             (StoredSmall9 suf)).
        unfold k9_middle_inject.
        destruct (buf6_is_empty sm).
        -- cbn [buf6_inject buf6_empty buf6_pop buf6_elems].
           split; [reflexivity|].
           destruct depth; cbn in Hcell_ready |- *; exact Hcell_ready.
        -- cbn [buf6_inject buf6_empty buf6_pop buf6_elems].
           split; [reflexivity|].
           destruct depth; cbn in Hcell_ready |- *; exact Hcell_ready.
      * right.
        destruct depth as [|depth']; [contradiction|].
        cbn in Hcell_ready.
        destruct Hcell_ready as (front_inner & sm_rest & Hsm & Hinner).
        destruct sm as [sm_elems].
        destruct sm_elems as [|sm_head sm_tail]; [cbn in Hsm; discriminate|].
        exists (StoredMiddle9 (mkBuf6 (sm_head :: sm_tail))), buf6_empty.
        cbn [k9_middle_inject buf6_is_empty buf6_empty buf6_inject
             buf6_pop buf6_elems].
        split; [reflexivity|].
        cbn. exists front_inner, sm_rest. split; assumption.
  - assert (Hprefix_front :
              front_ready_middle9_depth depth (mkBuf6 (front :: rest))).
    { destruct Hfront as [Hempty|Hready].
      - cbn [front_ready_or_empty_middle9_depth buf6_pop buf6_elems] in Hempty.
        discriminate.
      - destruct Hready as (front_cell & full_rest & Hpop & Hcell_ready).
        cbn [buf6_pop buf6_elems] in Hpop.
        injection Hpop as Hfront_cell Hfull_rest.
        subst front_cell full_rest.
        exists front, (mkBuf6 rest). cbn [buf6_pop buf6_elems].
        split; [reflexivity|exact Hcell_ready]. }
    destruct cell as [b|pre sm suf|sm].
    + right. apply front_ready_middle9_depth_inject_preserve.
      exact Hprefix_front.
    + right. apply front_ready_middle9_depth_inject_preserve.
      apply front_ready_middle9_depth_k9_middle_inject_preserve.
      apply front_ready_middle9_depth_inject_preserve.
      exact Hprefix_front.
    + right. apply front_ready_middle9_depth_k9_middle_inject_preserve.
      exact Hprefix_front.
Qed.

Theorem buf6_push_stored_middle_front_ready_depth :
  forall (depth : nat) (X : Type) (sm rest : Buf6 (Stored9 X)),
    front_ready_middle9_depth depth sm ->
    front_ready_middle9_depth (S depth) (buf6_push (StoredMiddle9 sm) rest).
Proof.
  intros depth X sm rest Hready.
  apply buf6_push_front_ready_stored9_depth.
  apply stored_middle9_front_ready_depth. exact Hready.
Qed.

Theorem buf6_inject_stored_middle_back_ready_depth :
  forall (depth : nat) (X : Type) (rest sm : Buf6 (Stored9 X)),
    back_ready_middle9_depth depth sm ->
    back_ready_middle9_depth (S depth) (buf6_inject rest (StoredMiddle9 sm)).
Proof.
  intros depth X rest sm Hready.
  apply buf6_inject_back_ready_stored9_depth.
  apply stored_middle9_back_ready_depth. exact Hready.
Qed.

Fixpoint front_nested_middle9 {X : Type}
  (depth : nat) (leaf : Stored9 X) : Buf6 (Stored9 X) :=
  match depth with
  | O => buf6_push leaf buf6_empty
  | S depth' => buf6_push (StoredMiddle9 (front_nested_middle9 depth' leaf)) buf6_empty
  end.

Fixpoint back_nested_middle9 {X : Type}
  (depth : nat) (leaf : Stored9 X) : Buf6 (Stored9 X) :=
  match depth with
  | O => buf6_inject buf6_empty leaf
  | S depth' => buf6_inject buf6_empty (StoredMiddle9 (back_nested_middle9 depth' leaf))
  end.

Theorem back_nested_middle9_not_empty :
  forall (depth : nat) (X : Type) (leaf : Stored9 X),
    buf6_is_empty (back_nested_middle9 depth leaf) = false.
Proof.
  intros [|depth] X leaf;
    cbn [back_nested_middle9 buf6_inject buf6_empty buf6_is_empty buf6_elems];
    reflexivity.
Qed.

Theorem front_nested_middle9_ready_depth :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    front_ready_middle9_depth depth
      (front_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros X b Hge.
  - apply buf6_push_front_ready_stored9_depth.
    cbn [front_ready_stored9_depth front_ready_stored9]. exact Hge.
  - apply buf6_push_stored_middle_front_ready_depth.
    apply IH. exact Hge.
Qed.

Theorem back_nested_middle9_ready_depth :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    back_ready_middle9_depth depth
      (back_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros X b Hge.
  - apply buf6_inject_back_ready_stored9_depth.
    cbn [back_ready_stored9_depth back_ready_stored9]. exact Hge.
  - apply buf6_inject_stored_middle_back_ready_depth.
    apply IH. exact Hge.
Qed.

Theorem back_nested_middle9_front_ready_depth :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    front_ready_middle9_depth depth
      (back_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros X b Hge.
  - cbn [back_nested_middle9 front_ready_middle9_depth
         buf6_inject buf6_empty buf6_pop buf6_elems].
    exists (StoredSmall9 b), buf6_empty. split; [reflexivity|].
    cbn [front_ready_stored9_depth front_ready_stored9]. exact Hge.
  - cbn [back_nested_middle9 front_ready_middle9_depth
         buf6_inject buf6_empty buf6_pop buf6_elems].
    exists (StoredMiddle9 (back_nested_middle9 depth (StoredSmall9 b))),
      buf6_empty.
    split; [reflexivity|].
    apply stored_middle9_front_ready_depth.
    apply IH. exact Hge.
Qed.

Theorem front_nested_middle9_back_ready_depth :
  forall (depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    back_ready_middle9_depth depth
      (front_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros X b Hge.
  - cbn [front_nested_middle9 back_ready_middle9_depth
         buf6_push buf6_empty buf6_eject buf6_elems].
    exists buf6_empty, (StoredSmall9 b). split; [reflexivity|].
    cbn [back_ready_stored9_depth back_ready_stored9]. exact Hge.
  - cbn [front_nested_middle9 back_ready_middle9_depth
         buf6_push buf6_empty buf6_eject buf6_elems].
    exists buf6_empty,
      (StoredMiddle9 (front_nested_middle9 depth (StoredSmall9 b))).
    split; [reflexivity|].
    apply stored_middle9_back_ready_depth.
    apply IH. exact Hge.
Qed.

Theorem front_nested_middle9_not_ready_too_shallow :
  forall (depth fuel_depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    fuel_depth < depth ->
    ~ front_ready_middle9_depth fuel_depth
        (front_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros fuel_depth X b Hlt Hready.
  - lia.
  - destruct fuel_depth as [|fuel_depth].
    + cbn [front_ready_middle9_depth front_nested_middle9] in Hready.
      destruct Hready as (cell & rest & Hpop & Hcell).
      rewrite buf6_pop_push in Hpop. injection Hpop as Hcell_eq _.
      subst cell. contradiction.
    + cbn [front_ready_middle9_depth front_nested_middle9] in Hready.
      destruct Hready as (cell & rest & Hpop & Hcell).
      rewrite buf6_pop_push in Hpop. injection Hpop as Hcell_eq _.
      subst cell. cbn in Hcell.
      assert (Hlt' : fuel_depth < depth) by lia.
      exact (IH fuel_depth X b Hlt' Hcell).
Qed.

Theorem back_nested_middle9_not_ready_too_shallow :
  forall (depth fuel_depth : nat) (X : Type) (b : Buf6 (KElem9 X)),
    fuel_depth < depth ->
    ~ back_ready_middle9_depth fuel_depth
        (back_nested_middle9 depth (StoredSmall9 b)).
Proof.
  induction depth as [|depth IH]; intros fuel_depth X b Hlt Hready.
  - lia.
  - destruct fuel_depth as [|fuel_depth].
    + cbn [back_ready_middle9_depth back_nested_middle9] in Hready.
      destruct Hready as (rest & cell & Heject & Hcell).
      rewrite buf6_eject_inject in Heject. injection Heject as _ Hcell_eq.
      subst cell. contradiction.
    + cbn [back_ready_middle9_depth back_nested_middle9] in Hready.
      destruct Hready as (rest & cell & Heject & Hcell).
      rewrite buf6_eject_inject in Heject. injection Heject as _ Hcell_eq.
      subst cell. cbn in Hcell.
      assert (Hlt' : fuel_depth < depth) by lia.
      exact (IH fuel_depth X b Hlt' Hcell).
Qed.

Fixpoint k9_with_front_fuel {X : Type} (fuel : nat)
  (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X))
  {struct fuel} : KCadeque9 X :=
  match fuel with
  | O => K9Triple h m t
  | S fuel' =>
      if buf6_is_empty h then
        match buf6_pop m with
        | Some (cell, m_rest) =>
            match cell with
            | StoredSmall9 b =>
                if buf6_is_empty b then
                  k9_with_front_fuel fuel' buf6_empty m_rest t
                else K9Triple b m_rest t
            | StoredBig9 pre sm suf =>
                let new_m :=
                  k9_middle_push sm (buf6_push (StoredSmall9 suf) m_rest) in
                if buf6_is_empty pre then
                  k9_with_front_fuel fuel' buf6_empty new_m t
                else K9Triple pre new_m t
            | StoredMiddle9 sm =>
                match buf6_pop sm with
                | Some (front_cell, sm_rest) =>
                    let new_m :=
                      buf6_push front_cell (k9_middle_push sm_rest m_rest) in
                    k9_with_front_fuel fuel' buf6_empty new_m t
                | None =>
                    k9_with_front_fuel fuel' buf6_empty m_rest t
                end
            end
        | None =>
            if buf6_is_empty t then K9Empty else K9Simple t
        end
      else if buf6_is_empty t then
        k9_with_back_fuel fuel' h m t
      else K9Triple h m t
  end

with k9_with_back_fuel {X : Type} (fuel : nat)
  (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X))
  {struct fuel} : KCadeque9 X :=
  match fuel with
  | O => K9Triple h m t
  | S fuel' =>
      if buf6_is_empty t then
        match buf6_eject m with
        | Some (m_rest, cell) =>
            match cell with
            | StoredSmall9 b =>
                if buf6_is_empty b then
                  k9_with_back_fuel fuel' h m_rest buf6_empty
                else K9Triple h m_rest b
            | StoredBig9 pre sm suf =>
                let new_m :=
                  k9_middle_inject (buf6_inject m_rest (StoredSmall9 pre)) sm in
                if buf6_is_empty suf then
                  k9_with_back_fuel fuel' h new_m buf6_empty
                else K9Triple h new_m suf
            | StoredMiddle9 sm =>
                match buf6_eject sm with
                | Some (sm_rest, back_cell) =>
                    let new_m :=
                      buf6_inject (k9_middle_inject m_rest sm_rest) back_cell in
                    k9_with_back_fuel fuel' h new_m buf6_empty
                | None =>
                    k9_with_back_fuel fuel' h m_rest buf6_empty
                end
            end
        | None =>
            if buf6_is_empty h then K9Empty else K9Simple h
        end
      else if buf6_is_empty h then
        k9_with_front_fuel fuel' h m t
      else K9Triple h m t
  end.

Theorem k9_with_front_fuel_front_nested_too_shallow :
  forall (depth : nat) (X : Type) (t b : Buf6 (KElem9 X)),
    k9_with_front_fuel depth buf6_empty
      (front_nested_middle9 depth (StoredSmall9 b)) t =
    K9Triple buf6_empty (buf6_push (StoredSmall9 b) buf6_empty) t.
Proof.
  induction depth as [|depth IH]; intros X t b.
  - cbn [k9_with_front_fuel front_nested_middle9]. reflexivity.
  - cbn [k9_with_front_fuel front_nested_middle9 buf6_is_empty].
    rewrite buf6_pop_push.
    destruct depth as [|depth'].
    + cbn [front_nested_middle9 buf6_pop buf6_push buf6_empty
           buf6_elems k9_middle_push k9_with_front_fuel].
      reflexivity.
    + cbn [front_nested_middle9 buf6_pop buf6_push buf6_empty
           buf6_elems k9_middle_push].
      exact (IH X t b).
Qed.

Theorem k9_with_back_fuel_back_nested_too_shallow :
  forall (depth : nat) (X : Type) (h b : Buf6 (KElem9 X)),
    k9_with_back_fuel depth h
      (back_nested_middle9 depth (StoredSmall9 b)) buf6_empty =
    K9Triple h (buf6_inject buf6_empty (StoredSmall9 b)) buf6_empty.
Proof.
  induction depth as [|depth IH]; intros X h b.
  - cbn [k9_with_back_fuel back_nested_middle9]. reflexivity.
  - cbn [k9_with_back_fuel back_nested_middle9 buf6_is_empty].
    rewrite buf6_eject_inject.
    destruct depth as [|depth'].
    + cbn [back_nested_middle9 buf6_eject buf6_inject buf6_empty
           buf6_elems k9_middle_inject k9_with_back_fuel].
      reflexivity.
    + cbn [back_nested_middle9 buf6_eject buf6_inject buf6_empty
           buf6_elems k9_middle_inject].
      exact (IH X h b).
Qed.

Lemma kelem9_flat_list_empty_of_is_empty :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    buf6_is_empty b = true ->
    kelem9_flat_list (buf6_elems b) = [].
Proof.
  intros X [xs] Hempty.
  unfold buf6_is_empty, buf6_elems in Hempty.
  destruct xs as [|x xs]; [reflexivity|discriminate].
Qed.

Lemma stored9_flat_list_empty_of_pop_none :
  forall (X : Type) (m : Buf6 (Stored9 X)),
    buf6_pop m = None ->
    stored9_flat_list (buf6_elems m) = [].
Proof.
  intros X m Hpop.
  apply buf6_pop_seq_none in Hpop. unfold buf6_to_list in Hpop.
  unfold stored9_flat_list. rewrite Hpop. reflexivity.
Qed.

Lemma stored9_flat_list_empty_of_eject_none :
  forall (X : Type) (m : Buf6 (Stored9 X)),
    buf6_eject m = None ->
    stored9_flat_list (buf6_elems m) = [].
Proof.
  intros X m Heject.
  apply buf6_eject_seq_none in Heject. unfold buf6_to_list in Heject.
  unfold stored9_flat_list. rewrite Heject. reflexivity.
Qed.

Lemma buf6_eq_empty_of_is_empty :
  forall (X : Type) (b : Buf6 X),
    buf6_is_empty b = true -> b = buf6_empty.
Proof.
  intros X [xs] Hempty.
  unfold buf6_is_empty, buf6_elems in Hempty.
  destruct xs as [|x xs]; [reflexivity|discriminate].
Qed.

Lemma buf6_is_empty_false_of_pop_some :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_pop b = Some (x, b') ->
    buf6_is_empty b = false.
Proof.
  intros X [xs] x b' Hpop.
  unfold buf6_pop, buf6_is_empty, buf6_elems in *.
  destruct xs as [|y ys]; [discriminate|reflexivity].
Qed.

Lemma buf6_is_empty_false_of_eject_some :
  forall (X : Type) (b b' : Buf6 X) (x : X),
    buf6_eject b = Some (b', x) ->
    buf6_is_empty b = false.
Proof.
  intros X [xs] b' x Heject.
  unfold buf6_is_empty, buf6_elems.
  destruct xs as [|y ys]; [cbn in Heject; discriminate|reflexivity].
Qed.

Lemma k9_middle_push_pop :
  forall (X : Type) (sm rest sm_rest : Buf6 (Stored9 X))
         (front_cell : Stored9 X),
    buf6_pop sm = Some (front_cell, sm_rest) ->
    buf6_pop (k9_middle_push sm rest) = Some (StoredMiddle9 sm, rest).
Proof.
  intros X sm rest sm_rest front_cell Hpop.
  unfold k9_middle_push.
  rewrite (buf6_is_empty_false_of_pop_some
             (Stored9 X) sm front_cell sm_rest Hpop).
  apply buf6_pop_push.
Qed.

Lemma k9_middle_inject_eject :
  forall (X : Type) (rest sm sm_rest : Buf6 (Stored9 X))
         (back_cell : Stored9 X),
    buf6_eject sm = Some (sm_rest, back_cell) ->
    buf6_eject (k9_middle_inject rest sm) = Some (rest, StoredMiddle9 sm).
Proof.
  intros X rest sm sm_rest back_cell Heject.
  unfold k9_middle_inject.
  rewrite (buf6_is_empty_false_of_eject_some
             (Stored9 X) sm sm_rest back_cell Heject).
  apply buf6_eject_inject.
Qed.

Lemma k9_middle_inject_eject_nonempty_inv :
  forall (X : Type) (rest sm out_rest : Buf6 (Stored9 X))
         (cell : Stored9 X),
    buf6_is_empty sm = false ->
    buf6_eject (k9_middle_inject rest sm) = Some (out_rest, cell) ->
    out_rest = rest /\ cell = StoredMiddle9 sm.
Proof.
  intros X [rs] [ss] out_rest cell Hnonempty Heject.
  unfold k9_middle_inject, buf6_is_empty, buf6_eject,
    buf6_inject, buf6_elems in *.
  destruct ss as [|s ss]; [discriminate|].
  rewrite rev_unit in Heject. cbn in Heject.
  rewrite rev_involutive in Heject.
  injection Heject as Hrest Hcell. subst.
  split; reflexivity.
Qed.

Lemma k9_with_fuel_seq_pair :
  forall fuel : nat,
    (forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
            (t : Buf6 (KElem9 X)),
        kcad9_to_list (k9_with_front_fuel fuel h m t)
        = kelem9_flat_list (buf6_elems h)
          ++ stored9_flat_list (buf6_elems m)
          ++ kelem9_flat_list (buf6_elems t)) /\
    (forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
            (t : Buf6 (KElem9 X)),
        kcad9_to_list (k9_with_back_fuel fuel h m t)
        = kelem9_flat_list (buf6_elems h)
          ++ stored9_flat_list (buf6_elems m)
          ++ kelem9_flat_list (buf6_elems t)).
Proof.
  induction fuel as [|fuel [IHfront IHback]].
  - split; intros X h m t;
      cbn [k9_with_front_fuel k9_with_back_fuel];
      rewrite kcad9_to_list_triple; reflexivity.
  - split; intros X h m t.
    + cbn [k9_with_front_fuel].
      destruct (buf6_is_empty h) eqn:Hh.
      * assert (Hhflat := kelem9_flat_list_empty_of_is_empty X h Hh).
        destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
        -- assert (Hm := Hpop). apply stored9_flat_list_pop_some in Hm.
           destruct cell as [b|pre sm suf|sm].
           ++ destruct (buf6_is_empty b) eqn:Hb.
              ** assert (Hbflat := kelem9_flat_list_empty_of_is_empty X b Hb).
                 rewrite IHfront. rewrite Hhflat. rewrite Hm.
                 rewrite stored9_to_list_small. rewrite Hbflat.
                 reflexivity.
              ** rewrite kcad9_to_list_triple. rewrite Hhflat. rewrite Hm.
                 rewrite stored9_to_list_small. rewrite <- !app_assoc.
                 reflexivity.
           ++ destruct (buf6_is_empty pre) eqn:Hpre.
              ** assert (Hpreflat :=
                   kelem9_flat_list_empty_of_is_empty X pre Hpre).
                 rewrite IHfront. rewrite k9_middle_push_seq.
                 rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
                 rewrite Hhflat. rewrite Hm. rewrite stored9_to_list_big.
                 rewrite Hpreflat. rewrite <- !app_assoc. reflexivity.
              ** rewrite kcad9_to_list_triple. rewrite k9_middle_push_seq.
                 rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
                 rewrite Hhflat. rewrite Hm. rewrite stored9_to_list_big.
                 rewrite <- !app_assoc. reflexivity.
           ++ destruct (buf6_pop sm) as [[front_cell sm_rest]|] eqn:Hsm.
              ** assert (Hsmflat := Hsm).
                 apply stored9_flat_list_pop_some in Hsmflat.
                 rewrite IHfront. rewrite stored9_flat_list_push.
                 rewrite k9_middle_push_seq. rewrite Hhflat. rewrite Hm.
                 rewrite stored9_to_list_middle. rewrite Hsmflat.
                 rewrite <- !app_assoc. reflexivity.
              ** assert (Hsmflat :=
                   stored9_flat_list_empty_of_pop_none X sm Hsm).
                 rewrite IHfront. rewrite Hhflat. rewrite Hm.
                 rewrite stored9_to_list_middle. rewrite Hsmflat.
                 reflexivity.
        -- assert (Hmflat := stored9_flat_list_empty_of_pop_none X m Hpop).
           destruct (buf6_is_empty t) eqn:Ht.
           ++ assert (Htflat := kelem9_flat_list_empty_of_is_empty X t Ht).
              rewrite Hhflat, Hmflat, Htflat. reflexivity.
           ++ rewrite kcad9_to_list_simple.
              rewrite Hhflat, Hmflat. reflexivity.
      * destruct (buf6_is_empty t) eqn:Ht.
        -- rewrite IHback. reflexivity.
        -- rewrite kcad9_to_list_triple. reflexivity.
    + cbn [k9_with_back_fuel].
      destruct (buf6_is_empty t) eqn:Ht.
      * assert (Htflat := kelem9_flat_list_empty_of_is_empty X t Ht).
        destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
        -- assert (Hm := Heject). apply stored9_flat_list_eject_some in Hm.
           destruct cell as [b|pre sm suf|sm].
           ++ destruct (buf6_is_empty b) eqn:Hb.
              ** assert (Hbflat := kelem9_flat_list_empty_of_is_empty X b Hb).
                 rewrite IHback. rewrite Hm. rewrite stored9_to_list_small.
                 rewrite Hbflat. rewrite Htflat. rewrite !app_nil_r.
                 reflexivity.
              ** rewrite kcad9_to_list_triple. rewrite Hm.
                 rewrite stored9_to_list_small. rewrite Htflat.
                 rewrite !app_nil_r. reflexivity.
           ++ destruct (buf6_is_empty suf) eqn:Hsuf.
              ** assert (Hsufflat :=
                   kelem9_flat_list_empty_of_is_empty X suf Hsuf).
                 rewrite IHback. rewrite k9_middle_inject_seq.
                 rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
                 rewrite Hm. rewrite stored9_to_list_big. rewrite Hsufflat.
                 rewrite Htflat. rewrite !app_nil_r.
                 rewrite <- !app_assoc. reflexivity.
              ** rewrite kcad9_to_list_triple. rewrite k9_middle_inject_seq.
                 rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
                 rewrite Hm. rewrite stored9_to_list_big. rewrite Htflat.
                 rewrite !app_nil_r.
                 rewrite <- !app_assoc. reflexivity.
           ++ destruct (buf6_eject sm) as [[sm_rest back_cell]|] eqn:Hsm.
              ** assert (Hsmflat := Hsm).
                 apply stored9_flat_list_eject_some in Hsmflat.
                 rewrite IHback. rewrite stored9_flat_list_inject.
                 rewrite k9_middle_inject_seq. rewrite Hm.
                 rewrite stored9_to_list_middle. rewrite Hsmflat.
                 rewrite Htflat. rewrite !app_nil_r.
                 rewrite <- !app_assoc. reflexivity.
              ** assert (Hsmflat :=
                   stored9_flat_list_empty_of_eject_none X sm Hsm).
                 rewrite IHback. rewrite Hm. rewrite stored9_to_list_middle.
                 rewrite Hsmflat. rewrite Htflat. rewrite !app_nil_r.
                 reflexivity.
        -- assert (Hmflat := stored9_flat_list_empty_of_eject_none X m Heject).
           destruct (buf6_is_empty h) eqn:Hh.
           ++ assert (Hhflat := kelem9_flat_list_empty_of_is_empty X h Hh).
              rewrite Hhflat, Hmflat, Htflat. reflexivity.
           ++ rewrite kcad9_to_list_simple.
              rewrite Hmflat, Htflat. rewrite app_nil_r. reflexivity.
      * destruct (buf6_is_empty h) eqn:Hh.
        -- rewrite IHfront. reflexivity.
        -- rewrite kcad9_to_list_triple. reflexivity.
Qed.

Theorem k9_with_front_fuel_seq :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    kcad9_to_list (k9_with_front_fuel fuel h m t)
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof.
  intros fuel. exact (proj1 (k9_with_fuel_seq_pair fuel)).
Qed.

Theorem k9_with_back_fuel_seq :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    kcad9_to_list (k9_with_back_fuel fuel h m t)
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof.
  intros fuel. exact (proj2 (k9_with_fuel_seq_pair fuel)).
Qed.

Theorem k9_with_fuel_deep_xbase_pair :
  forall fuel : nat,
    (forall (X : Type) (h : Buf6 (KElem9 X))
            (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
        all_xbase9 h ->
        xbase_middle9_deep m ->
        all_xbase9 t ->
        inv_kcad9_ocaml_deep_xbase (k9_with_front_fuel fuel h m t)) /\
    (forall (X : Type) (h : Buf6 (KElem9 X))
            (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
        all_xbase9 h ->
        xbase_middle9_deep m ->
        all_xbase9 t ->
        inv_kcad9_ocaml_deep_xbase (k9_with_back_fuel fuel h m t)).
Proof.
  induction fuel as [|fuel [IHfront IHback]].
  - split; intros X h m t Hh Hm Ht;
      cbn [k9_with_front_fuel k9_with_back_fuel
           inv_kcad9_ocaml_deep_xbase];
      repeat split; assumption.
  - split; intros X h m t Hh Hm Ht.
    + cbn [k9_with_front_fuel].
      destruct (buf6_is_empty h) eqn:Hh_empty.
      * destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
        -- destruct (xbase_middle9_deep_pop X m m_rest cell Hm Hpop)
             as [Hcell Hm_rest].
           destruct cell as [b|pre sm suf|sm].
           ++ cbn [xbase_stored9_deep] in Hcell.
              destruct (buf6_is_empty b) eqn:Hb_empty.
              ** apply IHfront; [apply all_xbase9_empty|exact Hm_rest|exact Ht].
              ** cbn [inv_kcad9_ocaml_deep_xbase].
                 repeat split; assumption.
           ++ apply xbase_stored9_deep_big_iff in Hcell.
              destruct Hcell as [Hpre [Hsuf Hsm]].
              assert (Hnew :
                xbase_middle9_deep
                  (k9_middle_push sm
                    (buf6_push (StoredSmall9 suf) m_rest))).
              { apply xbase_middle9_deep_k9_middle_push; [exact Hsm|].
                apply xbase_middle9_deep_push; [exact Hsuf|exact Hm_rest]. }
              destruct (buf6_is_empty pre) eqn:Hpre_empty.
              ** apply IHfront; [apply all_xbase9_empty|exact Hnew|exact Ht].
              ** cbn [inv_kcad9_ocaml_deep_xbase].
                 repeat split; assumption.
           ++ apply xbase_stored9_deep_middle_iff in Hcell.
              destruct (buf6_pop sm) as [[front_cell sm_rest]|] eqn:Hsm_pop.
              ** destruct (xbase_middle9_deep_pop
                             X sm sm_rest front_cell Hcell Hsm_pop)
                   as [Hfront_cell Hsm_rest].
                 apply IHfront; [apply all_xbase9_empty| |exact Ht].
                 apply xbase_middle9_deep_push; [exact Hfront_cell|].
                 apply xbase_middle9_deep_k9_middle_push;
                   [exact Hsm_rest|exact Hm_rest].
              ** apply IHfront; [apply all_xbase9_empty|exact Hm_rest|exact Ht].
        -- destruct (buf6_is_empty t) eqn:Ht_empty;
             cbn [inv_kcad9_ocaml_deep_xbase]; auto.
      * destruct (buf6_is_empty t) eqn:Ht_empty.
        -- apply IHback; assumption.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           repeat split; assumption.
    + cbn [k9_with_back_fuel].
      destruct (buf6_is_empty t) eqn:Ht_empty.
      * destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
        -- destruct (xbase_middle9_deep_eject X m m_rest cell Hm Heject)
             as [Hm_rest Hcell].
           destruct cell as [b|pre sm suf|sm].
           ++ cbn [xbase_stored9_deep] in Hcell.
              destruct (buf6_is_empty b) eqn:Hb_empty.
              ** apply IHback; [exact Hh|exact Hm_rest|apply all_xbase9_empty].
              ** cbn [inv_kcad9_ocaml_deep_xbase].
                 repeat split; assumption.
           ++ apply xbase_stored9_deep_big_iff in Hcell.
              destruct Hcell as [Hpre [Hsuf Hsm]].
              assert (Hnew :
                xbase_middle9_deep
                  (k9_middle_inject
                    (buf6_inject m_rest (StoredSmall9 pre)) sm)).
              { apply xbase_middle9_deep_k9_middle_inject; [|exact Hsm].
                apply xbase_middle9_deep_inject; [exact Hm_rest|exact Hpre]. }
              destruct (buf6_is_empty suf) eqn:Hsuf_empty.
              ** apply IHback; [exact Hh|exact Hnew|apply all_xbase9_empty].
              ** cbn [inv_kcad9_ocaml_deep_xbase].
                 repeat split; assumption.
           ++ apply xbase_stored9_deep_middle_iff in Hcell.
              destruct (buf6_eject sm) as [[sm_rest back_cell]|] eqn:Hsm_eject.
              ** destruct (xbase_middle9_deep_eject
                             X sm sm_rest back_cell Hcell Hsm_eject)
                   as [Hsm_rest Hback_cell].
                 apply IHback; [exact Hh| |apply all_xbase9_empty].
                 apply xbase_middle9_deep_inject; [|exact Hback_cell].
                 apply xbase_middle9_deep_k9_middle_inject;
                   [exact Hm_rest|exact Hsm_rest].
              ** apply IHback; [exact Hh|exact Hm_rest|apply all_xbase9_empty].
        -- destruct (buf6_is_empty h) eqn:Hh_empty;
             cbn [inv_kcad9_ocaml_deep_xbase]; auto.
      * destruct (buf6_is_empty h) eqn:Hh_empty.
        -- apply IHfront; assumption.
        -- cbn [inv_kcad9_ocaml_deep_xbase].
           repeat split; assumption.
Qed.

Theorem k9_with_front_fuel_deep_xbase :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    all_xbase9 h ->
    xbase_middle9_deep m ->
    all_xbase9 t ->
    inv_kcad9_ocaml_deep_xbase (k9_with_front_fuel fuel h m t).
Proof.
  intros fuel. exact (proj1 (k9_with_fuel_deep_xbase_pair fuel)).
Qed.

Theorem k9_with_back_fuel_deep_xbase :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    all_xbase9 h ->
    xbase_middle9_deep m ->
    all_xbase9 t ->
    inv_kcad9_ocaml_deep_xbase (k9_with_back_fuel fuel h m t).
Proof.
  intros fuel. exact (proj2 (k9_with_fuel_deep_xbase_pair fuel)).
Qed.

Theorem k9_with_front_fuel_one_present_boundaries :
  forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    buf6_size_ge 1 h ->
    buf6_size_ge 1 t ->
    k9_with_front_fuel 1 h m t = K9Triple h m t.
Proof.
  intros X h m t Hh Ht. cbn [k9_with_front_fuel].
  rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 h Hh).
  rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 t Ht).
  reflexivity.
Qed.

Theorem k9_with_back_fuel_one_present_boundaries :
  forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    buf6_size_ge 1 h ->
    buf6_size_ge 1 t ->
    k9_with_back_fuel 1 h m t = K9Triple h m t.
Proof.
  intros X h m t Hh Ht. cbn [k9_with_back_fuel].
  rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 t Ht).
  rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 h Hh).
  reflexivity.
Qed.

Theorem k9_with_front_fuel_present_boundaries :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_size_ge 1 h ->
    buf6_size_ge 1 t ->
    k9_with_front_fuel fuel h m t = K9Triple h m t.
Proof.
  intros [|fuel] X h m t Hh Ht.
  - cbn [k9_with_front_fuel]. reflexivity.
  - cbn [k9_with_front_fuel].
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 h Hh).
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 t Ht).
    reflexivity.
Qed.

Theorem k9_with_back_fuel_present_boundaries :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_size_ge 1 h ->
    buf6_size_ge 1 t ->
    k9_with_back_fuel fuel h m t = K9Triple h m t.
Proof.
  intros [|fuel] X h m t Hh Ht.
  - cbn [k9_with_back_fuel]. reflexivity.
  - cbn [k9_with_back_fuel].
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 t Ht).
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 h Hh).
    reflexivity.
Qed.

Theorem k9_with_front_fuel_one_exposed_ready :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X) (t : Buf6 (KElem9 X)),
    buf6_pop m = Some (cell, m_rest) ->
    front_ready_stored9 cell ->
    exists h' m',
      k9_with_front_fuel 1 buf6_empty m t = K9Triple h' m' t /\
      buf6_size_ge 1 h'.
Proof.
  intros X m m_rest cell t Hpop Hready.
  cbn [k9_with_front_fuel].
  rewrite Hpop.
  destruct cell as [b|pre sm suf|sm].
  - cbn [front_ready_stored9] in Hready.
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hready).
    exists b, m_rest. split; [reflexivity|exact Hready].
  - cbn [front_ready_stored9] in Hready.
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 pre Hready).
    exists pre, (k9_middle_push sm (buf6_push (StoredSmall9 suf) m_rest)).
    split; [reflexivity|exact Hready].
  - contradiction.
Qed.

Theorem k9_with_back_fuel_one_exposed_ready :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X) (h : Buf6 (KElem9 X)),
    buf6_eject m = Some (m_rest, cell) ->
    back_ready_stored9 cell ->
    exists m' t',
      k9_with_back_fuel 1 h m buf6_empty = K9Triple h m' t' /\
      buf6_size_ge 1 t'.
Proof.
  intros X m m_rest cell h Heject Hready.
  cbn [k9_with_back_fuel].
  rewrite Heject.
  destruct cell as [b|pre sm suf|sm].
  - cbn [back_ready_stored9] in Hready.
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hready).
    exists m_rest, b. split; [reflexivity|exact Hready].
  - cbn [back_ready_stored9] in Hready.
    rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 suf Hready).
    exists (k9_middle_inject (buf6_inject m_rest (StoredSmall9 pre)) sm), suf.
    split; [reflexivity|exact Hready].
  - contradiction.
Qed.

Theorem k9_with_front_fuel_exposed_ready_depth :
  forall (depth : nat) (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X) (t : Buf6 (KElem9 X)),
    buf6_pop m = Some (cell, m_rest) ->
    front_ready_stored9_depth depth cell ->
    exists h' m',
      k9_with_front_fuel (S depth) buf6_empty m t = K9Triple h' m' t /\
      buf6_size_ge 1 h'.
Proof.
  induction depth as [|depth IH].
  - intros X m m_rest cell t Hpop Hready.
    eapply k9_with_front_fuel_one_exposed_ready; eassumption.
  - intros X m m_rest cell t Hpop Hready.
    cbn [k9_with_front_fuel].
    rewrite Hpop.
    destruct cell as [b|pre sm suf|sm].
    + cbn [front_ready_stored9_depth] in Hready.
      rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hready).
      exists b, m_rest. split; [reflexivity|exact Hready].
    + cbn [front_ready_stored9_depth] in Hready.
      rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 pre Hready).
      exists pre, (k9_middle_push sm (buf6_push (StoredSmall9 suf) m_rest)).
      split; [reflexivity|exact Hready].
    + cbn [front_ready_stored9_depth] in Hready.
      destruct Hready as (front_cell & sm_rest & Hsm & Hinner).
      rewrite Hsm.
      destruct (IH X
        (buf6_push front_cell (k9_middle_push sm_rest m_rest))
        (k9_middle_push sm_rest m_rest) front_cell t
        (buf6_pop_push (Stored9 X) front_cell
           (k9_middle_push sm_rest m_rest))
        Hinner) as (h' & m' & Heq & Hge).
      exists h', m'. split; [exact Heq|exact Hge].
Qed.

Theorem k9_with_back_fuel_exposed_ready_depth :
  forall (depth : nat) (X : Type) (m m_rest : Buf6 (Stored9 X))
         (cell : Stored9 X) (h : Buf6 (KElem9 X)),
    buf6_eject m = Some (m_rest, cell) ->
    back_ready_stored9_depth depth cell ->
    exists m' t',
      k9_with_back_fuel (S depth) h m buf6_empty = K9Triple h m' t' /\
      buf6_size_ge 1 t'.
Proof.
  induction depth as [|depth IH].
  - intros X m m_rest cell h Heject Hready.
    eapply k9_with_back_fuel_one_exposed_ready; eassumption.
  - intros X m m_rest cell h Heject Hready.
    cbn [k9_with_back_fuel].
    rewrite Heject.
    destruct cell as [b|pre sm suf|sm].
    + cbn [back_ready_stored9_depth] in Hready.
      rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 b Hready).
      exists m_rest, b. split; [reflexivity|exact Hready].
    + cbn [back_ready_stored9_depth] in Hready.
      rewrite (buf6_size_ge_S_not_empty (KElem9 X) 0 suf Hready).
      exists (k9_middle_inject (buf6_inject m_rest (StoredSmall9 pre)) sm), suf.
      split; [reflexivity|exact Hready].
    + cbn [back_ready_stored9_depth] in Hready.
      destruct Hready as (sm_rest & back_cell & Hsm & Hinner).
      rewrite Hsm.
      destruct (IH X
        (buf6_inject (k9_middle_inject m_rest sm_rest) back_cell)
        (k9_middle_inject m_rest sm_rest) back_cell h
        (buf6_eject_inject (Stored9 X)
           (k9_middle_inject m_rest sm_rest) back_cell)
        Hinner) as (m' & t' & Heq & Hge).
      exists m', t'. split; [exact Heq|exact Hge].
Qed.

Theorem k9_with_front_fuel_middle_ready_depth :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    front_ready_middle9_depth depth m ->
    exists h' m',
      k9_with_front_fuel (S depth) buf6_empty m t = K9Triple h' m' t /\
      buf6_size_ge 1 h'.
Proof.
  intros depth X m t (cell & m_rest & Hpop & Hready).
  eapply k9_with_front_fuel_exposed_ready_depth; eassumption.
Qed.

Theorem k9_with_back_fuel_middle_ready_depth :
  forall (depth : nat) (X : Type) (m : Buf6 (Stored9 X))
         (h : Buf6 (KElem9 X)),
    back_ready_middle9_depth depth m ->
    exists m' t',
      k9_with_back_fuel (S depth) h m buf6_empty = K9Triple h m' t' /\
      buf6_size_ge 1 t'.
Proof.
  intros depth X m h (m_rest & cell & Heject & Hready).
  eapply k9_with_back_fuel_exposed_ready_depth; eassumption.
Qed.

Definition refill_h_K9Triple_fuel {X : Type} (fuel : nat)
  (h' : Buf6 (KElem9 X))
  (m : Buf6 (Stored9 X))
  (t : Buf6 (KElem9 X))
  : KCadeque9 X :=
  match buf6_pop m with
  | Some (cell, m_rest) =>
      match cell with
      | StoredSmall9 b =>
          k9_with_front_fuel fuel h' (buf6_push (StoredSmall9 b) m_rest) t
      | StoredBig9 pre sm suf =>
          let new_m :=
            buf6_push (StoredSmall9 pre)
              (k9_middle_push sm
                (buf6_push (StoredSmall9 suf) m_rest)) in
          k9_with_front_fuel fuel h' new_m t
      | StoredMiddle9 sm =>
          k9_with_front_fuel fuel h' (k9_middle_push sm m_rest) t
      end
  | None =>
      k9_with_front_fuel fuel h' buf6_empty t
  end.

Definition refill_t_K9Triple_fuel {X : Type} (fuel : nat)
  (h : Buf6 (KElem9 X))
  (m : Buf6 (Stored9 X))
  (t' : Buf6 (KElem9 X))
  : KCadeque9 X :=
  match buf6_eject m with
  | Some (m_rest, cell) =>
      match cell with
      | StoredSmall9 b =>
          k9_with_back_fuel fuel h (buf6_inject m_rest (StoredSmall9 b)) t'
      | StoredBig9 pre sm suf =>
          let new_m :=
            buf6_inject
              (k9_middle_inject
                (buf6_inject m_rest (StoredSmall9 pre))
                sm)
              (StoredSmall9 suf) in
          k9_with_back_fuel fuel h new_m t'
      | StoredMiddle9 sm =>
          k9_with_back_fuel fuel h (k9_middle_inject m_rest sm) t'
      end
  | None =>
      k9_with_back_fuel fuel h buf6_empty t'
  end.

Theorem refill_h_K9Triple_fuel_deep_xbase :
  forall (fuel : nat) (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    all_xbase9 h' ->
    xbase_middle9_deep m ->
    all_xbase9 t ->
    inv_kcad9_ocaml_deep_xbase (refill_h_K9Triple_fuel fuel h' m t).
Proof.
  intros fuel X h' m t Hh' Hm Ht.
  unfold refill_h_K9Triple_fuel.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - destruct (xbase_middle9_deep_pop X m m_rest cell Hm Hpop)
      as [Hcell Hm_rest].
    destruct cell as [b|pre sm suf|sm].
    + apply k9_with_front_fuel_deep_xbase; [exact Hh'| |exact Ht].
      apply xbase_middle9_deep_push; [exact Hcell|exact Hm_rest].
    + apply xbase_stored9_deep_big_iff in Hcell.
      destruct Hcell as [Hpre [Hsuf Hsm]].
      apply k9_with_front_fuel_deep_xbase; [exact Hh'| |exact Ht].
      apply xbase_middle9_deep_push; [exact Hpre|].
      apply xbase_middle9_deep_k9_middle_push.
      * exact Hsm.
      * apply xbase_middle9_deep_push; [exact Hsuf|exact Hm_rest].
    + apply xbase_stored9_deep_middle_iff in Hcell.
      apply k9_with_front_fuel_deep_xbase; [exact Hh'| |exact Ht].
      apply xbase_middle9_deep_k9_middle_push; assumption.
  - apply k9_with_front_fuel_deep_xbase.
    + exact Hh'.
    + apply xbase_middle9_deep_empty.
    + exact Ht.
Qed.

Theorem refill_t_K9Triple_fuel_deep_xbase :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    all_xbase9 h ->
    xbase_middle9_deep m ->
    all_xbase9 t' ->
    inv_kcad9_ocaml_deep_xbase (refill_t_K9Triple_fuel fuel h m t').
Proof.
  intros fuel X h m t' Hh Hm Ht'.
  unfold refill_t_K9Triple_fuel.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
  - destruct (xbase_middle9_deep_eject X m m_rest cell Hm Heject)
      as [Hm_rest Hcell].
    destruct cell as [b|pre sm suf|sm].
    + apply k9_with_back_fuel_deep_xbase; [exact Hh| |exact Ht'].
      apply xbase_middle9_deep_inject; [exact Hm_rest|exact Hcell].
    + apply xbase_stored9_deep_big_iff in Hcell.
      destruct Hcell as [Hpre [Hsuf Hsm]].
      apply k9_with_back_fuel_deep_xbase; [exact Hh| |exact Ht'].
      apply xbase_middle9_deep_inject.
      * apply xbase_middle9_deep_k9_middle_inject.
        -- apply xbase_middle9_deep_inject; [exact Hm_rest|exact Hpre].
        -- exact Hsm.
      * exact Hsuf.
    + apply xbase_stored9_deep_middle_iff in Hcell.
      apply k9_with_back_fuel_deep_xbase; [exact Hh| |exact Ht'].
      apply xbase_middle9_deep_k9_middle_inject; assumption.
  - apply k9_with_back_fuel_deep_xbase.
    + exact Hh.
    + apply xbase_middle9_deep_empty.
    + exact Ht'.
Qed.

Definition kcad9_pop_ocaml_shape_fuel {X : Type} (fuel : nat)
  (k : KCadeque9 X) : option (X * KCadeque9 X) :=
  match k with
  | K9Empty => None
  | K9Simple b =>
      match buf6_pop b with
      | Some (XBase9 x, b') =>
          if buf6_is_empty b' then Some (x, K9Empty)
          else Some (x, K9Simple b')
      | _ => None
      end
  | K9Triple h m t =>
      match buf6_pop h with
      | Some (XBase9 x, h') =>
          if Nat.leb 5 (buf6_size h') then
            Some (x, K9Triple h' m t)
          else
            Some (x, refill_h_K9Triple_fuel fuel h' m t)
      | _ => None
      end
  end.

Definition kcad9_eject_ocaml_shape_fuel {X : Type} (fuel : nat)
  (k : KCadeque9 X) : option (KCadeque9 X * X) :=
  match k with
  | K9Empty => None
  | K9Simple b =>
      match buf6_eject b with
      | Some (b', XBase9 x) =>
          if buf6_is_empty b' then Some (K9Empty, x)
          else Some (K9Simple b', x)
      | _ => None
      end
  | K9Triple h m t =>
      match buf6_eject t with
      | Some (t', XBase9 x) =>
          if Nat.leb 5 (buf6_size t') then
            Some (K9Triple h m t', x)
          else
            Some (refill_t_K9Triple_fuel fuel h m t', x)
      | _ => None
      end
  end.

Theorem kcad9_pop_ocaml_shape_fuel_inv_deep_xbase :
  forall (fuel : nat) (X : Type) (k : KCadeque9 X)
         (x : X) (k' : KCadeque9 X),
    inv_kcad9_ocaml_deep_xbase k ->
    kcad9_pop_ocaml_shape_fuel fuel k = Some (x, k') ->
    inv_kcad9_ocaml_deep_xbase k'.
Proof.
  intros fuel X [|b|h m t] x k' Hinv Hpop;
    cbn [kcad9_pop_ocaml_shape_fuel] in Hpop.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct (all_xbase9_pop X b b' e Hinv Hpb) as [He Hb'].
    destruct e as [y|s]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k';
      cbn [inv_kcad9_ocaml_deep_xbase]; auto.
  - destruct Hinv as [Hh [Hm Ht]].
    destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct (all_xbase9_pop X h h' e Hh Hph) as [He Hh'].
    destruct e as [y|s]; [|destruct He].
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'.
    + cbn [inv_kcad9_ocaml_deep_xbase]. repeat split; assumption.
    + apply refill_h_K9Triple_fuel_deep_xbase; assumption.
Qed.

Theorem kcad9_eject_ocaml_shape_fuel_inv_deep_xbase :
  forall (fuel : nat) (X : Type) (k : KCadeque9 X)
         (k' : KCadeque9 X) (x : X),
    inv_kcad9_ocaml_deep_xbase k ->
    kcad9_eject_ocaml_shape_fuel fuel k = Some (k', x) ->
    inv_kcad9_ocaml_deep_xbase k'.
Proof.
  intros fuel X [|b|h m t] k' x Hinv Heject;
    cbn [kcad9_eject_ocaml_shape_fuel] in Heject.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct (all_xbase9_eject X b b' e Hinv Heb) as [Hb' He].
    destruct e as [y|s]; [|destruct He].
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k';
      cbn [inv_kcad9_ocaml_deep_xbase]; auto.
  - destruct Hinv as [Hh [Hm Ht]].
    destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct (all_xbase9_eject X t t' e Ht Het) as [Ht' He].
    destruct e as [y|s]; [|destruct He].
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'.
    + cbn [inv_kcad9_ocaml_deep_xbase]. repeat split; assumption.
    + apply refill_t_K9Triple_fuel_deep_xbase; assumption.
Qed.

Theorem refill_h_K9Triple_fuel_inv_boundaries_present :
  forall (fuel : nat) (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_size_ge 1 h' ->
    buf6_size_ge 1 t ->
    inv_kcad9_ocaml_boundaries (refill_h_K9Triple_fuel fuel h' m t).
Proof.
  intros fuel X h' m t Hh' Ht. unfold refill_h_K9Triple_fuel.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - destruct cell as [b|pre sm suf|sm];
      rewrite (k9_with_front_fuel_present_boundaries fuel X h' _ t Hh' Ht);
      cbn [inv_kcad9_ocaml_boundaries]; split; assumption.
  - rewrite (k9_with_front_fuel_present_boundaries fuel X h' _ t Hh' Ht);
      cbn [inv_kcad9_ocaml_boundaries]; split; assumption.
Qed.

Theorem refill_t_K9Triple_fuel_inv_boundaries_present :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    buf6_size_ge 1 h ->
    buf6_size_ge 1 t' ->
    inv_kcad9_ocaml_boundaries (refill_t_K9Triple_fuel fuel h m t').
Proof.
  intros fuel X h m t' Hh Ht'. unfold refill_t_K9Triple_fuel.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
  - destruct cell as [b|pre sm suf|sm];
      rewrite (k9_with_back_fuel_present_boundaries fuel X h _ t' Hh Ht');
      cbn [inv_kcad9_ocaml_boundaries]; split; assumption.
  - rewrite (k9_with_back_fuel_present_boundaries fuel X h _ t' Hh Ht');
      cbn [inv_kcad9_ocaml_boundaries]; split; assumption.
Qed.

Theorem refill_h_K9Triple_fuel_front_ready_depth :
  forall (depth : nat) (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_is_empty h' = true ->
    front_ready_middle9_depth depth m ->
    exists h'' m',
      refill_h_K9Triple_fuel (S depth) h' m t = K9Triple h'' m' t /\
      buf6_size_ge 1 h''.
Proof.
  intros depth X h' m t Hempty Hready.
  apply buf6_eq_empty_of_is_empty in Hempty. subst h'.
  unfold refill_h_K9Triple_fuel.
  destruct Hready as (cell & m_rest & Hpop & Hcell).
  rewrite Hpop.
  destruct cell as [b|pre sm suf|sm].
  - eapply k9_with_front_fuel_exposed_ready_depth.
    + apply buf6_pop_push.
    + destruct depth; cbn in Hcell |- *; exact Hcell.
  - eapply k9_with_front_fuel_exposed_ready_depth.
    + apply buf6_pop_push.
    + destruct depth; cbn in Hcell |- *; exact Hcell.
  - destruct depth as [|depth']; [contradiction|].
    cbn in Hcell.
    destruct Hcell as (front_cell & sm_rest & Hsm & Hinner).
    eapply k9_with_front_fuel_exposed_ready_depth.
    + eapply k9_middle_push_pop. exact Hsm.
    + cbn. exists front_cell, sm_rest. split; [exact Hsm|exact Hinner].
Qed.

Theorem refill_t_K9Triple_fuel_back_ready_depth :
  forall (depth : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    buf6_is_empty t' = true ->
    back_ready_middle9_depth depth m ->
    exists m' t'',
      refill_t_K9Triple_fuel (S depth) h m t' = K9Triple h m' t'' /\
      buf6_size_ge 1 t''.
Proof.
  intros depth X h m t' Hempty Hready.
  apply buf6_eq_empty_of_is_empty in Hempty. subst t'.
  unfold refill_t_K9Triple_fuel.
  destruct Hready as (m_rest & cell & Heject & Hcell).
  rewrite Heject.
  destruct cell as [b|pre sm suf|sm].
  - eapply k9_with_back_fuel_exposed_ready_depth.
    + apply buf6_eject_inject.
    + destruct depth; cbn in Hcell |- *; exact Hcell.
  - eapply k9_with_back_fuel_exposed_ready_depth.
    + apply buf6_eject_inject.
    + destruct depth; cbn in Hcell |- *; exact Hcell.
  - destruct depth as [|depth']; [contradiction|].
    cbn in Hcell.
    destruct Hcell as (sm_rest & back_cell & Hsm & Hinner).
    eapply k9_with_back_fuel_exposed_ready_depth.
    + eapply k9_middle_inject_eject. exact Hsm.
    + cbn. exists sm_rest, back_cell. split; [exact Hsm|exact Hinner].
Qed.

Lemma refill_h_K9Triple_fuel_seq :
  forall (fuel : nat) (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    kcad9_to_list (refill_h_K9Triple_fuel fuel h' m t)
    = kelem9_flat_list (buf6_elems h')
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof.
  intros fuel X h' m t. unfold refill_h_K9Triple_fuel.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - assert (Hm := Hpop). apply stored9_flat_list_pop_some in Hm.
    destruct cell as [b|pre sm suf|sm].
    + rewrite k9_with_front_fuel_seq. rewrite stored9_flat_list_push.
      rewrite Hm. rewrite stored9_to_list_small.
      rewrite <- !app_assoc. reflexivity.
    + rewrite k9_with_front_fuel_seq. rewrite stored9_flat_list_push.
      rewrite k9_middle_push_seq. rewrite stored9_flat_list_push.
      rewrite Hm. rewrite !stored9_to_list_small. rewrite stored9_to_list_big.
      rewrite <- !app_assoc. reflexivity.
    + rewrite k9_with_front_fuel_seq. rewrite k9_middle_push_seq.
      rewrite Hm. rewrite stored9_to_list_middle.
      rewrite <- !app_assoc. reflexivity.
  - assert (Hmflat := stored9_flat_list_empty_of_pop_none X m Hpop).
    rewrite k9_with_front_fuel_seq. rewrite Hmflat. reflexivity.
Qed.

Lemma refill_t_K9Triple_fuel_seq :
  forall (fuel : nat) (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    kcad9_to_list (refill_t_K9Triple_fuel fuel h m t')
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t').
Proof.
  intros fuel X h m t'. unfold refill_t_K9Triple_fuel.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heject.
  - assert (Hm := Heject). apply stored9_flat_list_eject_some in Hm.
    destruct cell as [b|pre sm suf|sm].
    + rewrite k9_with_back_fuel_seq. rewrite stored9_flat_list_inject.
      rewrite Hm. rewrite stored9_to_list_small.
      rewrite <- !app_assoc. reflexivity.
    + rewrite k9_with_back_fuel_seq. rewrite stored9_flat_list_inject.
      rewrite k9_middle_inject_seq. rewrite stored9_flat_list_inject.
      rewrite Hm. rewrite !stored9_to_list_small. rewrite stored9_to_list_big.
      rewrite <- !app_assoc. reflexivity.
    + rewrite k9_with_back_fuel_seq. rewrite k9_middle_inject_seq.
      rewrite Hm. rewrite stored9_to_list_middle.
      rewrite <- !app_assoc. reflexivity.
  - assert (Hmflat := stored9_flat_list_empty_of_eject_none X m Heject).
    rewrite k9_with_back_fuel_seq. rewrite Hmflat. reflexivity.
Qed.

Theorem kcad9_pop_ocaml_shape_fuel_seq :
  forall (fuel : nat) (X : Type) (k : KCadeque9 X)
         (x : X) (k' : KCadeque9 X),
    kcad9_pop_ocaml_shape_fuel fuel k = Some (x, k') ->
    kcad9_to_list k = x :: kcad9_to_list k'.
Proof.
  intros fuel X [|b|h m t] x k' Hpop; cbn [kcad9_pop_ocaml_shape_fuel] in Hpop.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hb; [|discriminate].
    destruct e as [y|s]; [|discriminate].
    apply buf6_pop_seq_some in Hb. unfold buf6_to_list in Hb.
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Hpop as Hx Hk'; subst x k'.
    + apply buf6_eq_empty_of_is_empty in Hempty. subst b'.
      rewrite kcad9_to_list_simple. rewrite Hb.
      cbn [kelem9_flat_list kelem9_to_list]. reflexivity.
    + rewrite !kcad9_to_list_simple. rewrite Hb.
      cbn [kelem9_flat_list kelem9_to_list]. reflexivity.
  - destruct (buf6_pop h) as [[e h']|] eqn:Hh; [|discriminate].
    destruct e as [y|s]; [|discriminate].
    apply buf6_pop_seq_some in Hh. unfold buf6_to_list in Hh.
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k'.
    + rewrite !kcad9_to_list_triple. rewrite Hh.
      cbn [kelem9_flat_list kelem9_to_list]. reflexivity.
    + rewrite kcad9_to_list_triple. rewrite Hh.
      cbn [kelem9_flat_list kelem9_to_list].
      rewrite refill_h_K9Triple_fuel_seq.
      reflexivity.
Qed.

Theorem kcad9_eject_ocaml_shape_fuel_seq :
  forall (fuel : nat) (X : Type) (k : KCadeque9 X)
         (k' : KCadeque9 X) (x : X),
    kcad9_eject_ocaml_shape_fuel fuel k = Some (k', x) ->
    kcad9_to_list k = kcad9_to_list k' ++ [x].
Proof.
  intros fuel X [|b|h m t] k' x Heject;
    cbn [kcad9_eject_ocaml_shape_fuel] in Heject.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Hb; [|discriminate].
    destruct e as [y|s]; [|discriminate].
    apply buf6_eject_seq_some in Hb. unfold buf6_to_list in Hb.
    destruct (buf6_is_empty b') eqn:Hempty;
      injection Heject as Hk' Hx; subst x k'.
    + apply buf6_eq_empty_of_is_empty in Hempty. subst b'.
      rewrite kcad9_to_list_simple. rewrite Hb.
      cbn [kelem9_flat_list kelem9_to_list]. reflexivity.
    + rewrite !kcad9_to_list_simple. rewrite Hb.
      replace (kelem9_flat_list (buf6_elems b' ++ [XBase9 y]))
        with (kelem9_flat_list (buf6_elems b') ++ [y]).
      * reflexivity.
      * symmetry.
        change (kelem9_flat_list (buf6_elems (buf6_inject b' (XBase9 y)))
                = kelem9_flat_list (buf6_elems b') ++ [y]).
        rewrite kelem9_flat_list_inject. reflexivity.
  - destruct (buf6_eject t) as [[t' e]|] eqn:Ht; [|discriminate].
    destruct e as [y|s]; [|discriminate].
    apply buf6_eject_seq_some in Ht. unfold buf6_to_list in Ht.
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heject as Hk' Hx; subst x k'.
    + rewrite !kcad9_to_list_triple. rewrite Ht.
      replace (kelem9_flat_list (buf6_elems t' ++ [XBase9 y]))
        with (kelem9_flat_list (buf6_elems t') ++ [y]).
      2:{
        symmetry.
        change (kelem9_flat_list (buf6_elems (buf6_inject t' (XBase9 y)))
                = kelem9_flat_list (buf6_elems t') ++ [y]).
        rewrite kelem9_flat_list_inject. reflexivity.
      }
      rewrite <- !app_assoc. reflexivity.
    + rewrite kcad9_to_list_triple. rewrite Ht.
      replace (kelem9_flat_list (buf6_elems t' ++ [XBase9 y]))
        with (kelem9_flat_list (buf6_elems t') ++ [y]).
      2:{
        symmetry.
        change (kelem9_flat_list (buf6_elems (buf6_inject t' (XBase9 y)))
                = kelem9_flat_list (buf6_elems t') ++ [y]).
        rewrite kelem9_flat_list_inject. reflexivity.
      }
      rewrite refill_t_K9Triple_fuel_seq.
      rewrite <- !app_assoc. reflexivity.
Qed.

Definition kcad9_concat_ocaml_shape {X : Type}
  (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      let m_new :=
        match buf6_eject m2 with
        | Some (m2_rest, back_cell) =>
            let cell :=
              StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
            buf6_inject
              (buf6_inject m1 cell)
              back_cell
        | None =>
            let cell := StoredBig9 t1 buf6_empty h2 in
            buf6_inject m1 cell
        end in
      K9Triple h1 m_new t2
  end.

Theorem kcad9_concat_ocaml_shape_seq :
  forall (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat_ocaml_shape a b)
    = kcad9_to_list a ++ kcad9_to_list b.
Proof.
  intros X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_shape].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_triple, !kcad9_to_list_simple.
    cbn [stored9_flat_list buf6_elems]. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !kcad9_to_list_triple.
    destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject.
    + assert (Hm2 := Heject). apply stored9_flat_list_eject_some in Hm2.
      rewrite !stored9_flat_list_inject. rewrite stored9_to_list_big.
      rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
      rewrite Hm2. cbn [stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. reflexivity.
    + assert (Hm2flat := stored9_flat_list_empty_of_eject_none X m2 Heject).
      rewrite stored9_flat_list_inject. rewrite stored9_to_list_big.
      rewrite Hm2flat. cbn [stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. reflexivity.
Qed.

Definition kcad9_concat_ocaml_open_back_bridge_cell_base {X : Type}
  (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
  (back_cell : Stored9 X) : Stored9 X :=
  match back_cell with
  | StoredSmall9 b =>
      StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) b
  | StoredBig9 pre sm suf =>
      StoredBig9 t1
        (k9_middle_inject
          (buf6_inject (buf6_push (StoredSmall9 h2) m2_rest)
            (StoredSmall9 pre))
          sm)
        suf
  | StoredMiddle9 sm =>
      StoredBig9 t1
        (k9_middle_inject (buf6_push (StoredSmall9 h2) m2_rest) sm)
        buf6_empty
  end.

Lemma kcad9_concat_ocaml_open_back_bridge_cell_base_seq :
  forall (X : Type) (t1 h2 : Buf6 (KElem9 X))
         (m2_rest : Buf6 (Stored9 X)) (back_cell : Stored9 X),
    stored9_to_list
      (kcad9_concat_ocaml_open_back_bridge_cell_base
        t1 h2 m2_rest back_cell) =
    kelem9_flat_list (buf6_elems t1) ++
    kelem9_flat_list (buf6_elems h2) ++
    stored9_flat_list (buf6_elems m2_rest) ++
    stored9_to_list back_cell.
Proof.
  intros X t1 h2 m2_rest [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_open_back_bridge_cell_base].
  - rewrite stored9_to_list_big, stored9_flat_list_push, stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_to_list_big, k9_middle_inject_seq.
    rewrite stored9_flat_list_inject, stored9_flat_list_push.
    rewrite !stored9_to_list_small, stored9_to_list_big.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_to_list_big, k9_middle_inject_seq.
    rewrite stored9_flat_list_push, stored9_to_list_small, stored9_to_list_middle.
    cbn [kelem9_flat_list buf6_elems]. rewrite app_nil_r.
    rewrite <- !app_assoc. reflexivity.
Qed.

Fixpoint kcad9_concat_ocaml_open_back_bridge_cell_fuel {X : Type}
  (fuel : nat) (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
  (back_cell : Stored9 X) {struct fuel} : Stored9 X :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (sm_rest, inner_back) =>
          kcad9_concat_ocaml_open_back_bridge_cell_fuel fuel'
            t1 h2 (k9_middle_inject m2_rest sm_rest) inner_back
      | None =>
          StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty
      end
  | _, _ =>
      kcad9_concat_ocaml_open_back_bridge_cell_base t1 h2 m2_rest back_cell
  end.

Lemma kcad9_concat_ocaml_open_back_bridge_cell_fuel_seq :
  forall (fuel : nat) (X : Type) (t1 h2 : Buf6 (KElem9 X))
         (m2_rest : Buf6 (Stored9 X)) (back_cell : Stored9 X),
    stored9_to_list
      (kcad9_concat_ocaml_open_back_bridge_cell_fuel
        fuel t1 h2 m2_rest back_cell) =
    kelem9_flat_list (buf6_elems t1) ++
    kelem9_flat_list (buf6_elems h2) ++
    stored9_flat_list (buf6_elems m2_rest) ++
    stored9_to_list back_cell.
Proof.
  induction fuel as [|fuel IH]; intros X t1 h2 m2_rest [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_open_back_bridge_cell_fuel].
  - apply kcad9_concat_ocaml_open_back_bridge_cell_base_seq.
  - apply kcad9_concat_ocaml_open_back_bridge_cell_base_seq.
  - apply kcad9_concat_ocaml_open_back_bridge_cell_base_seq.
  - apply kcad9_concat_ocaml_open_back_bridge_cell_base_seq.
  - apply kcad9_concat_ocaml_open_back_bridge_cell_base_seq.
  - destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject.
    + rewrite IH. rewrite k9_middle_inject_seq.
      assert (Hsm := Heject). apply stored9_flat_list_eject_some in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      rewrite <- !app_assoc. reflexivity.
    + rewrite stored9_to_list_big, stored9_flat_list_push, stored9_to_list_small.
      assert (Hsm := Heject). apply stored9_flat_list_empty_of_eject_none in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      cbn [kelem9_flat_list buf6_elems]. rewrite app_nil_r.
      rewrite app_nil_r. reflexivity.
Qed.

Definition kcad9_concat_ocaml_open_back_shape_fuel {X : Type}
  (fuel : nat) (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      let m_new :=
        match buf6_eject m2 with
        | Some (m2_rest, back_cell) =>
            buf6_inject m1
              (kcad9_concat_ocaml_open_back_bridge_cell_fuel
                fuel t1 h2 m2_rest back_cell)
        | None =>
            let cell := StoredBig9 t1 buf6_empty h2 in
            buf6_inject m1 cell
        end in
      K9Triple h1 m_new t2
  end.

Theorem kcad9_concat_ocaml_open_back_shape_fuel_seq :
  forall (fuel : nat) (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat_ocaml_open_back_shape_fuel fuel a b)
    = kcad9_to_list a ++ kcad9_to_list b.
Proof.
  intros fuel X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_open_back_shape_fuel].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_triple, !kcad9_to_list_simple.
    cbn [stored9_flat_list buf6_elems]. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !kcad9_to_list_triple.
    destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject.
    + assert (Hm2 := Heject). apply stored9_flat_list_eject_some in Hm2.
      rewrite stored9_flat_list_inject.
      rewrite kcad9_concat_ocaml_open_back_bridge_cell_fuel_seq.
      rewrite Hm2. rewrite <- !app_assoc. reflexivity.
    + assert (Hm2flat := stored9_flat_list_empty_of_eject_none X m2 Heject).
      rewrite stored9_flat_list_inject. rewrite stored9_to_list_big.
      rewrite Hm2flat. cbn [stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. reflexivity.
Qed.

Fixpoint kcad9_concat_ocaml_selective_open_back_middle_fuel {X : Type}
  (fuel : nat) (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
  (m2_rest : Buf6 (Stored9 X)) (back_cell : Stored9 X) {struct fuel}
    : Buf6 (Stored9 X) :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (sm_rest, inner_back) =>
          kcad9_concat_ocaml_selective_open_back_middle_fuel fuel'
            m1 t1 h2 (k9_middle_inject m2_rest sm_rest) inner_back
      | None =>
          buf6_inject m1
            (StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty)
      end
  | _, StoredSmall9 b =>
      buf6_inject m1
        (StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) b)
  | _, StoredBig9 pre sm suf =>
      let cell :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      buf6_inject (buf6_inject m1 cell) (StoredBig9 pre sm suf)
  | _, StoredMiddle9 sm =>
      let cell :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      buf6_inject (buf6_inject m1 cell) (StoredMiddle9 sm)
  end.

Lemma kcad9_concat_ocaml_selective_open_back_middle_fuel_seq :
  forall (fuel : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (back_cell : Stored9 X),
    stored9_flat_list
      (buf6_elems
        (kcad9_concat_ocaml_selective_open_back_middle_fuel
          fuel m1 t1 h2 m2_rest back_cell)) =
    stored9_flat_list (buf6_elems m1) ++
    kelem9_flat_list (buf6_elems t1) ++
    kelem9_flat_list (buf6_elems h2) ++
    stored9_flat_list (buf6_elems m2_rest) ++
    stored9_to_list back_cell.
Proof.
  induction fuel as [|fuel IH]; intros X m1 t1 h2 m2_rest [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_selective_open_back_middle_fuel].
  - rewrite stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !stored9_flat_list_inject, !stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    cbn [stored9_flat_list buf6_elems].
    rewrite <- !app_assoc. reflexivity.
  - rewrite !stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite stored9_to_list_middle.
    cbn [stored9_flat_list buf6_elems]. rewrite app_nil_r.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !stored9_flat_list_inject, !stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    cbn [stored9_flat_list buf6_elems].
    rewrite <- !app_assoc. reflexivity.
  - destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject.
    + rewrite IH. rewrite k9_middle_inject_seq.
      assert (Hsm := Heject). apply stored9_flat_list_eject_some in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      rewrite <- !app_assoc. reflexivity.
    + rewrite stored9_flat_list_inject, stored9_to_list_big.
      rewrite stored9_flat_list_push, stored9_to_list_small.
      assert (Hsm := Heject). apply stored9_flat_list_empty_of_eject_none in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      cbn [kelem9_flat_list stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. rewrite !app_nil_r. reflexivity.
Qed.

Definition kcad9_concat_ocaml_selective_open_back_shape_fuel {X : Type}
  (fuel : nat) (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      let m_new :=
        match buf6_eject m2 with
        | Some (m2_rest, back_cell) =>
            kcad9_concat_ocaml_selective_open_back_middle_fuel
              fuel m1 t1 h2 m2_rest back_cell
        | None =>
            let cell := StoredBig9 t1 buf6_empty h2 in
            buf6_inject m1 cell
        end in
      K9Triple h1 m_new t2
  end.

Theorem kcad9_concat_ocaml_selective_open_back_shape_fuel_seq :
  forall (fuel : nat) (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat_ocaml_selective_open_back_shape_fuel fuel a b)
    = kcad9_to_list a ++ kcad9_to_list b.
Proof.
  intros fuel X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_selective_open_back_shape_fuel].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_triple, !kcad9_to_list_simple.
    cbn [stored9_flat_list buf6_elems]. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !kcad9_to_list_triple.
    destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject.
    + assert (Hm2 := Heject). apply stored9_flat_list_eject_some in Hm2.
      rewrite kcad9_concat_ocaml_selective_open_back_middle_fuel_seq.
      rewrite Hm2. rewrite <- !app_assoc. reflexivity.
    + assert (Hm2flat := stored9_flat_list_empty_of_eject_none X m2 Heject).
      rewrite stored9_flat_list_inject. rewrite stored9_to_list_big.
      rewrite Hm2flat. cbn [stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. reflexivity.
Qed.

Lemma kcad9_concat_ocaml_selective_open_back_middle_big_back_cell :
  forall (fuel : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (pre suf : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X)),
    kcad9_concat_ocaml_selective_open_back_middle_fuel
      fuel m1 t1 h2 m2_rest (StoredBig9 pre sm suf) =
    let cell :=
      StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
    buf6_inject (buf6_inject m1 cell) (StoredBig9 pre sm suf).
Proof.
  intros [|fuel] X m1 t1 h2 m2_rest pre suf sm; reflexivity.
Qed.

Definition kcad9_concat_ocaml_full_split_open_back_base {X : Type}
  (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
  (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
  (back_cell : Stored9 X) : Buf6 (Stored9 X) * Buf6 (KElem9 X) :=
  match back_cell with
  | StoredSmall9 b =>
      let cell := StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) b in
      (buf6_inject m1 cell, t2)
  | StoredMiddle9 sm =>
      let cell :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      (buf6_inject (buf6_inject m1 cell) (StoredMiddle9 sm), t2)
  | StoredBig9 pre sm suf =>
      let bridge :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      (buf6_concat
        (buf6_inject (buf6_inject m1 bridge) (StoredSmall9 pre))
        sm,
       buf6_concat suf t2)
  end.

Fixpoint kcad9_concat_ocaml_full_split_open_back_middle_fuel {X : Type}
  (fuel : nat) (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
  (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
  (back_cell : Stored9 X) {struct fuel}
    : Buf6 (Stored9 X) * Buf6 (KElem9 X) :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (sm_rest, inner_back) =>
          kcad9_concat_ocaml_full_split_open_back_middle_fuel fuel'
            m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back
      | None =>
          let cell :=
            StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
          (buf6_inject m1 cell, t2)
      end
  | _, _ =>
      kcad9_concat_ocaml_full_split_open_back_base
        m1 t1 h2 m2_rest t2 back_cell
  end.

Lemma kcad9_concat_ocaml_full_split_open_back_middle_fuel_seq :
  forall (fuel : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    let '(m_new, t_new) :=
      kcad9_concat_ocaml_full_split_open_back_middle_fuel
        fuel m1 t1 h2 m2_rest t2 back_cell in
    stored9_flat_list (buf6_elems m_new) ++
    kelem9_flat_list (buf6_elems t_new) =
    stored9_flat_list (buf6_elems m1) ++
    kelem9_flat_list (buf6_elems t1) ++
    kelem9_flat_list (buf6_elems h2) ++
    stored9_flat_list (buf6_elems m2_rest) ++
    stored9_to_list back_cell ++
    kelem9_flat_list (buf6_elems t2).
Proof.
  induction fuel as [|fuel IH]; intros X m1 t1 h2 m2_rest t2 [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_full_split_open_back_middle_fuel
         kcad9_concat_ocaml_full_split_open_back_base].
  - rewrite stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_flat_list_concat, !stored9_flat_list_inject.
    rewrite !stored9_to_list_big, stored9_to_list_small.
    rewrite stored9_flat_list_push, kelem9_flat_list_concat.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite stored9_to_list_middle.
    cbn [kelem9_flat_list buf6_elems]. rewrite app_nil_r.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_flat_list_inject, stored9_to_list_big.
    rewrite stored9_flat_list_push, stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored9_flat_list_concat, !stored9_flat_list_inject.
    rewrite !stored9_to_list_big, stored9_to_list_small.
    rewrite stored9_flat_list_push, kelem9_flat_list_concat.
    rewrite <- !app_assoc. reflexivity.
  - destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject.
    + specialize (IH X m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back).
      destruct
        (kcad9_concat_ocaml_full_split_open_back_middle_fuel
          fuel m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back)
        as [m_new t_new].
      cbn in IH. rewrite IH.
      rewrite k9_middle_inject_seq.
      assert (Hsm := Heject). apply stored9_flat_list_eject_some in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      rewrite <- !app_assoc. reflexivity.
    + rewrite stored9_flat_list_inject, stored9_to_list_big.
      rewrite stored9_flat_list_push, stored9_to_list_small.
      assert (Hsm := Heject). apply stored9_flat_list_empty_of_eject_none in Hsm.
      rewrite stored9_to_list_middle, Hsm.
      cbn [stored9_flat_list kelem9_flat_list buf6_elems].
      rewrite app_nil_r. try rewrite app_nil_r.
      rewrite <- !app_assoc.
      reflexivity.
Qed.

Definition kcad9_concat_ocaml_full_split_open_back_shape_fuel {X : Type}
  (fuel : nat) (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      match buf6_eject m2 with
      | Some (m2_rest, back_cell) =>
          let '(m_new, t_new) :=
            kcad9_concat_ocaml_full_split_open_back_middle_fuel
              fuel m1 t1 h2 m2_rest t2 back_cell in
          K9Triple h1 m_new t_new
      | None =>
          let cell := StoredBig9 t1 buf6_empty h2 in
          K9Triple h1 (buf6_inject m1 cell) t2
      end
  end.

Theorem kcad9_concat_ocaml_full_split_open_back_shape_fuel_seq :
  forall (fuel : nat) (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat_ocaml_full_split_open_back_shape_fuel fuel a b)
    = kcad9_to_list a ++ kcad9_to_list b.
Proof.
  intros fuel X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_full_split_open_back_shape_fuel].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_triple, !kcad9_to_list_simple.
    cbn [stored9_flat_list buf6_elems]. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_push. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite stored9_flat_list_inject. rewrite stored9_to_list_small.
    rewrite <- !app_assoc. reflexivity.
  - rewrite !kcad9_to_list_triple.
    destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject.
    + pose proof
        (kcad9_concat_ocaml_full_split_open_back_middle_fuel_seq
           fuel X m1 t1 h2 m2_rest t2 back_cell) as Hsplit.
      destruct
        (kcad9_concat_ocaml_full_split_open_back_middle_fuel
          fuel m1 t1 h2 m2_rest t2 back_cell)
        as [m_new t_new].
      cbn in Hsplit.
      match goal with
      | |- _ = ?R =>
          change
            (kelem9_flat_list (buf6_elems h1) ++
             (stored9_flat_list (buf6_elems m_new) ++
              kelem9_flat_list (buf6_elems t_new)) = R)
      end.
      rewrite Hsplit.
      assert (Hm2 := Heject). apply stored9_flat_list_eject_some in Hm2.
      rewrite Hm2. rewrite <- !app_assoc. reflexivity.
    + try rewrite kcad9_to_list_triple.
      assert (Hm2flat := stored9_flat_list_empty_of_eject_none X m2 Heject).
      rewrite stored9_flat_list_inject. rewrite stored9_to_list_big.
      rewrite Hm2flat. cbn [stored9_flat_list buf6_elems].
      rewrite <- !app_assoc. reflexivity.
Qed.

Definition kcad9_shipped_inject_stored_cells {X : Type}
    (rest cells : Buf6 (Stored9 X)) : Buf6 (Stored9 X) :=
  fold_left buf6_inject (buf6_elems cells) rest.

Definition kcad9_shipped_prepend_kelem_cells {X : Type}
    (prefix suffix : Buf6 (KElem9 X)) : Buf6 (KElem9 X) :=
  fold_right buf6_push suffix (buf6_elems prefix).

Lemma kcad9_shipped_inject_stored_cells_eq_concat :
  forall (X : Type) (rest cells : Buf6 (Stored9 X)),
    kcad9_shipped_inject_stored_cells rest cells =
    buf6_concat rest cells.
Proof.
  intros X [rest] [cells].
  unfold kcad9_shipped_inject_stored_cells, buf6_elems.
  revert rest.
  induction cells as [|cell cells IH]; intros rest.
  - cbn [fold_left buf6_concat buf6_elems].
    unfold buf6_concat, buf6_elems. rewrite app_nil_r. reflexivity.
  - cbn [fold_left].
    change
      (fold_left (@buf6_inject (Stored9 X)) cells
         {| buf6_elems := rest ++ [cell] |} =
       buf6_concat {| buf6_elems := rest |} {| buf6_elems := cell :: cells |}).
    rewrite IH.
    unfold buf6_concat, buf6_elems.
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma kcad9_shipped_prepend_kelem_cells_eq_concat :
  forall (X : Type) (prefix suffix : Buf6 (KElem9 X)),
    kcad9_shipped_prepend_kelem_cells prefix suffix =
    buf6_concat prefix suffix.
Proof.
  intros X [prefix] [suffix].
  unfold kcad9_shipped_prepend_kelem_cells, buf6_elems.
  induction prefix as [|cell prefix IH].
  - reflexivity.
  - cbn [fold_right].
    rewrite IH.
    reflexivity.
Qed.

Definition kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
    {X : Type}
    (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
    (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
    (back_cell : Stored9 X) : Buf6 (Stored9 X) * Buf6 (KElem9 X) :=
  match back_cell with
  | StoredSmall9 b =>
      let cell := StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) b in
      (buf6_inject m1 cell, t2)
  | StoredMiddle9 sm =>
      let cell :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      (buf6_inject (buf6_inject m1 cell) (StoredMiddle9 sm), t2)
  | StoredBig9 pre sm suf =>
      let bridge :=
        StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
      (kcad9_shipped_inject_stored_cells
        (buf6_inject (buf6_inject m1 bridge) (StoredSmall9 pre))
        sm,
       kcad9_shipped_prepend_kelem_cells suf t2)
  end.

Lemma kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq :
  forall (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
      m1 t1 h2 m2_rest t2 back_cell =
    kcad9_concat_ocaml_full_split_open_back_base
      m1 t1 h2 m2_rest t2 back_cell.
Proof.
  intros X m1 t1 h2 m2_rest t2 [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
         kcad9_concat_ocaml_full_split_open_back_base].
  - reflexivity.
  - rewrite kcad9_shipped_inject_stored_cells_eq_concat.
    rewrite kcad9_shipped_prepend_kelem_cells_eq_concat.
    reflexivity.
  - reflexivity.
Qed.

Fixpoint kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
    {X : Type}
    (fuel : nat) (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
    (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
    (back_cell : Stored9 X) {struct fuel}
    : Buf6 (Stored9 X) * Buf6 (KElem9 X) :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (sm_rest, inner_back) =>
          kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
            fuel' m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back
      | None =>
          let cell :=
            StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
          (buf6_inject m1 cell, t2)
      end
  | _, _ =>
      kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
        m1 t1 h2 m2_rest t2 back_cell
  end.

Lemma kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_eq :
  forall (fuel : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
      fuel m1 t1 h2 m2_rest t2 back_cell =
    kcad9_concat_ocaml_full_split_open_back_middle_fuel
      fuel m1 t1 h2 m2_rest t2 back_cell.
Proof.
  induction fuel as [|fuel IH]; intros X m1 t1 h2 m2_rest t2
    [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
         kcad9_concat_ocaml_full_split_open_back_middle_fuel].
  - apply kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq.
  - apply kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq.
  - apply kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq.
  - apply kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq.
  - apply kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_eq.
  - destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject.
    + apply IH.
    + reflexivity.
Qed.

Definition kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds
    {X : Type} (fuel : nat) (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      match buf6_eject m2 with
      | Some (m2_rest, back_cell) =>
          let '(m_new, t_new) :=
            kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
              fuel m1 t1 h2 m2_rest t2 back_cell in
          K9Triple h1 m_new t_new
      | None =>
          let cell := StoredBig9 t1 buf6_empty h2 in
          K9Triple h1 (buf6_inject m1 cell) t2
      end
  end.

Theorem kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_eq :
  forall (fuel : nat) (X : Type) (a b : KCadeque9 X),
    kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds
      fuel a b =
    kcad9_concat_ocaml_full_split_open_back_shape_fuel fuel a b.
Proof.
  intros fuel X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds
         kcad9_concat_ocaml_full_split_open_back_shape_fuel];
    try reflexivity.
  destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject;
    [|reflexivity].
  rewrite
    kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_eq.
  reflexivity.
Qed.

Definition k9_middle_inject_primitive_cost {X : Type}
    (sm : Buf6 (Stored9 X)) : nat :=
  1 + if buf6_is_empty sm then 0 else 1.

Theorem k9_middle_inject_primitive_cost_bound :
  forall (X : Type) (sm : Buf6 (Stored9 X)),
    k9_middle_inject_primitive_cost sm <= 2.
Proof.
  intros X sm. unfold k9_middle_inject_primitive_cost.
  destruct (buf6_is_empty sm); lia.
Qed.

Definition kcad9_shipped_full_split_base_sources_size_le
    {X : Type} (bound : nat) (back_cell : Stored9 X) : Prop :=
  match back_cell with
  | StoredBig9 _ sm suf => buf6_size sm <= bound /\ buf6_size suf <= bound
  | _ => True
  end.

Fixpoint kcad9_shipped_full_split_middle_sources_size_le
    {X : Type} (fuel bound : nat) (back_cell : Stored9 X)
    {struct fuel} : Prop :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (_, inner_back) =>
          kcad9_shipped_full_split_middle_sources_size_le
            fuel' bound inner_back
      | None => True
      end
  | _, _ =>
      kcad9_shipped_full_split_base_sources_size_le bound back_cell
  end.

Definition kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost
    {X : Type} (back_cell : Stored9 X) : nat :=
  match back_cell with
  | StoredSmall9 _ => 2
  | StoredMiddle9 _ => 3
  | StoredBig9 _ sm suf => 3 + buf6_size sm + buf6_size suf
  end.

Definition kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed
    {X : Type}
    (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
    (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
    (back_cell : Stored9 X)
    : (Buf6 (Stored9 X) * Buf6 (KElem9 X)) * nat :=
  (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
     m1 t1 h2 m2_rest t2 back_cell,
   kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost
     back_cell).

Theorem kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_result :
  forall (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    fst
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed
         m1 t1 h2 m2_rest t2 back_cell) =
    kcad9_concat_ocaml_full_split_open_back_base_shipped_folds
      m1 t1 h2 m2_rest t2 back_cell.
Proof.
  reflexivity.
Qed.

Theorem kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost :
  forall (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    snd
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed
         m1 t1 h2 m2_rest t2 back_cell) =
    kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost back_cell.
Proof.
  reflexivity.
Qed.

Theorem kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound :
  forall (bound : nat) (X : Type) (back_cell : Stored9 X),
    kcad9_shipped_full_split_base_sources_size_le bound back_cell ->
    kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost back_cell <=
      3 + bound + bound.
Proof.
  intros bound X [b|pre sm suf|sm] Hbound; cbn in Hbound |- *; lia.
Qed.

Fixpoint kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
    {X : Type}
    (fuel : nat) (m1 : Buf6 (Stored9 X)) (t1 h2 : Buf6 (KElem9 X))
    (m2_rest : Buf6 (Stored9 X)) (t2 : Buf6 (KElem9 X))
    (back_cell : Stored9 X) {struct fuel}
    : (Buf6 (Stored9 X) * Buf6 (KElem9 X)) * nat :=
  match fuel, back_cell with
  | S fuel', StoredMiddle9 sm =>
      match buf6_eject sm with
      | Some (sm_rest, inner_back) =>
          let '(result, cost) :=
            kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
              fuel' m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2
              inner_back in
          (result, 1 + k9_middle_inject_primitive_cost sm_rest + cost)
      | None =>
          let cell :=
            StoredBig9 t1 (buf6_push (StoredSmall9 h2) m2_rest) buf6_empty in
          ((buf6_inject m1 cell, t2), 3)
      end
  | _, _ =>
      kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed
        m1 t1 h2 m2_rest t2 back_cell
  end.

Theorem kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed_result :
  forall (fuel : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    fst
      (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
         fuel m1 t1 h2 m2_rest t2 back_cell) =
    kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
      fuel m1 t1 h2 m2_rest t2 back_cell.
Proof.
  induction fuel as [|fuel IH]; intros X m1 t1 h2 m2_rest t2
    [b|pre sm suf|sm];
    cbn [kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
         kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
         kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed];
    try reflexivity.
  destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject;
    [|reflexivity].
  specialize
    (IH X m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back).
  destruct
    (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
       fuel m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back)
    as [result cost] eqn:Hcosted.
  cbn in IH |- *.
  exact IH.
Qed.

Theorem kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_cost_bound :
  forall (fuel bound : nat) (X : Type) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2_rest : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)) (back_cell : Stored9 X),
    kcad9_shipped_full_split_middle_sources_size_le fuel bound back_cell ->
    snd
      (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
         fuel m1 t1 h2 m2_rest t2 back_cell) <=
      fuel + fuel + fuel + 3 + bound + bound.
Proof.
  induction fuel as [|fuel IH]; intros bound X m1 t1 h2 m2_rest t2
    [b|pre sm suf|sm] Hbound;
    cbn [kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
         kcad9_shipped_full_split_middle_sources_size_le] in Hbound |- *.
  - rewrite kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound
         bound X (StoredSmall9 b) Hbound).
    lia.
  - rewrite kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound
         bound X (StoredBig9 pre sm suf) Hbound).
    lia.
  - rewrite kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound
         bound X (StoredMiddle9 sm) Hbound).
    lia.
  - rewrite kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound
         bound X (StoredSmall9 b) Hbound).
    lia.
  - rewrite kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_costed_cost.
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_base_shipped_folds_cost_bound
         bound X (StoredBig9 pre sm suf) Hbound).
    lia.
  - destruct (buf6_eject sm) as [[sm_rest inner_back]|] eqn:Heject.
    + specialize
        (IH bound X m1 t1 h2 (k9_middle_inject m2_rest sm_rest)
           t2 inner_back Hbound).
      pose proof (k9_middle_inject_primitive_cost_bound X sm_rest).
      destruct
        (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
           fuel m1 t1 h2 (k9_middle_inject m2_rest sm_rest) t2 inner_back)
        as [result cost] eqn:Hcosted.
      cbn [snd] in IH |- *.
      assert (Hstep : 1 + k9_middle_inject_primitive_cost sm_rest <= 3)
        by lia.
      change
        (1 + k9_middle_inject_primitive_cost sm_rest + cost <=
         S fuel + S fuel + S fuel + 3 + bound + bound).
      assert (Hcost :
        cost <= fuel + fuel + fuel + 3 + bound + bound) by exact IH.
      eapply Nat.le_trans.
      * apply Nat.add_le_mono; [exact Hstep|exact Hcost].
      * lia.
    + cbn [snd]. lia.
Qed.

Definition kcad9_shipped_full_split_shape_sources_size_le
    {X : Type} (fuel bound : nat) (a b : KCadeque9 X) : Prop :=
  match a, b with
  | K9Triple _ _ _, K9Triple _ m2 _ =>
      match buf6_eject m2 with
      | Some (_, back_cell) =>
          kcad9_shipped_full_split_middle_sources_size_le
            fuel bound back_cell
      | None => True
      end
  | _, _ => True
  end.

Definition kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
    {X : Type} (fuel : nat) (a b : KCadeque9 X)
    : KCadeque9 X * nat :=
  match a, b with
  | K9Empty, _ => (b, 1)
  | _, K9Empty => (a, 1)
  | K9Simple ba, K9Simple bb =>
      (K9Triple ba buf6_empty bb, 1)
  | K9Simple ba, K9Triple h2 m2 t2 =>
      (K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2, 2)
  | K9Triple h1 m1 t1, K9Simple bb =>
      (K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb, 2)
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      match buf6_eject m2 with
      | Some (m2_rest, back_cell) =>
          let '(mt, cost) :=
            kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
              fuel m1 t1 h2 m2_rest t2 back_cell in
          let '(m_new, t_new) := mt in
          (K9Triple h1 m_new t_new, 1 + cost)
      | None =>
          let cell := StoredBig9 t1 buf6_empty h2 in
          (K9Triple h1 (buf6_inject m1 cell) t2, 2)
      end
  end.

Theorem kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed_result :
  forall (fuel : nat) (X : Type) (a b : KCadeque9 X),
    fst
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
         fuel a b) =
    kcad9_concat_ocaml_full_split_open_back_shape_fuel fuel a b.
Proof.
  intros fuel X [|ba|h1 m1 t1] [|bb|h2 m2 t2];
    cbn [kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
         kcad9_concat_ocaml_full_split_open_back_shape_fuel];
    try reflexivity.
  destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject;
    [|reflexivity].
  destruct
    (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
       fuel m1 t1 h2 m2_rest t2 back_cell)
    as [[m_new t_new] cost] eqn:Hcosted.
  assert (Hresult :
    (m_new, t_new) =
    kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
      fuel m1 t1 h2 m2_rest t2 back_cell).
  { pose proof
      (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed_result
         fuel X m1 t1 h2 m2_rest t2 back_cell) as Hresult.
    rewrite Hcosted in Hresult. exact Hresult. }
  rewrite <- kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_eq.
  change
    (K9Triple h1 m_new t_new =
     let '(m_new0, t_new0) :=
       kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds
         fuel m1 t1 h2 m2_rest t2 back_cell in
     K9Triple h1 m_new0 t_new0).
  rewrite <- Hresult.
  reflexivity.
Qed.

Theorem kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_cost_bound :
  forall (fuel bound : nat) (X : Type) (a b : KCadeque9 X),
    kcad9_shipped_full_split_shape_sources_size_le fuel bound a b ->
    snd
      (kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
         fuel a b) <=
      fuel + fuel + fuel + 4 + bound + bound.
Proof.
  intros fuel bound X a b Hbound.
  destruct a as [|ba|h1 m1 t1];
    destruct b as [|bb|h2 m2 t2];
    cbn [snd
         kcad9_concat_ocaml_full_split_open_back_shape_fuel_shipped_folds_costed
         kcad9_shipped_full_split_shape_sources_size_le] in Hbound |- *.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject;
      [|cbn [snd]; lia].
    pose proof
      (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_cost_bound
         fuel bound X m1 t1 h2 m2_rest t2 back_cell Hbound)
      as Hcost.
    destruct
      (kcad9_concat_ocaml_full_split_open_back_middle_fuel_shipped_folds_costed
         fuel m1 t1 h2 m2_rest t2 back_cell)
      as [mt cost] eqn:Hcosted.
    destruct mt as [m_new t_new].
    cbn [snd] in Hcost |- *.
    lia.
Qed.

Definition kcad9_concat_direct_big_shape {X : Type}
  (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a
  | K9Simple ba, K9Simple bb =>
      K9Triple ba buf6_empty bb
  | K9Simple ba, K9Triple h2 m2 t2 =>
      K9Triple ba (buf6_push (StoredSmall9 h2) m2) t2
  | K9Triple h1 m1 t1, K9Simple bb =>
      K9Triple h1 (buf6_inject m1 (StoredSmall9 t1)) bb
  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      let cell := StoredBig9 t1 m2 h2 in
      K9Triple h1 (buf6_inject m1 cell) t2
  end.

Theorem kcad9_concat_direct_big_shape_seq_counterexample :
  kcad9_to_list
    (kcad9_concat_direct_big_shape
       (K9Triple (mkBuf6 [XBase9 1]) buf6_empty (mkBuf6 [XBase9 2]))
       (K9Triple (mkBuf6 [XBase9 3])
          (mkBuf6 [StoredSmall9 (mkBuf6 [XBase9 4])])
          (mkBuf6 [XBase9 5])))
  <>
  kcad9_to_list
    (K9Triple (mkBuf6 [XBase9 1]) buf6_empty (mkBuf6 [XBase9 2]))
  ++
  kcad9_to_list
    (K9Triple (mkBuf6 [XBase9 3])
       (mkBuf6 [StoredSmall9 (mkBuf6 [XBase9 4])])
       (mkBuf6 [XBase9 5])).
Proof.
  cbn [kcad9_concat_direct_big_shape kcad9_to_list stored9_to_list
       kelem9_to_list buf6_elems].
  discriminate.
Qed.

Theorem kcad9_concat_ocaml_shape_tt_back_ready_depth :
  forall (depth : nat) (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 : Buf6 (KElem9 X)) (m2 : Buf6 (Stored9 X))
         (t2 : Buf6 (KElem9 X)),
    back_ready_middle9_depth depth m2 ->
    match kcad9_concat_ocaml_shape (K9Triple h1 m1 t1) (K9Triple h2 m2 t2) with
    | K9Triple _ m_new _ => back_ready_middle9_depth depth m_new
    | _ => False
    end.
Proof.
  intros depth X h1 m1 t1 h2 m2 t2
    (m2_rest & back_cell & Heject & Hback).
  cbn [kcad9_concat_ocaml_shape]. rewrite Heject.
  apply buf6_inject_back_ready_stored9_depth. exact Hback.
Qed.

Theorem kcad9_concat_ocaml_shape_tt_empty_right_middle_back_ready :
  forall (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 t2 : Buf6 (KElem9 X)),
    buf6_size_ge 1 h2 ->
    match kcad9_concat_ocaml_shape
            (K9Triple h1 m1 t1)
            (K9Triple h2 buf6_empty t2) with
    | K9Triple _ m_new _ => back_ready_middle9_depth 0 m_new
    | _ => False
    end.
Proof.
  intros X h1 m1 t1 h2 t2 Hh2.
  cbn [kcad9_concat_ocaml_shape k9_middle_inject buf6_is_empty buf6_empty].
  apply buf6_inject_back_ready_stored9_depth.
  cbn [back_ready_stored9_depth back_ready_stored9].
  exact Hh2.
Qed.

Theorem kcad9_concat_ocaml_shape_tt_back_nested_ready_depth :
  forall (depth : nat) (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 t2 b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    match kcad9_concat_ocaml_shape
            (K9Triple h1 m1 t1)
            (K9Triple h2 (back_nested_middle9 depth (StoredSmall9 b)) t2) with
    | K9Triple _ m_new _ => back_ready_middle9_depth depth m_new
    | _ => False
    end.
Proof.
  intros depth X h1 m1 t1 h2 t2 b Hge.
  apply kcad9_concat_ocaml_shape_tt_back_ready_depth.
  apply back_nested_middle9_ready_depth. exact Hge.
Qed.

Theorem kcad9_concat_ocaml_shape_tt_back_nested_not_ready_too_shallow :
  forall (depth fuel_depth : nat) (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 t2 b : Buf6 (KElem9 X)),
    fuel_depth < depth ->
    ~ match kcad9_concat_ocaml_shape
              (K9Triple h1 m1 t1)
              (K9Triple h2 (back_nested_middle9 depth (StoredSmall9 b)) t2) with
      | K9Triple _ m_new _ => back_ready_middle9_depth fuel_depth m_new
      | _ => False
      end.
Proof.
  intros depth fuel_depth X h1 m1 t1 h2 t2 b Hlt Hready.
  cbn [kcad9_concat_ocaml_shape] in Hready.
  destruct (buf6_eject (back_nested_middle9 depth (StoredSmall9 b)))
    as [[m_rest cell]|] eqn:Heject.
  - destruct Hready as (out_rest & out_cell & Hout & Hcell).
    rewrite buf6_eject_inject in Hout. injection Hout as _ Hcell_eq.
    subst out_cell.
    assert (Horig :
      back_ready_middle9_depth fuel_depth
        (back_nested_middle9 depth (StoredSmall9 b))).
    { exists m_rest, cell. split; assumption. }
    exact (back_nested_middle9_not_ready_too_shallow
             depth fuel_depth X b Hlt Horig).
  - destruct depth;
      cbn [back_nested_middle9 buf6_inject buf6_empty buf6_eject buf6_elems]
        in Heject;
      discriminate.
Qed.

Theorem kcad9_concat_ocaml_shape_tt_back_nested_exceeds_any_depth :
  forall (fuel_depth : nat) (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 t2 b : Buf6 (KElem9 X)),
    ~ match kcad9_concat_ocaml_shape
              (K9Triple h1 m1 t1)
              (K9Triple h2
                 (back_nested_middle9 (S fuel_depth) (StoredSmall9 b))
                 t2) with
      | K9Triple _ m_new _ => back_ready_middle9_depth fuel_depth m_new
      | _ => False
      end.
Proof.
  intros fuel_depth X h1 m1 t1 h2 t2 b Hready.
  assert (Hlt : fuel_depth < S fuel_depth) by lia.
  exact (kcad9_concat_ocaml_shape_tt_back_nested_not_ready_too_shallow
           (S fuel_depth) fuel_depth X h1 m1 t1 h2 t2 b
           Hlt Hready).
Qed.

Theorem kcad9_concat_ocaml_shape_tt_back_nested_exceeds_ready_depth :
  forall (fuel_depth : nat) (X : Type)
         (h1 : Buf6 (KElem9 X)) (m1 : Buf6 (Stored9 X))
         (t1 h2 t2 b : Buf6 (KElem9 X)),
    buf6_size_ge 1 b ->
    match kcad9_concat_ocaml_shape
            (K9Triple h1 m1 t1)
            (K9Triple h2
               (back_nested_middle9 (S fuel_depth) (StoredSmall9 b))
               t2) with
    | K9Triple _ m_new _ => back_ready_middle9_depth (S fuel_depth) m_new
    | _ => False
    end.
Proof.
  intros fuel_depth X h1 m1 t1 h2 t2 b Hge.
  apply kcad9_concat_ocaml_shape_tt_back_nested_ready_depth.
  exact Hge.
Qed.

Theorem kcad9_push_inv_ocaml_boundaries :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    inv_kcad9_ocaml_boundaries k ->
    inv_kcad9_ocaml_boundaries (kcad9_push x k).
Proof.
  intros X x [|b|h m t] Hinv; cbn [inv_kcad9_ocaml_boundaries kcad9_push] in *.
  - unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - apply buf6_size_ge_push_preserve. exact Hinv.
  - destruct Hinv as [Hh Ht].
    split; [apply buf6_size_ge_push_preserve; exact Hh|exact Ht].
Qed.

Theorem kcad9_inject_inv_ocaml_boundaries :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    inv_kcad9_ocaml_boundaries k ->
    inv_kcad9_ocaml_boundaries (kcad9_inject k x).
Proof.
  intros X [|b|h m t] x Hinv; cbn [inv_kcad9_ocaml_boundaries kcad9_inject] in *.
  - unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - apply buf6_size_ge_inject_preserve. exact Hinv.
  - destruct Hinv as [Hh Ht].
    split; [exact Hh|apply buf6_size_ge_inject_preserve; exact Ht].
Qed.

Theorem kcad9_concat_ocaml_shape_inv_boundaries :
  forall (X : Type) (a b : KCadeque9 X),
    inv_kcad9_ocaml_boundaries a ->
    inv_kcad9_ocaml_boundaries b ->
    inv_kcad9_ocaml_boundaries (kcad9_concat_ocaml_shape a b).
Proof.
  intros X [|ba|h1 m1 t1] [|bb|h2 m2 t2] Ha Hb;
    cbn [inv_kcad9_ocaml_boundaries kcad9_concat_ocaml_shape] in *.
  - exact I.
  - exact Hb.
  - exact Hb.
  - exact Ha.
  - split; assumption.
  - destruct Hb as [_ Ht2]. split; assumption.
  - exact Ha.
  - destruct Ha as [Hh1 _]. split; assumption.
  - destruct Ha as [Hh1 _]. destruct Hb as [_ Ht2].
    split; assumption.
Qed.

Theorem kcad9_push_ocaml_deep_xbase :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    inv_kcad9_ocaml_deep_xbase k ->
    inv_kcad9_ocaml_deep_xbase (kcad9_push x k).
Proof.
  intros X x [|b|h m t] Hinv;
    cbn [inv_kcad9_ocaml_deep_xbase kcad9_push] in *.
  - constructor; [exact I|constructor].
  - apply all_xbase9_push_base. exact Hinv.
  - destruct Hinv as [Hh [Hm Ht]].
    repeat split; try assumption.
    apply all_xbase9_push_base. exact Hh.
Qed.

Theorem kcad9_inject_ocaml_deep_xbase :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    inv_kcad9_ocaml_deep_xbase k ->
    inv_kcad9_ocaml_deep_xbase (kcad9_inject k x).
Proof.
  intros X [|b|h m t] x Hinv;
    cbn [inv_kcad9_ocaml_deep_xbase kcad9_inject] in *.
  - constructor; [exact I|constructor].
  - apply all_xbase9_inject_base. exact Hinv.
  - destruct Hinv as [Hh [Hm Ht]].
    repeat split; try assumption.
    apply all_xbase9_inject_base. exact Ht.
Qed.

Theorem kcad9_concat_ocaml_shape_inv_deep_xbase :
  forall (X : Type) (a b : KCadeque9 X),
    inv_kcad9_ocaml_deep_xbase a ->
    inv_kcad9_ocaml_deep_xbase b ->
    inv_kcad9_ocaml_deep_xbase (kcad9_concat_ocaml_shape a b).
Proof.
  intros X [|ba|h1 m1 t1] [|bb|h2 m2 t2] Ha Hb;
    cbn [inv_kcad9_ocaml_deep_xbase kcad9_concat_ocaml_shape] in *.
  - exact I.
  - exact Hb.
  - exact Hb.
  - exact Ha.
  - repeat split; try assumption.
    apply xbase_middle9_deep_empty.
  - destruct Hb as [Hh2 [Hm2 Ht2]].
    repeat split; try assumption.
    apply xbase_middle9_deep_push; [exact Hh2|exact Hm2].
  - exact Ha.
  - destruct Ha as [Hh1 [Hm1 Ht1]].
    repeat split; try assumption.
    apply xbase_middle9_deep_inject; [exact Hm1|exact Ht1].
  - destruct Ha as [Hh1 [Hm1 Ht1]].
    destruct Hb as [Hh2 [Hm2 Ht2]].
    repeat split; try assumption.
    destruct (buf6_eject m2) as [[m2_rest back_cell]|] eqn:Heject.
    + destruct (xbase_middle9_deep_eject X m2 m2_rest back_cell Hm2 Heject)
        as [Hm2_rest Hback_cell].
      apply xbase_middle9_deep_inject; [|exact Hback_cell].
      apply xbase_middle9_deep_inject; [exact Hm1|].
      apply xbase_stored9_deep_big.
      * exact Ht1.
      * apply xbase_middle9_deep_push.
        -- exact Hh2.
        -- exact Hm2_rest.
      * apply all_xbase9_empty.
    + apply xbase_middle9_deep_inject; [exact Hm1|].
      apply xbase_stored9_deep_big.
      * exact Ht1.
      * apply xbase_middle9_deep_empty.
      * exact Hh2.
Qed.
