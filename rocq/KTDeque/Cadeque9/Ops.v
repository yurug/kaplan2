(** * Module: KTDeque.Cadeque9.Ops — paper-faithful KT99 §6
      operations on the Cadeque9 type family.

    Phase 4 (this file, initial drop): push and inject.
    Push and inject only ever grow buffers, so under wf they trivially
    preserve [wf_kcad9_strong].

    Phases 5 / 6 to follow:
      pop / eject (with the refill rebalance keyed off the ≥ 5 boundary)
      concat     (trivially O(1) under the ≥ 5 / ≥ 3 invariants)
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque9  Require Import Model WFStrong.

(** ** Push.

    On K9Empty: become K9Simple with a 1-element buffer.
    On K9Simple: grow the single buffer.
    On K9Triple: grow the head boundary buffer. *)

Definition kcad9_push {X : Type} (x : X) (k : KCadeque9 X) : KCadeque9 X :=
  match k with
  | K9Empty        => K9Simple (mkBuf6 [XBase9 x])
  | K9Simple b     => K9Simple (buf6_push (XBase9 x) b)
  | K9Triple h m t => K9Triple (buf6_push (XBase9 x) h) m t
  end.

(** ** Inject. *)

Definition kcad9_inject {X : Type} (k : KCadeque9 X) (x : X) : KCadeque9 X :=
  match k with
  | K9Empty        => K9Simple (mkBuf6 [XBase9 x])
  | K9Simple b     => K9Simple (buf6_inject b (XBase9 x))
  | K9Triple h m t => K9Triple h m (buf6_inject t (XBase9 x))
  end.

Definition k9_middle_push {X : Type}
  (sm rest : Buf6 (Stored9 X)) : Buf6 (Stored9 X) :=
  if buf6_is_empty sm then rest else buf6_push (StoredMiddle9 sm) rest.

Definition k9_middle_inject {X : Type}
  (rest sm : Buf6 (Stored9 X)) : Buf6 (Stored9 X) :=
  if buf6_is_empty sm then rest else buf6_inject rest (StoredMiddle9 sm).

(* ========================================================================== *)
(* Sequence preservation.                                                     *)
(* ========================================================================== *)

(** A helper: [kelem9_flat_list] on a buf6's elements.  Mirrors the
    [Cadeque8/Seq.v] pattern; lets us fold the inline-fix-go form
    that the [Model.v] flattener uses. *)
Definition kelem9_flat_list {X : Type} (l : list (KElem9 X)) : list X :=
  (fix go (l : list (KElem9 X)) : list X :=
     match l with
     | []      => []
     | e :: es => kelem9_to_list e ++ go es
     end) l.

Definition stored9_flat_list {X : Type} (l : list (Stored9 X)) : list X :=
  (fix go (l : list (Stored9 X)) : list X :=
     match l with
     | []      => []
     | s :: ss => stored9_to_list s ++ go ss
     end) l.

Lemma kcad9_to_list_simple :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    kcad9_to_list (K9Simple b) = kelem9_flat_list (buf6_elems b).
Proof. intros; reflexivity. Qed.

Lemma kcad9_to_list_triple :
  forall (X : Type) (h : Buf6 (KElem9 X)) (m : Buf6 (Stored9 X))
         (t : Buf6 (KElem9 X)),
    kcad9_to_list (K9Triple h m t)
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof. intros; reflexivity. Qed.

Lemma kelem9_flat_list_push :
  forall (X : Type) (e : KElem9 X) (b : Buf6 (KElem9 X)),
    kelem9_flat_list (buf6_elems (buf6_push e b))
    = kelem9_to_list e ++ kelem9_flat_list (buf6_elems b).
Proof.
  intros X e [xs]. unfold buf6_push, buf6_elems, kelem9_flat_list. cbn.
  reflexivity.
Qed.

Lemma kelem9_flat_list_inject :
  forall (X : Type) (b : Buf6 (KElem9 X)) (e : KElem9 X),
    kelem9_flat_list (buf6_elems (buf6_inject b e))
    = kelem9_flat_list (buf6_elems b) ++ kelem9_to_list e.
Proof.
  intros X [xs] e. unfold buf6_inject, buf6_elems, kelem9_flat_list. cbn.
  induction xs as [|y ys IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Theorem kcad9_push_seq :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    kcad9_to_list (kcad9_push x k) = x :: kcad9_to_list k.
Proof.
  intros X x k. destruct k as [|b|h m t]; cbn [kcad9_push].
  - reflexivity.
  - rewrite kcad9_to_list_simple. rewrite kelem9_flat_list_push. reflexivity.
  - rewrite !kcad9_to_list_triple. rewrite kelem9_flat_list_push.
    rewrite <- !app_assoc. reflexivity.
Qed.

Theorem kcad9_inject_seq :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    kcad9_to_list (kcad9_inject k x) = kcad9_to_list k ++ [x].
Proof.
  intros X k x. destruct k as [|b|h m t]; cbn [kcad9_inject].
  - reflexivity.
  - rewrite kcad9_to_list_simple. rewrite kelem9_flat_list_inject. reflexivity.
  - rewrite !kcad9_to_list_triple. rewrite kelem9_flat_list_inject.
    rewrite <- !app_assoc. reflexivity.
Qed.

(* ========================================================================== *)
(* WF preservation.                                                           *)
(* ========================================================================== *)

(** Push preserves [wf_kcad9_strong].  All three branches only grow
    the relevant boundary buffer, so any size lower bound is preserved
    (we strengthen [≥ 5] to [≥ 6], which still satisfies [≥ 5]). *)
Theorem kcad9_push_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque9 X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_push x k).
Proof.
  intros X x k Hwf. destruct k as [|b|h m t]; cbn [kcad9_push].
  - (* K9Empty: result is K9Simple (mkBuf6 [XBase9 x]).  Size = 1 ≥ 1. *)
    cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - (* K9Simple: push grows the buffer.  Result size ≥ size+1 ≥ 1. *)
    cbn in *. apply buf6_size_ge_push_preserve. exact Hwf.
  - (* K9Triple: push grows h.  Need h still ≥ 5. *)
    cbn in *. destruct Hwf as [Hh [Ht Hm]].
    repeat split.
    + apply buf6_size_ge_push_preserve. exact Hh.
    + exact Ht.
    + exact Hm.
Qed.

(** Inject preserves [wf_kcad9_strong] — symmetric. *)
Theorem kcad9_inject_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (x : X),
    wf_kcad9_strong k -> wf_kcad9_strong (kcad9_inject k x).
Proof.
  intros X k x Hwf. destruct k as [|b|h m t]; cbn [kcad9_inject].
  - cbn. unfold buf6_size_ge, buf6_size, buf6_elems. cbn. lia.
  - cbn in *. apply buf6_size_ge_inject_preserve. exact Hwf.
  - cbn in *. destruct Hwf as [Hh [Ht Hm]].
    repeat split; auto.
    apply buf6_size_ge_inject_preserve. exact Ht.
Qed.

(** ** Sanity checks. *)

Example push_singleton9 :
  forall (X : Type) (x : X),
    kcad9_to_list (kcad9_push x (@K9Empty X)) = [x].
Proof. intros; reflexivity. Qed.

Example inject_singleton9 :
  forall (X : Type) (x : X),
    kcad9_to_list (kcad9_inject (@K9Empty X) x) = [x].
Proof. intros; reflexivity. Qed.

(* ========================================================================== *)
(* Pop / Eject.                                                               *)
(* ========================================================================== *)

(** ** Refill helpers.

    When pop drops [h]'s size below the boundary threshold (we trigger
    at original-size = 5, so post-pop [|h'|] = 4), pull the leftmost
    stored cell out of [m] and unfold it into [h']:

      [StoredSmall9 b]      → new_h = h' ++ b, m_rest stays.
      [StoredBig9 pre sm suf] → new_h = h' ++ pre, m_new = sm ++
                                [StoredSmall9 suf] ++ m_rest.
      [m empty]              → collapse to K9Simple (h' ++ t).

    Symmetric for eject + refill of [t]. *)

Definition refill_h_K9Triple {X : Type}
  (h' : Buf6 (KElem9 X))
  (m : Buf6 (Stored9 X))
  (t : Buf6 (KElem9 X))
  : KCadeque9 X :=
  match buf6_pop m with
  | None =>
      K9Simple (buf6_concat h' t)
  | Some (cell, m_rest) =>
      match cell with
      | StoredSmall9 b =>
          K9Triple (buf6_concat h' b) m_rest t
      | StoredBig9 pre sm suf =>
          let new_h := buf6_concat h' pre in
          let m_carrying_suf := buf6_push (StoredSmall9 suf) m_rest in
          let new_m := buf6_concat sm m_carrying_suf in
          K9Triple new_h new_m t
      | StoredMiddle9 sm =>
          K9Triple h' (buf6_concat sm m_rest) t
      end
  end.

Definition refill_t_K9Triple {X : Type}
  (h : Buf6 (KElem9 X))
  (m : Buf6 (Stored9 X))
  (t' : Buf6 (KElem9 X))
  : KCadeque9 X :=
  match buf6_eject m with
  | None =>
      K9Simple (buf6_concat h t')
  | Some (m_rest, cell) =>
      match cell with
      | StoredSmall9 b =>
          K9Triple h m_rest (buf6_concat b t')
      | StoredBig9 pre sm suf =>
          let new_t := buf6_concat suf t' in
          let m_carrying_pre := buf6_inject m_rest (StoredSmall9 pre) in
          let new_m := buf6_concat m_carrying_pre sm in
          K9Triple h new_m new_t
      | StoredMiddle9 sm =>
          K9Triple h (buf6_concat m_rest sm) t'
      end
  end.

(** ** Public pop.  Returns [None] on empty; under wf this is the only
    way to get [None].  The XStored9 patterns are defensive — they
    don't fire under [wf_kcad9_strong] (which we'll extend in a
    follow-up to forbid XStored9 in boundary buffers). *)

Definition kcad9_pop {X : Type} (k : KCadeque9 X)
                     : option (X * KCadeque9 X) :=
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
          (* Under wf, |h| ≥ 5 so |h'| ≥ 4.  We refill when |h'| < 5
             (i.e., |h'| = 4 exactly).  Equivalently: refill when
             |h| was = 5; no refill when |h| ≥ 6. *)
          if Nat.leb 5 (buf6_size h') then
            Some (x, K9Triple h' m t)
          else
            Some (x, refill_h_K9Triple h' m t)
      | _ => None
      end
  end.

Definition kcad9_eject {X : Type} (k : KCadeque9 X)
                       : option (KCadeque9 X * X) :=
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
            Some (refill_t_K9Triple h m t', x)
      | _ => None
      end
  end.

(* ========================================================================== *)
(* Seq laws — helper lemmas.                                                  *)
(* ========================================================================== *)

(** Flat-list distribution over concat / push / inject for both
    [kelem9_flat_list] and [stored9_flat_list]. *)

Lemma kelem9_flat_list_concat :
  forall (X : Type) (a b : Buf6 (KElem9 X)),
    kelem9_flat_list (buf6_elems (buf6_concat a b))
    = kelem9_flat_list (buf6_elems a)
      ++ kelem9_flat_list (buf6_elems b).
Proof.
  intros X [xs] [ys]. unfold buf6_concat, buf6_elems, kelem9_flat_list.
  induction xs as [|e es IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma stored9_flat_list_concat :
  forall (X : Type) (a b : Buf6 (Stored9 X)),
    stored9_flat_list (buf6_elems (buf6_concat a b))
    = stored9_flat_list (buf6_elems a)
      ++ stored9_flat_list (buf6_elems b).
Proof.
  intros X [xs] [ys]. unfold buf6_concat, buf6_elems, stored9_flat_list.
  induction xs as [|s ss IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma stored9_flat_list_push :
  forall (X : Type) (s : Stored9 X) (m : Buf6 (Stored9 X)),
    stored9_flat_list (buf6_elems (buf6_push s m))
    = stored9_to_list s ++ stored9_flat_list (buf6_elems m).
Proof.
  intros X s [xs]. unfold buf6_push, buf6_elems, stored9_flat_list. cbn.
  reflexivity.
Qed.

Lemma stored9_flat_list_inject :
  forall (X : Type) (m : Buf6 (Stored9 X)) (s : Stored9 X),
    stored9_flat_list (buf6_elems (buf6_inject m s))
    = stored9_flat_list (buf6_elems m) ++ stored9_to_list s.
Proof.
  intros X [xs] s. unfold buf6_inject, buf6_elems, stored9_flat_list. cbn.
  induction xs as [|s' ss IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** [stored9_to_list] of a [StoredSmall9] / [StoredBig9]. *)

Lemma stored9_to_list_small :
  forall (X : Type) (b : Buf6 (KElem9 X)),
    stored9_to_list (StoredSmall9 b)
    = kelem9_flat_list (buf6_elems b).
Proof. reflexivity. Qed.

Lemma stored9_to_list_big :
  forall (X : Type) (pre : Buf6 (KElem9 X)) (sm : Buf6 (Stored9 X))
         (suf : Buf6 (KElem9 X)),
    stored9_to_list (StoredBig9 pre sm suf)
    = kelem9_flat_list (buf6_elems pre)
      ++ stored9_flat_list (buf6_elems sm)
      ++ kelem9_flat_list (buf6_elems suf).
Proof. reflexivity. Qed.

Lemma stored9_to_list_middle :
  forall (X : Type) (sm : Buf6 (Stored9 X)),
    stored9_to_list (StoredMiddle9 sm)
    = stored9_flat_list (buf6_elems sm).
Proof. reflexivity. Qed.

Lemma k9_middle_push_seq :
  forall (X : Type) (sm rest : Buf6 (Stored9 X)),
    stored9_flat_list (buf6_elems (k9_middle_push sm rest))
    = stored9_flat_list (buf6_elems sm)
      ++ stored9_flat_list (buf6_elems rest).
Proof.
  intros X [xs] rest.
  destruct xs as [|s ss].
  - reflexivity.
  - unfold k9_middle_push, buf6_is_empty, buf6_push, buf6_elems.
    reflexivity.
Qed.

Lemma k9_middle_inject_seq :
  forall (X : Type) (rest sm : Buf6 (Stored9 X)),
    stored9_flat_list (buf6_elems (k9_middle_inject rest sm))
    = stored9_flat_list (buf6_elems rest)
      ++ stored9_flat_list (buf6_elems sm).
Proof.
  intros X [rs] [xs].
  destruct xs as [|s ss].
  - unfold k9_middle_inject, buf6_is_empty, buf6_elems.
    cbn. rewrite app_nil_r. reflexivity.
  - unfold k9_middle_inject, buf6_is_empty, buf6_inject, buf6_elems.
    induction rs as [|r rs IH]; cbn.
    + rewrite app_nil_r. reflexivity.
    + unfold stored9_flat_list in IH. cbn in IH.
      rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** Conversion: [buf6_pop_seq_some] applied to a Stored9-buffer. *)

Lemma stored9_flat_list_pop_some :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    buf6_pop m = Some (s, m_rest) ->
    stored9_flat_list (buf6_elems m)
    = stored9_to_list s ++ stored9_flat_list (buf6_elems m_rest).
Proof.
  intros X m m_rest s Hp.
  apply buf6_pop_seq_some in Hp.
  unfold buf6_to_list in Hp.
  unfold stored9_flat_list. rewrite Hp. cbn. reflexivity.
Qed.

Lemma stored9_flat_list_app :
  forall (X : Type) (a b : list (Stored9 X)),
    stored9_flat_list (a ++ b)
    = stored9_flat_list a ++ stored9_flat_list b.
Proof.
  intros X a b. unfold stored9_flat_list.
  induction a as [|s ss IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma stored9_flat_list_eject_some :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    buf6_eject m = Some (m_rest, s) ->
    stored9_flat_list (buf6_elems m)
    = stored9_flat_list (buf6_elems m_rest) ++ stored9_to_list s.
Proof.
  intros X m m_rest s He.
  apply buf6_eject_seq_some in He.
  unfold buf6_to_list in He.
  rewrite He.
  rewrite stored9_flat_list_app.
  unfold stored9_flat_list at 2. cbn.
  rewrite app_nil_r. reflexivity.
Qed.

(** kelem9 buffer pop: extract the flattening structure. *)

Lemma kelem9_flat_list_pop_some :
  forall (X : Type) (b b' : Buf6 (KElem9 X)) (e : KElem9 X),
    buf6_pop b = Some (e, b') ->
    kelem9_flat_list (buf6_elems b)
    = kelem9_to_list e ++ kelem9_flat_list (buf6_elems b').
Proof.
  intros X b b' e Hp.
  apply buf6_pop_seq_some in Hp.
  unfold buf6_to_list in Hp.
  unfold kelem9_flat_list. rewrite Hp. cbn. reflexivity.
Qed.

Lemma kelem9_flat_list_app :
  forall (X : Type) (a b : list (KElem9 X)),
    kelem9_flat_list (a ++ b)
    = kelem9_flat_list a ++ kelem9_flat_list b.
Proof.
  intros X a b. unfold kelem9_flat_list.
  induction a as [|e es IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma kelem9_flat_list_eject_some :
  forall (X : Type) (b b' : Buf6 (KElem9 X)) (e : KElem9 X),
    buf6_eject b = Some (b', e) ->
    kelem9_flat_list (buf6_elems b)
    = kelem9_flat_list (buf6_elems b') ++ kelem9_to_list e.
Proof.
  intros X b b' e He.
  apply buf6_eject_seq_some in He.
  unfold buf6_to_list in He.
  rewrite He.
  rewrite kelem9_flat_list_app.
  unfold kelem9_flat_list at 2. cbn.
  rewrite app_nil_r. reflexivity.
Qed.

(* ========================================================================== *)
(* Refill helper seq laws.                                                    *)
(* ========================================================================== *)

(** [refill_h_K9Triple h' m t] flattens to [h' ++ flatten(m) ++ t]. *)
Lemma refill_h_K9Triple_seq :
  forall (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    kcad9_to_list (refill_h_K9Triple h' m t)
    = kelem9_flat_list (buf6_elems h')
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t).
Proof.
  intros X h' m t. unfold refill_h_K9Triple.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - assert (Hm := Hpop).
    apply stored9_flat_list_pop_some in Hm.
    destruct cell as [b|pre sm suf|sm].
    + (* StoredSmall9 b *)
      rewrite kcad9_to_list_triple.
      rewrite kelem9_flat_list_concat.
      rewrite Hm. rewrite stored9_to_list_small.
      rewrite <- !app_assoc. reflexivity.
    + (* StoredBig9 pre sm suf *)
      rewrite kcad9_to_list_triple.
      rewrite kelem9_flat_list_concat.
      rewrite stored9_flat_list_concat.
      rewrite stored9_flat_list_push.
      rewrite stored9_to_list_small.
      rewrite Hm. rewrite stored9_to_list_big.
      rewrite <- !app_assoc. reflexivity.
    + (* StoredMiddle9 sm *)
      rewrite kcad9_to_list_triple.
      rewrite stored9_flat_list_concat.
      rewrite Hm. rewrite stored9_to_list_middle.
      rewrite <- !app_assoc. reflexivity.
  - apply buf6_pop_seq_none in Hpop.
    unfold buf6_to_list in Hpop.
    rewrite kcad9_to_list_simple.
    rewrite kelem9_flat_list_concat.
    assert (Hm : stored9_flat_list (buf6_elems m) = []).
    { unfold stored9_flat_list. rewrite Hpop. reflexivity. }
    rewrite Hm. cbn [app]. reflexivity.
Qed.

(** [refill_t_K9Triple h m t'] flattens to [h ++ flatten(m) ++ t']. *)
Lemma refill_t_K9Triple_seq :
  forall (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    kcad9_to_list (refill_t_K9Triple h m t')
    = kelem9_flat_list (buf6_elems h)
      ++ stored9_flat_list (buf6_elems m)
      ++ kelem9_flat_list (buf6_elems t').
Proof.
  intros X h m t'. unfold refill_t_K9Triple.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heje.
  - assert (Hm := Heje).
    apply stored9_flat_list_eject_some in Hm.
    destruct cell as [b|pre sm suf|sm].
    + (* StoredSmall9 b *)
      rewrite kcad9_to_list_triple.
      rewrite kelem9_flat_list_concat.
      rewrite Hm. rewrite stored9_to_list_small.
      rewrite <- !app_assoc. reflexivity.
    + (* StoredBig9 pre sm suf *)
      rewrite kcad9_to_list_triple.
      rewrite kelem9_flat_list_concat.
      rewrite stored9_flat_list_concat.
      rewrite stored9_flat_list_inject.
      rewrite stored9_to_list_small.
      rewrite Hm. rewrite stored9_to_list_big.
      rewrite <- !app_assoc. reflexivity.
    + (* StoredMiddle9 sm *)
      rewrite kcad9_to_list_triple.
      rewrite stored9_flat_list_concat.
      rewrite Hm. rewrite stored9_to_list_middle.
      rewrite <- !app_assoc. reflexivity.
  - apply buf6_eject_seq_none in Heje.
    unfold buf6_to_list in Heje.
    rewrite kcad9_to_list_simple.
    rewrite kelem9_flat_list_concat.
    assert (Hm : stored9_flat_list (buf6_elems m) = []).
    { unfold stored9_flat_list. rewrite Heje. reflexivity. }
    rewrite Hm. cbn [app]. reflexivity.
Qed.

(* ========================================================================== *)
(* Pop / Eject seq preservation.                                              *)
(* ========================================================================== *)

Theorem kcad9_pop_seq :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    kcad9_pop k = Some (x, k') ->
    kcad9_to_list k = x :: kcad9_to_list k'.
Proof.
  intros X k x k' Hpop.
  destruct k as [|b|h m t]; cbn [kcad9_pop] in Hpop.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    rewrite kcad9_to_list_simple.
    assert (Hflat := Hpb).
    apply kelem9_flat_list_pop_some in Hflat.
    rewrite Hflat. cbn [kelem9_to_list].
    destruct (buf6_is_empty b') eqn:Hbe; injection Hpop as Hx Hk'; subst x k'.
    + (* b' empty: result K9Empty *)
      cbn.
      assert (Hb' : kelem9_flat_list (buf6_elems b') = []).
      { apply buf6_is_empty_size in Hbe.
        unfold kelem9_flat_list.
        destruct b' as [xs]. unfold buf6_size, buf6_elems in *. cbn in *.
        destruct xs; [reflexivity | cbn in Hbe; lia]. }
      rewrite Hb'. cbn [app]. reflexivity.
    + (* b' non-empty: result K9Simple b' *)
      rewrite kcad9_to_list_simple. reflexivity.
  - destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    apply kelem9_flat_list_pop_some in Hph.
    rewrite kcad9_to_list_triple. rewrite Hph. cbn [kelem9_to_list].
    rewrite <- !app_assoc. cbn [app].
    destruct (Nat.leb 5 (buf6_size h')); injection Hpop as Hx Hk'; subst x k'.
    + (* No refill *)
      rewrite kcad9_to_list_triple. reflexivity.
    + (* Refill *)
      rewrite refill_h_K9Triple_seq. reflexivity.
Qed.

Theorem kcad9_eject_seq :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    kcad9_eject k = Some (k', x) ->
    kcad9_to_list k = kcad9_to_list k' ++ [x].
Proof.
  intros X k k' x Heje.
  destruct k as [|b|h m t]; cbn [kcad9_eject] in Heje.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    rewrite kcad9_to_list_simple.
    apply kelem9_flat_list_eject_some in Heb.
    rewrite Heb.
    destruct (buf6_is_empty b') eqn:Hbe; injection Heje as Hk' Hx; subst x k'.
    + assert (Hb' : kelem9_flat_list (buf6_elems b') = []).
      { apply buf6_is_empty_size in Hbe.
        unfold kelem9_flat_list.
        destruct b' as [xs]. unfold buf6_size, buf6_elems in *. cbn in *.
        destruct xs; [reflexivity | cbn in Hbe; lia]. }
      rewrite Hb'. cbn [app kelem9_to_list]. reflexivity.
    + rewrite kcad9_to_list_simple.
      cbn [kelem9_to_list]. reflexivity.
  - destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    apply kelem9_flat_list_eject_some in Het.
    rewrite kcad9_to_list_triple. rewrite Het. cbn [kelem9_to_list].
    destruct (Nat.leb 5 (buf6_size t')); injection Heje as Hk' Hx; subst x k'.
    + rewrite kcad9_to_list_triple.
      rewrite <- !app_assoc. cbn [app]. reflexivity.
    + rewrite refill_t_K9Triple_seq.
      rewrite <- !app_assoc. cbn [app]. reflexivity.
Qed.

(* ========================================================================== *)
(* WF preservation for pop / eject.                                           *)
(* ========================================================================== *)

(** [wf_middle9] preserved by buf6_pop (the head cell is wf if m was). *)
Lemma wf_middle9_pop :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    wf_middle9 m ->
    buf6_pop m = Some (s, m_rest) ->
    wf_stored9 s /\ wf_middle9 m_rest.
Proof.
  intros X m m_rest s Hm Hpop.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  unfold wf_middle9 in *. rewrite Hpop in Hm. inversion Hm; subst.
  split; assumption.
Qed.

Lemma wf_middle9_eject :
  forall (X : Type) (m m_rest : Buf6 (Stored9 X)) (s : Stored9 X),
    wf_middle9 m ->
    buf6_eject m = Some (m_rest, s) ->
    wf_middle9 m_rest /\ wf_stored9 s.
Proof.
  intros X m m_rest s Hm Hej.
  apply buf6_eject_seq_some in Hej. unfold buf6_to_list in Hej.
  unfold wf_middle9 in *. rewrite Hej in Hm.
  apply Forall_app in Hm. destruct Hm as [Hm_rest Hs].
  inversion Hs; subst.
  split; assumption.
Qed.

(** [wf_middle9] preserved by buf6_concat. *)
Lemma wf_middle9_concat :
  forall (X : Type) (a b : Buf6 (Stored9 X)),
    wf_middle9 a -> wf_middle9 b -> wf_middle9 (buf6_concat a b).
Proof.
  intros X [xs] [ys] Ha Hb.
  unfold wf_middle9, buf6_concat, buf6_elems in *.
  apply Forall_app. split; assumption.
Qed.

(** [refill_h_K9Triple] preserves [wf_kcad9_strong] under the right
    preconditions:
      - [|h'| = 4] (it dropped one below the boundary)
      - [|t| ≥ 5] (unchanged)
      - [m] is [wf_middle9]
*)
Lemma refill_h_K9Triple_wf :
  forall (X : Type) (h' : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t : Buf6 (KElem9 X)),
    buf6_size_ge 4 h' ->
    buf6_size_ge 5 t ->
    wf_middle9 m ->
    wf_kcad9_strong (refill_h_K9Triple h' m t).
Proof.
  intros X h' m t Hh' Ht Hm.
  unfold refill_h_K9Triple.
  destruct (buf6_pop m) as [[cell m_rest]|] eqn:Hpop.
  - destruct (wf_middle9_pop _ _ _ _ Hm Hpop) as [Hcell Hm_rest].
    destruct cell as [b|pre sm suf|sm].
    + (* StoredSmall9 b: |b| ≥ 3 *)
      cbn in Hcell. cbn [wf_kcad9_strong].
      repeat split.
      * eapply buf6_size_ge_weaken; [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Ht.
      * exact Hm_rest.
    + (* StoredBig9 pre sm suf: |pre|, |suf| ≥ 3 *)
      apply wf_stored9_big_iff in Hcell. destruct Hcell as [Hpre [Hsuf Hsm]].
      cbn [wf_kcad9_strong].
      repeat split.
      * eapply buf6_size_ge_weaken; [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Ht.
      * apply wf_middle9_concat; [exact Hsm |].
        apply wf_middle9_push.
        -- cbn. exact Hsuf.
        -- exact Hm_rest.
    + contradiction.
  - (* m empty: collapse to K9Simple (h' ++ t).  Need |h' ++ t| ≥ 1. *)
    cbn [wf_kcad9_strong].
    eapply buf6_size_ge_weaken with (n := 4).
    + lia.
    + apply buf6_size_ge_concat_l. exact Hh'.
Qed.

Lemma refill_t_K9Triple_wf :
  forall (X : Type) (h : Buf6 (KElem9 X))
         (m : Buf6 (Stored9 X)) (t' : Buf6 (KElem9 X)),
    buf6_size_ge 5 h ->
    buf6_size_ge 4 t' ->
    wf_middle9 m ->
    wf_kcad9_strong (refill_t_K9Triple h m t').
Proof.
  intros X h m t' Hh Ht' Hm.
  unfold refill_t_K9Triple.
  destruct (buf6_eject m) as [[m_rest cell]|] eqn:Heje.
  - destruct (wf_middle9_eject _ _ _ _ Hm Heje) as [Hm_rest Hcell].
    destruct cell as [b|pre sm suf|sm].
    + cbn in Hcell. cbn [wf_kcad9_strong].
      repeat split.
      * exact Hh.
      * eapply buf6_size_ge_weaken; [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Hm_rest.
    + apply wf_stored9_big_iff in Hcell. destruct Hcell as [Hpre [Hsuf Hsm]].
      cbn [wf_kcad9_strong].
      repeat split.
      * exact Hh.
      * eapply buf6_size_ge_weaken; [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * apply wf_middle9_concat.
        -- apply wf_middle9_inject; [exact Hm_rest | cbn; exact Hpre].
        -- exact Hsm.
    + contradiction.
  - cbn [wf_kcad9_strong].
    apply buf6_size_ge_concat_l. unfold buf6_size_ge in Hh |- *. lia.
Qed.

Theorem kcad9_pop_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (x : X) (k' : KCadeque9 X),
    wf_kcad9_strong k ->
    kcad9_pop k = Some (x, k') -> wf_kcad9_strong k'.
Proof.
  intros X k x k' Hwf Hpop.
  destruct k as [|b|h m t]; cbn [kcad9_pop] in Hpop.
  - discriminate.
  - destruct (buf6_pop b) as [[e b']|] eqn:Hpb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hbe; injection Hpop as Hx Hk'; subst x k';
      cbn [wf_kcad9_strong]; auto.
    (* b' non-empty: need |b'| ≥ 1 *)
    unfold buf6_is_empty, buf6_size_ge, buf6_size, buf6_elems in *.
    destruct b' as [xs]. cbn in *.
    destruct xs as [|y ys]; [discriminate Hbe | cbn; lia].
  - destruct (buf6_pop h) as [[e h']|] eqn:Hph; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    cbn [wf_kcad9_strong] in Hwf.
    destruct Hwf as [Hh [Ht Hm]].
    assert (Hh' : buf6_size_ge 4 h').
    { unfold buf6_size_ge in Hh |- *.
      apply buf6_pop_size_some in Hph. lia. }
    destruct (Nat.leb 5 (buf6_size h')) eqn:Hcmp;
      injection Hpop as Hx Hk'; subst x k';
      cbn [wf_kcad9_strong].
    + (* No refill: |h'| ≥ 5 *)
      apply PeanoNat.Nat.leb_le in Hcmp.
      repeat split; [unfold buf6_size_ge; exact Hcmp | exact Ht | exact Hm].
    + (* Refill: |h'| = 4 *)
      apply refill_h_K9Triple_wf; assumption.
Qed.

(* ========================================================================== *)
(* Concat — trivially O(1) under the strong invariant.                        *)
(* ========================================================================== *)

(** This abstract operation keeps the old proof-friendly [buf6_concat]
    cases.  The hand-edited OCaml constant-work shape, including the
    scheduled T+T bridge, is modeled in [Normalize.v]. *)

Definition kcad9_concat {X : Type} (a b : KCadeque9 X) : KCadeque9 X :=
  match a, b with
  | K9Empty, _ => b
  | _, K9Empty => a

  | K9Simple ba, K9Simple bb =>
      (* Both are size ≥ 1.  Combined size ≥ 2.  Result: K9Simple of
         concatenated buffer.  (Under the wf, we can't promote to a
         K9Triple here without size ≥ 5 boundaries.) *)
      K9Simple (buf6_concat ba bb)

  | K9Simple ba, K9Triple h2 m2 t2 =>
      (* Push (StoredSmall9 h2) to the front of m2 if |h2| ≥ 3
         (which is weaker than the K9Triple's |h2| ≥ 5 — always holds).
         The combined ba ++ h2 will be the new head buffer.
         BUT this loses the ≥5 head invariant if |ba| < 5.

         Cleanest recipe: concat ba into h2's front, giving the new
         result's head.  No boundary cell adjustment needed since
         t2 remains as the tail.

         |new_h| = |ba| + |h2| ≥ 1 + 5 = 6 ≥ 5 ✓ *)
      K9Triple (buf6_concat ba h2) m2 t2

  | K9Triple h1 m1 t1, K9Simple bb =>
      (* Concat bb into t1's back.  |new_t| = |t1| + |bb| ≥ 5 + 1 = 6 ✓. *)
      K9Triple h1 m1 (buf6_concat t1 bb)

  | K9Triple h1 m1 t1, K9Triple h2 m2 t2 =>
      (* THE HEADLINE CASE.  Result middle contains:
           m1's cells, then [StoredSmall9 (t1 ++ h2)], then m2's cells.
         This flattens to:
           flatten(m1) ++ (t1 ++ h2) ++ flatten(m2)
         giving the total: h1 ++ flatten(m1) ++ t1 ++ h2 ++ flatten(m2) ++ t2.
         Match! ✓
         The merged cell has size |t1|+|h2| ≥ 5+5 = 10 ≥ 3 ✓ for wf. *)
      let cell := StoredSmall9 (buf6_concat t1 h2) in
      let m_new := buf6_concat (buf6_inject m1 cell) m2 in
      K9Triple h1 m_new t2
  end.

(** ** Concat sequence preservation. *)

Theorem kcad9_concat_seq :
  forall (X : Type) (a b : KCadeque9 X),
    kcad9_to_list (kcad9_concat a b) = kcad9_to_list a ++ kcad9_to_list b.
Proof.
  intros X a b.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad9_concat].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - (* Simple, Simple *)
    rewrite !kcad9_to_list_simple. apply kelem9_flat_list_concat.
  - (* Simple, Triple *)
    rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite kelem9_flat_list_concat.
    rewrite <- !app_assoc. reflexivity.
  - cbn [kcad9_to_list]. rewrite app_nil_r. reflexivity.
  - (* Triple, Simple *)
    rewrite kcad9_to_list_simple, !kcad9_to_list_triple.
    rewrite kelem9_flat_list_concat.
    rewrite <- !app_assoc. reflexivity.
  - (* Triple, Triple — the headline case *)
    rewrite !kcad9_to_list_triple.
    rewrite stored9_flat_list_concat.
    rewrite stored9_flat_list_inject.
    rewrite stored9_to_list_small.
    rewrite kelem9_flat_list_concat.
    rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Concat WF preservation. *)

Theorem kcad9_concat_wf_strong :
  forall (X : Type) (a b : KCadeque9 X),
    wf_kcad9_strong a -> wf_kcad9_strong b ->
    wf_kcad9_strong (kcad9_concat a b).
Proof.
  intros X a b Ha Hb.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad9_concat]; auto.
  - (* Simple, Simple *)
    cbn in Ha, Hb |- *.
    apply buf6_size_ge_concat_l. exact Ha.
  - (* Simple, Triple *)
    cbn in Ha, Hb |- *. destruct Hb as [Hh2 [Ht2 Hm2]].
    repeat split.
    + apply buf6_size_ge_concat_r. exact Hh2.
    + exact Ht2.
    + exact Hm2.
  - (* Triple, Simple *)
    cbn in Ha, Hb |- *. destruct Ha as [Hh1 [Ht1 Hm1]].
    repeat split.
    + exact Hh1.
    + apply buf6_size_ge_concat_l. exact Ht1.
    + exact Hm1.
  - (* Triple, Triple — THE HEADLINE CASE *)
    cbn in Ha, Hb |- *.
    destruct Ha as [Hh1 [Ht1 Hm1]]. destruct Hb as [Hh2 [Ht2 Hm2]].
    repeat split.
    + exact Hh1.
    + exact Ht2.
    + apply wf_middle9_concat.
      * apply wf_middle9_inject; [exact Hm1 |].
        (* StoredSmall9 (t1 ++ h2) wf: size ≥ |t1| + |h2| ≥ 5 + 5 = 10 ≥ 3 *)
        cbn. eapply buf6_size_ge_weaken;
          [|eapply buf6_size_ge_concat_sum; eassumption]. lia.
      * exact Hm2.
Qed.

Theorem kcad9_eject_wf_strong :
  forall (X : Type) (k : KCadeque9 X) (k' : KCadeque9 X) (x : X),
    wf_kcad9_strong k ->
    kcad9_eject k = Some (k', x) -> wf_kcad9_strong k'.
Proof.
  intros X k k' x Hwf Heje.
  destruct k as [|b|h m t]; cbn [kcad9_eject] in Heje.
  - discriminate.
  - destruct (buf6_eject b) as [[b' e]|] eqn:Heb; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    destruct (buf6_is_empty b') eqn:Hbe; injection Heje as Hk' Hx; subst x k';
      cbn [wf_kcad9_strong]; auto.
    unfold buf6_is_empty, buf6_size_ge, buf6_size, buf6_elems in *.
    destruct b' as [xs]. cbn in *.
    destruct xs as [|y ys]; [discriminate Hbe | cbn; lia].
  - destruct (buf6_eject t) as [[t' e]|] eqn:Het; [|discriminate].
    destruct e as [xv|sv]; [|discriminate].
    cbn [wf_kcad9_strong] in Hwf.
    destruct Hwf as [Hh [Ht Hm]].
    assert (Ht' : buf6_size_ge 4 t').
    { unfold buf6_size_ge in Ht |- *.
      apply buf6_eject_size_some in Het. lia. }
    destruct (Nat.leb 5 (buf6_size t')) eqn:Hcmp;
      injection Heje as Hk' Hx; subst x k';
      cbn [wf_kcad9_strong].
    + apply PeanoNat.Nat.leb_le in Hcmp.
      repeat split; [exact Hh | unfold buf6_size_ge; exact Hcmp | exact Hm].
    + apply refill_t_K9Triple_wf; assumption.
Qed.
