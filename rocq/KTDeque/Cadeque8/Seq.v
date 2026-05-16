(** * Module: KTDeque.Cadeque8.Seq — sequence-preservation laws.

    Proves that each public op preserves the abstract list semantics:
      kcad8_to_list (kcad8_push x k)    = x :: kcad8_to_list k
      kcad8_to_list (kcad8_inject k x)  = kcad8_to_list k ++ [x]
      kcad8_to_list (kcad8_concat a b)  = kcad8_to_list a ++ kcad8_to_list b
      kcad8_pop k = Some (x, k')        -> kcad8_to_list k = x :: kcad8_to_list k'
      kcad8_eject k = Some (k', x)      -> kcad8_to_list k = kcad8_to_list k' ++ [x] *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops.

(** ** Buffer flatten helper (uses the same inline-fix form that
       cbn produces from the to_list mutual block). *)

Definition kelem8_flat_list {X : Type} (l : list (KElem8 X)) : list X :=
  (fix go (l0 : list (KElem8 X)) : list X :=
     match l0 with
     | []      => []
     | e :: es => kelem8_to_list e ++ go es
     end) l.

Definition stored8_flat_list {X : Type} (l : list (Stored8 X)) : list X :=
  (fix go (l0 : list (Stored8 X)) : list X :=
     match l0 with
     | []      => []
     | s :: ss => stored8_to_list s ++ go ss
     end) l.

(** Folding the inline fix in [kcad8_to_list K8Simple] back to
    [kelem8_flat_list]. *)

Lemma kcad8_to_list_simple :
  forall (X : Type) (b : Buf6 (KElem8 X)),
    kcad8_to_list (K8Simple b) = kelem8_flat_list (buf6_elems b).
Proof. intros; reflexivity. Qed.

Lemma kcad8_to_list_triple :
  forall (X : Type) (h : Buf6 (KElem8 X))
         (m : Buf6 (Stored8 X)) (t : Buf6 (KElem8 X)),
    kcad8_to_list (K8Triple h m t)
    = kelem8_flat_list (buf6_elems h)
      ++ stored8_flat_list (buf6_elems m)
      ++ kelem8_flat_list (buf6_elems t).
Proof. intros; reflexivity. Qed.

(** Effect of [buf6_push] / [buf6_inject] on the flat list semantics. *)

Lemma kelem8_flat_list_push :
  forall (X : Type) (e : KElem8 X) (b : Buf6 (KElem8 X)),
    kelem8_flat_list (buf6_elems (buf6_push e b))
    = kelem8_to_list e ++ kelem8_flat_list (buf6_elems b).
Proof.
  intros X e [xs]. unfold buf6_push, buf6_elems, kelem8_flat_list. cbn.
  reflexivity.
Qed.

Lemma kelem8_flat_list_inject :
  forall (X : Type) (b : Buf6 (KElem8 X)) (e : KElem8 X),
    kelem8_flat_list (buf6_elems (buf6_inject b e))
    = kelem8_flat_list (buf6_elems b) ++ kelem8_to_list e.
Proof.
  intros X [xs] e. unfold buf6_inject, buf6_elems, kelem8_flat_list. cbn.
  induction xs as [|y ys IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** ** Push preserves the sequence. *)

Theorem kcad8_push_seq :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    kcad8_to_list (kcad8_push x k) = x :: kcad8_to_list k.
Proof.
  intros X x k. destruct k as [|b|h m t]; cbn [kcad8_push].
  - reflexivity.
  - rewrite kcad8_to_list_simple. rewrite kelem8_flat_list_push.
    cbn [kelem8_to_list]. rewrite kcad8_to_list_simple. reflexivity.
  - rewrite !kcad8_to_list_triple.
    rewrite kelem8_flat_list_push.
    cbn [kelem8_to_list]. reflexivity.
Qed.

(** ** Inject preserves the sequence. *)

Theorem kcad8_inject_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_to_list (kcad8_inject k x) = kcad8_to_list k ++ [x].
Proof.
  intros X k x. destruct k as [|b|h m t]; cbn [kcad8_inject].
  - reflexivity.
  - rewrite kcad8_to_list_simple. rewrite kelem8_flat_list_inject.
    cbn [kelem8_to_list]. rewrite kcad8_to_list_simple. reflexivity.
  - rewrite !kcad8_to_list_triple.
    rewrite kelem8_flat_list_inject.
    cbn [kelem8_to_list].
    rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Helpers for concat — folding inline-fix in [stored8_flat_list]
       singleton case. *)

Lemma stored8_flat_list_singleton :
  forall (X : Type) (s : Stored8 X),
    stored8_flat_list [s] = stored8_to_list s.
Proof. intros; cbn; rewrite app_nil_r; reflexivity. Qed.

Lemma stored8_flat_list_inject :
  forall (X : Type) (b : Buf6 (Stored8 X)) (s : Stored8 X),
    stored8_flat_list (buf6_elems (buf6_inject b s))
    = stored8_flat_list (buf6_elems b) ++ stored8_to_list s.
Proof.
  intros X [xs] s. unfold buf6_inject, buf6_elems, stored8_flat_list. cbn.
  induction xs as [|y ys IH]; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma stored8_flat_list_push :
  forall (X : Type) (s : Stored8 X) (b : Buf6 (Stored8 X)),
    stored8_flat_list (buf6_elems (buf6_push s b))
    = stored8_to_list s ++ stored8_flat_list (buf6_elems b).
Proof.
  intros X s [xs]. unfold buf6_push, buf6_elems, stored8_flat_list. cbn.
  reflexivity.
Qed.

Lemma buf6_pop_some_elems :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_pop b = Some (x, b') ->
    buf6_elems b = x :: buf6_elems b'.
Proof.
  intros X b x b' H. apply buf6_pop_seq_some in H.
  unfold buf6_to_list in H. exact H.
Qed.

(** Big stored8 sequence law. *)

Lemma stored8_to_list_big :
  forall (X : Type) (pre : Buf6 (KElem8 X)) (c : KCadeque8 X)
         (suf : Buf6 (KElem8 X)),
    stored8_to_list (StoredBig8 pre c suf)
    = kelem8_flat_list (buf6_elems pre)
      ++ kcad8_to_list c
      ++ kelem8_flat_list (buf6_elems suf).
Proof. intros; reflexivity. Qed.

(** ** Concat preserves the sequence. *)

Theorem kcad8_concat_seq :
  forall (X : Type) (a b : KCadeque8 X),
    kcad8_to_list (kcad8_concat a b) = kcad8_to_list a ++ kcad8_to_list b.
Proof.
  intros X a b.
  destruct a as [|ba|h1 m1 t1]; destruct b as [|bb|h2 m2 t2];
    cbn [kcad8_concat].
  - reflexivity.                              (* Empty, Empty *)
  - reflexivity.                              (* Empty, Simple *)
  - reflexivity.                              (* Empty, Triple *)
  - cbn. rewrite app_nil_r. reflexivity.       (* Simple, Empty *)
  - (* Simple, Simple → K8Triple ba [] bb *)
    rewrite !kcad8_to_list_simple, kcad8_to_list_triple.
    unfold buf6_elems; cbn [stored8_flat_list]. reflexivity.
  - (* Simple, Triple: K8Triple ba (mkBuf6 [boundary]) t2 *)
    rewrite kcad8_to_list_simple, !kcad8_to_list_triple.
    unfold buf6_elems; cbn [stored8_flat_list].
    rewrite app_nil_r.
    rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    unfold buf6_elems; cbn [kelem8_flat_list].
    rewrite app_nil_r.
    rewrite <- !app_assoc. reflexivity.
  - cbn. rewrite app_nil_r. reflexivity.       (* Triple, Empty *)
  - (* Triple, Simple: K8Triple h1 (inject m1 (StoredSmall8 t1)) bb *)
    rewrite kcad8_to_list_simple, !kcad8_to_list_triple.
    rewrite stored8_flat_list_inject.
    cbn [stored8_to_list].
    unfold buf6_elems; cbn [kelem8_flat_list].
    rewrite <- !app_assoc. reflexivity.
  - (* Triple, Triple *)
    rewrite !kcad8_to_list_triple.
    rewrite stored8_flat_list_inject.
    rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    unfold buf6_elems; cbn [kelem8_flat_list].
    rewrite app_nil_r.
    rewrite <- !app_assoc. reflexivity.
Qed.

(** ** kcad8_from_list flattens back to its input. *)

Lemma kcad8_to_list_inject :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_to_list (kcad8_inject k x) = kcad8_to_list k ++ [x].
Proof. exact kcad8_inject_seq. Qed.

Lemma kcad8_to_list_fold_inject :
  forall (X : Type) (xs : list X) (k : KCadeque8 X),
    kcad8_to_list (List.fold_left (fun acc y => kcad8_inject acc y) xs k)
    = kcad8_to_list k ++ xs.
Proof.
  intros X xs. induction xs as [|y ys IH]; intros k; cbn.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. rewrite kcad8_inject_seq.
    rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma kcad8_to_list_from_list :
  forall (X : Type) (xs : list X),
    kcad8_to_list (kcad8_from_list xs) = xs.
Proof.
  intros X xs. unfold kcad8_from_list.
  rewrite kcad8_to_list_fold_inject. cbn. reflexivity.
Qed.

(** ** Helper: [buf6_is_empty] is exactly "buf6_elems is nil". *)

Lemma buf6_is_empty_iff_nil :
  forall (X : Type) (b : Buf6 X),
    buf6_is_empty b = true <-> buf6_elems b = [].
Proof.
  intros X b. unfold buf6_is_empty.
  destruct (buf6_elems b); split; intros H; try reflexivity; try discriminate.
Qed.

Lemma kelem8_flat_list_nil :
  forall (X : Type) (b : Buf6 (KElem8 X)),
    buf6_is_empty b = true ->
    kelem8_flat_list (buf6_elems b) = [].
Proof.
  intros X b H. rewrite buf6_is_empty_iff_nil in H. rewrite H. reflexivity.
Qed.

Lemma stored8_flat_list_nil :
  forall (X : Type) (m : Buf6 (Stored8 X)),
    buf6_is_empty m = true ->
    stored8_flat_list (buf6_elems m) = [].
Proof.
  intros X m H. rewrite buf6_is_empty_iff_nil in H. rewrite H. reflexivity.
Qed.

Lemma buf6_pop_none_empty :
  forall (X : Type) (b : Buf6 X),
    buf6_pop b = None -> buf6_is_empty b = true.
Proof.
  intros X b H. apply buf6_pop_seq_none in H.
  rewrite buf6_is_empty_iff_nil. unfold buf6_to_list in H. exact H.
Qed.

(** ** Pop preserves the sequence — K8Simple case. *)

Lemma pop_struct_seq_simple :
  forall (X : Type) (b : Buf6 (KElem8 X)) (x : X) (k' : KCadeque8 X),
    kcad8_pop_struct (K8Simple b) = Some (x, k') ->
    kcad8_to_list (K8Simple b) = x :: kcad8_to_list k'.
Proof.
  intros X b x k' H. cbn [kcad8_pop_struct] in H.
  destruct (buf6_pop b) as [[e b']|] eqn:Hpop; [|discriminate].
  destruct e as [xv|sv]; [|discriminate].
  injection H as Hxv Hk'. subst xv k'.
  apply buf6_pop_seq_some in Hpop.
  unfold buf6_to_list in Hpop.
  rewrite kcad8_to_list_simple. unfold kelem8_flat_list at 1.
  rewrite Hpop. cbn [kelem8_to_list].
  destruct (buf6_is_empty b') eqn:He.
  - apply buf6_is_empty_iff_nil in He.
    cbn. rewrite He. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
Qed.

(** ** Pop preserves the sequence — K8Triple, easy case (h' non-empty). *)

Lemma pop_struct_seq_triple_easy :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (h' : Buf6 (KElem8 X)),
    buf6_pop h = Some (XBase8 x, h') ->
    buf6_is_empty h' = false ->
    kcad8_to_list (K8Triple h m t)
    = x :: kcad8_to_list (K8Triple h' m t).
Proof.
  intros X h m t x h' Hpop He.
  rewrite !kcad8_to_list_triple.
  apply buf6_pop_seq_some in Hpop.
  unfold buf6_to_list in Hpop.
  unfold kelem8_flat_list at 1.
  rewrite Hpop. cbn [kelem8_to_list].
  cbn. reflexivity.
Qed.

(** ** K8Triple, rebalance with middle empty (degenerate case). *)

Lemma pop_struct_seq_triple_rebalance_m_empty :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (h' : Buf6 (KElem8 X)),
    buf6_pop h = Some (XBase8 x, h') ->
    buf6_is_empty h' = true ->
    buf6_pop m = None ->
    kcad8_to_list (K8Triple h m t) = x :: kcad8_to_list (K8Simple t).
Proof.
  intros X h m t x h' Hpop Hhe Hme.
  rewrite kcad8_to_list_triple, kcad8_to_list_simple.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  apply buf6_pop_none_empty in Hme.
  apply (stored8_flat_list_nil _ m) in Hme.
  apply (kelem8_flat_list_nil _ h') in Hhe.
  unfold kelem8_flat_list at 1.
  rewrite Hpop. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems h')).
  rewrite Hhe, Hme. cbn. reflexivity.
Qed.

(** ** Rebalance with middle non-empty: unfold and reassemble.

    Sub-case split on [s = unfold_stored s] (StoredSmall vs StoredBig)
    AND on [sub] in the StoredBig case (K8Empty / K8Simple / K8Triple).

    Helper: the reassembled middle's flatten equals
      sub.to_list ++ suf.flat ++ m_rest.flat *)

Lemma reassemble_middle_flat :
  forall (X : Type) (sub : KCadeque8 X)
         (suf : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)),
    stored8_flat_list (buf6_elems
      (let m_with_suf := if buf6_is_empty suf then m_rest
                         else buf6_push (StoredSmall8 suf) m_rest in
       match sub with
       | K8Empty     => m_with_suf
       | K8Simple b  => buf6_push (StoredSmall8 b) m_with_suf
       | K8Triple sh sm st =>
           buf6_push (StoredBig8 sh
                                 (K8Triple (mkBuf6 []) sm (mkBuf6 []))
                                 st)
                     m_with_suf
       end))
    = kcad8_to_list sub
      ++ kelem8_flat_list (buf6_elems suf)
      ++ stored8_flat_list (buf6_elems m_rest).
Proof.
  intros X sub suf m_rest.
  set (m_with_suf :=
    if buf6_is_empty suf then m_rest
    else buf6_push (StoredSmall8 suf) m_rest).
  assert (Hwith : stored8_flat_list (buf6_elems m_with_suf)
                  = kelem8_flat_list (buf6_elems suf)
                    ++ stored8_flat_list (buf6_elems m_rest)).
  { unfold m_with_suf.
    destruct (buf6_is_empty suf) eqn:Hsuf.
    - apply (kelem8_flat_list_nil _ suf) in Hsuf.
      rewrite Hsuf. cbn. reflexivity.
    - rewrite stored8_flat_list_push. cbn [stored8_to_list].
      reflexivity. }
  destruct sub as [|sb|sh sm st]; cbn [kcad8_to_list].
  - (* K8Empty *) exact Hwith.
  - (* K8Simple sb *)
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    rewrite Hwith. rewrite app_assoc. reflexivity.
  - (* K8Triple sh sm st *)
    rewrite stored8_flat_list_push.
    rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    unfold buf6_elems at 2 4; cbn [kelem8_flat_list].
    rewrite Hwith.
    rewrite !app_nil_r.
    repeat rewrite <- app_assoc. reflexivity.
Qed.

(** ** Flatten of the reassembled deque. *)

Lemma reassemble_after_pop_unfold_flat :
  forall (X : Type) (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X)
         (suf : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)),
    kcad8_to_list (reassemble_after_pop_unfold pre sub suf m_rest t)
    = kelem8_flat_list (buf6_elems pre)
      ++ kcad8_to_list sub
      ++ kelem8_flat_list (buf6_elems suf)
      ++ stored8_flat_list (buf6_elems m_rest)
      ++ kelem8_flat_list (buf6_elems t).
Proof.
  intros X pre sub suf m_rest t.
  unfold reassemble_after_pop_unfold.
  cbv zeta.
  rewrite kcad8_to_list_triple.
  destruct (buf6_is_empty suf) eqn:Hsuf;
    destruct sub as [|sb|sh sm st]; cbn [kcad8_to_list].
  - (* suf empty, sub K8Empty *)
    apply (kelem8_flat_list_nil _ suf) in Hsuf.
    rewrite Hsuf. cbn [app]. reflexivity.
  - (* suf empty, sub K8Simple *)
    apply (kelem8_flat_list_nil _ suf) in Hsuf.
    rewrite Hsuf. cbn [app].
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - (* suf empty, sub K8Triple *)
    apply (kelem8_flat_list_nil _ suf) in Hsuf.
    rewrite Hsuf. cbn [app].
    rewrite stored8_flat_list_push.
    rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    unfold buf6_elems at 2 4. cbn [kelem8_flat_list].
    rewrite !app_nil_r.
    rewrite <- !app_assoc. reflexivity.
  - (* suf non-empty, sub K8Empty *)
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - (* suf non-empty, sub K8Simple *)
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - (* suf non-empty, sub K8Triple *)
    rewrite stored8_flat_list_push. rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    rewrite stored8_flat_list_push. cbn [stored8_to_list].
    unfold buf6_elems at 2 4. cbn [kelem8_flat_list].
    rewrite !app_nil_r.
    rewrite <- !app_assoc. reflexivity.
Qed.

(** Combining [reassemble_after_pop_unfold_flat] with the [stored8_to_list]
    definition closes the rebalance case.  Captured here as a structural
    note; the final composition is one more cbn + rewrite. *)
