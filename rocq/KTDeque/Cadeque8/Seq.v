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

(** Small stored8 sequence law. *)
Lemma stored8_to_list_small :
  forall (X : Type) (b : Buf6 (KElem8 X)),
    stored8_to_list (StoredSmall8 b) = kelem8_flat_list (buf6_elems b).
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
  - (* Simple, Triple (WC O(1) fix):
       K8Triple ba (buf6_push (StoredSmall8 h2) m2) t2 *)
    rewrite kcad8_to_list_simple, !kcad8_to_list_triple.
    rewrite stored8_flat_list_push.
    rewrite stored8_to_list_small.
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
    kcad8_to_list (K8Triple h m t) = x :: kcad8_to_list (kcad8_simple_or_empty t).
Proof.
  intros X h m t x h' Hpop Hhe Hme.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_seq_some in Hpop. unfold buf6_to_list in Hpop.
  apply buf6_pop_none_empty in Hme.
  apply (stored8_flat_list_nil _ m) in Hme.
  apply (kelem8_flat_list_nil _ h') in Hhe.
  unfold kelem8_flat_list at 1.
  rewrite Hpop. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems h')).
  rewrite Hhe, Hme. cbn.
  unfold kcad8_simple_or_empty.
  destruct (buf6_is_empty t) eqn:Ht.
  - apply (kelem8_flat_list_nil _ t) in Ht. rewrite Ht. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
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

(** ** Rebalance, middle non-empty — StoredSmall case. *)

Lemma pop_struct_seq_triple_rebalance_small :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (h' : Buf6 (KElem8 X))
         (b : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    buf6_pop h = Some (XBase8 x, h') ->
    buf6_is_empty h' = true ->
    buf6_pop m = Some (StoredSmall8 b, m_rest) ->
    kcad8_to_list (K8Triple h m t)
    = x :: kcad8_to_list
              (reassemble_after_pop_unfold b K8Empty (mkBuf6 []) m_rest t).
Proof.
  intros X h m t x h' b m_rest Hh Hhe Hm.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_seq_some in Hh. unfold buf6_to_list in Hh.
  apply (kelem8_flat_list_nil _ h') in Hhe.
  unfold kelem8_flat_list at 1.
  rewrite Hh. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems h')).
  rewrite Hhe. cbn [app].
  apply buf6_pop_some_elems in Hm.
  unfold stored8_flat_list at 1.
  rewrite Hm. fold (stored8_flat_list (buf6_elems m_rest)).
  cbn [stored8_to_list].
  rewrite reassemble_after_pop_unfold_flat.
  cbn [kcad8_to_list].
  (* RHS has kelem8_flat_list (buf6_elems (mkBuf6 [])) which we want to be []. *)
  replace (kelem8_flat_list (buf6_elems (mkBuf6 (@nil (KElem8 X)))))
    with (@nil X) by reflexivity.
  cbn [app].
  (* LHS is left-assoc, RHS is right-assoc — fix via app_assoc. *)
  rewrite app_assoc. reflexivity.
Qed.

(** ** Rebalance, middle non-empty — StoredBig case. *)

Lemma pop_struct_seq_triple_rebalance_big :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (h' : Buf6 (KElem8 X))
         (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X)
         (suf : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    buf6_pop h = Some (XBase8 x, h') ->
    buf6_is_empty h' = true ->
    buf6_pop m = Some (StoredBig8 pre sub suf, m_rest) ->
    kcad8_to_list (K8Triple h m t)
    = x :: kcad8_to_list
              (reassemble_after_pop_unfold pre sub suf m_rest t).
Proof.
  intros X h m t x h' pre sub suf m_rest Hh Hhe Hm.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_seq_some in Hh. unfold buf6_to_list in Hh.
  apply (kelem8_flat_list_nil _ h') in Hhe.
  unfold kelem8_flat_list at 1.
  rewrite Hh. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems h')).
  rewrite Hhe. cbn [app].
  apply buf6_pop_some_elems in Hm.
  unfold stored8_flat_list at 1.
  rewrite Hm. fold (stored8_flat_list (buf6_elems m_rest)).
  cbn [stored8_to_list].
  rewrite reassemble_after_pop_unfold_flat.
  rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Boundary fallbacks: head already empty when pop is called.
       These cover the cases in [kcad8_pop_struct] where the
       structural walk descends through an empty [h] to [m] or [t].
       They never fire under the maintained invariant but the code
       handles them, so [seq] preservation must too. *)

Lemma pop_struct_seq_triple_h_empty_small :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (b : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)) (x : X) (b' : Buf6 (KElem8 X)),
    buf6_pop h = None ->
    buf6_pop m = Some (StoredSmall8 b, m_rest) ->
    buf6_pop b = Some (XBase8 x, b') ->
    kcad8_to_list (K8Triple h m t)
    = x :: kcad8_to_list
              (reassemble_after_pop_unfold b' K8Empty (mkBuf6 []) m_rest t).
Proof.
  intros X h m t b m_rest x b' Hh Hm Hbp.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_none_empty in Hh.
  apply (kelem8_flat_list_nil _ h) in Hh.
  rewrite Hh. cbn [app].
  apply buf6_pop_some_elems in Hm.
  unfold stored8_flat_list at 1.
  rewrite Hm. fold (stored8_flat_list (buf6_elems m_rest)).
  cbn [stored8_to_list].
  apply buf6_pop_seq_some in Hbp. unfold buf6_to_list in Hbp.
  unfold kelem8_flat_list at 1.
  rewrite Hbp. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems b')).
  rewrite reassemble_after_pop_unfold_flat.
  cbn [kcad8_to_list].
  replace (kelem8_flat_list (buf6_elems (mkBuf6 (@nil (KElem8 X)))))
    with (@nil X) by reflexivity.
  cbn [app].
  rewrite app_assoc. reflexivity.
Qed.

Lemma pop_struct_seq_triple_h_empty_big :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (pre : Buf6 (KElem8 X))
         (sub : KCadeque8 X) (suf : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)) (x : X) (pre' : Buf6 (KElem8 X)),
    buf6_pop h = None ->
    buf6_pop m = Some (StoredBig8 pre sub suf, m_rest) ->
    buf6_pop pre = Some (XBase8 x, pre') ->
    kcad8_to_list (K8Triple h m t)
    = x :: kcad8_to_list
              (reassemble_after_pop_unfold pre' sub suf m_rest t).
Proof.
  intros X h m t pre sub suf m_rest x pre' Hh Hm Hpre.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_none_empty in Hh.
  apply (kelem8_flat_list_nil _ h) in Hh.
  rewrite Hh. cbn [app].
  apply buf6_pop_some_elems in Hm.
  unfold stored8_flat_list at 1.
  rewrite Hm. fold (stored8_flat_list (buf6_elems m_rest)).
  cbn [stored8_to_list].
  apply buf6_pop_seq_some in Hpre. unfold buf6_to_list in Hpre.
  unfold kelem8_flat_list at 1.
  rewrite Hpre. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems pre')).
  rewrite reassemble_after_pop_unfold_flat.
  rewrite <- !app_assoc. reflexivity.
Qed.

Lemma pop_struct_seq_triple_h_m_empty_t :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X)),
    buf6_pop h = None ->
    buf6_pop m = None ->
    buf6_pop t = Some (XBase8 x, t') ->
    kcad8_to_list (K8Triple h m t)
    = x :: (if buf6_is_empty t' then []
            else kcad8_to_list (K8Simple t')).
Proof.
  intros X h m t x t' Hh Hm Ht.
  rewrite kcad8_to_list_triple.
  apply buf6_pop_none_empty in Hh.
  apply (kelem8_flat_list_nil _ h) in Hh. rewrite Hh.
  apply buf6_pop_none_empty in Hm.
  apply (stored8_flat_list_nil _ m) in Hm. rewrite Hm.
  cbn [app].
  apply buf6_pop_seq_some in Ht. unfold buf6_to_list in Ht.
  unfold kelem8_flat_list at 1. rewrite Ht. cbn [kelem8_to_list].
  fold (kelem8_flat_list (buf6_elems t')).
  destruct (buf6_is_empty t') eqn:Hte.
  - apply (kelem8_flat_list_nil _ t') in Hte. rewrite Hte. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
Qed.

(** ** Composition: structural pop preserves the sequence. *)

Theorem kcad8_pop_struct_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop_struct k = Some (x, k') ->
    kcad8_to_list k = x :: kcad8_to_list k'.
Proof.
  intros X k x k' H.
  destruct k as [|b|h m t].
  - (* K8Empty *) discriminate.
  - (* K8Simple *) apply pop_struct_seq_simple, H.
  - (* K8Triple *)
    cbn [kcad8_pop_struct] in H.
    destruct (buf6_pop h) as [[e h']|] eqn:Hpop.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty h') eqn:Hhe.
      * (* rebalance_after_h_empty returned Some k' *)
        unfold rebalance_after_h_empty in H.
        destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
        -- destruct (stored_sub_left_safe s) eqn:Hsls.
           2: { discriminate H. }
           destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
           ++ injection H as Hxv Hk'. subst xv k'.
              apply pop_struct_seq_triple_rebalance_small
                with (h' := h'); assumption.
           ++ injection H as Hxv Hk'. subst xv k'.
              apply pop_struct_seq_triple_rebalance_big
                with (h' := h'); assumption.
        -- injection H as Hxv Hk'. subst xv k'.
           apply pop_struct_seq_triple_rebalance_m_empty
             with (h' := h'); assumption.
      * injection H as Hxv Hk'. subst xv k'.
        apply pop_struct_seq_triple_easy with (h' := h'); assumption.
    + destruct (buf6_pop m) as [[s m_rest]|] eqn:Hmp.
      * destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
        -- destruct (buf6_pop b) as [[e b']|] eqn:Hbp.
           2: { discriminate H. }
           destruct e as [xv|sv].
           2: { discriminate H. }
           injection H as Hxv Hk'. subst xv k'.
           apply pop_struct_seq_triple_h_empty_small
             with (b := b); assumption.
        -- destruct (buf6_pop pre) as [[e pre']|] eqn:Hpep.
           2: { discriminate H. }
           destruct e as [xv|sv].
           2: { discriminate H. }
           injection H as Hxv Hk'. subst xv k'.
           apply pop_struct_seq_triple_h_empty_big
             with (pre := pre) (sub := sub) (suf := suf); assumption.
      * destruct (buf6_pop t) as [[e t']|] eqn:Htp.
        2: { discriminate H. }
        destruct e as [xv|sv].
        2: { discriminate H. }
        injection H as Hxv Hk'. subst xv k'.
        rewrite (pop_struct_seq_triple_h_m_empty_t _ _ _ _ x t' Hpop Hmp Htp).
        destruct (buf6_is_empty t') eqn:Hte; reflexivity.
Qed.

(** ** Public pop preserves the sequence. *)

Theorem kcad8_pop_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop k = Some (x, k') ->
    kcad8_to_list k = x :: kcad8_to_list k'.
Proof.
  intros X k x k' H. unfold kcad8_pop in H.
  destruct (kcad8_pop_struct k) as [[x0 k0]|] eqn:Hstr.
  - injection H as Hx Hk. subst x0 k0.
    apply kcad8_pop_struct_seq, Hstr.
  - destruct (kcad8_to_list k) as [|y ys] eqn:Hlist; [discriminate|].
    injection H as Hx Hk. subst y k'.
    f_equal. symmetry. apply kcad8_to_list_from_list.
Qed.

(* =====================================================================
   Eject preserves the sequence — symmetric mirror of pop.
   ===================================================================== *)

Lemma buf6_eject_some_elems :
  forall (X : Type) (b : Buf6 X) (x : X) (b' : Buf6 X),
    buf6_eject b = Some (b', x) ->
    buf6_elems b = buf6_elems b' ++ [x].
Proof.
  intros X b x b' H. apply buf6_eject_seq_some in H.
  unfold buf6_to_list in H. exact H.
Qed.

Lemma buf6_eject_none_empty :
  forall (X : Type) (b : Buf6 X),
    buf6_eject b = None -> buf6_is_empty b = true.
Proof.
  intros X b H. apply buf6_eject_seq_none in H.
  rewrite buf6_is_empty_iff_nil. unfold buf6_to_list in H. exact H.
Qed.

(** ** Flat-list app distributes over kelem8_flat_list / stored8_flat_list. *)

Lemma kelem8_flat_list_app :
  forall (X : Type) (xs ys : list (KElem8 X)),
    kelem8_flat_list (xs ++ ys)
    = kelem8_flat_list xs ++ kelem8_flat_list ys.
Proof.
  intros X xs ys. unfold kelem8_flat_list.
  induction xs as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

Lemma stored8_flat_list_app :
  forall (X : Type) (xs ys : list (Stored8 X)),
    stored8_flat_list (xs ++ ys)
    = stored8_flat_list xs ++ stored8_flat_list ys.
Proof.
  intros X xs ys. unfold stored8_flat_list.
  induction xs as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite IH. rewrite app_assoc. reflexivity.
Qed.

(** ** Helper: kelem8_flat_list of a singleton XBase8. *)

Lemma kelem8_flat_list_singleton_base :
  forall (X : Type) (x : X),
    kelem8_flat_list [XBase8 x] = [x].
Proof. intros; reflexivity. Qed.

(** ** Helper: rewrite kelem8_flat_list of (b' ++ [XBase8 x]) into the
       expected shape. *)

Lemma kelem8_flat_list_inject_form :
  forall (X : Type) (b' : Buf6 (KElem8 X)) (b : Buf6 (KElem8 X)) (x : X),
    buf6_elems b = buf6_elems b' ++ [XBase8 x] ->
    kelem8_flat_list (buf6_elems b)
    = kelem8_flat_list (buf6_elems b') ++ [x].
Proof.
  intros X b' b x H. rewrite H.
  rewrite kelem8_flat_list_app.
  rewrite kelem8_flat_list_singleton_base. reflexivity.
Qed.

(** ** Helper: rewrite stored8_flat_list of (b' ++ [s]) into the
       expected shape. *)

Lemma stored8_flat_list_inject_form :
  forall (X : Type) (b' : Buf6 (Stored8 X)) (b : Buf6 (Stored8 X))
         (s : Stored8 X),
    buf6_elems b = buf6_elems b' ++ [s] ->
    stored8_flat_list (buf6_elems b)
    = stored8_flat_list (buf6_elems b') ++ stored8_to_list s.
Proof.
  intros X b' b s H. rewrite H.
  rewrite stored8_flat_list_app.
  cbn [stored8_flat_list]. rewrite app_nil_r. reflexivity.
Qed.

(** ** Eject preserves the sequence — K8Simple case. *)

Lemma eject_struct_seq_simple :
  forall (X : Type) (b : Buf6 (KElem8 X)) (k' : KCadeque8 X) (x : X),
    kcad8_eject_struct (K8Simple b) = Some (k', x) ->
    kcad8_to_list (K8Simple b) = kcad8_to_list k' ++ [x].
Proof.
  intros X b k' x H. cbn [kcad8_eject_struct] in H.
  destruct (buf6_eject b) as [[b' e]|] eqn:Hej.
  2: { discriminate H. }
  destruct e as [xv|sv].
  2: { discriminate H. }
  injection H as Hk' Hxv. subst xv k'.
  apply buf6_eject_some_elems in Hej.
  rewrite kcad8_to_list_simple.
  rewrite (kelem8_flat_list_inject_form _ b' b x Hej).
  destruct (buf6_is_empty b') eqn:He.
  - apply (kelem8_flat_list_nil _ b') in He. rewrite He. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
Qed.

(** ** Eject — K8Triple, easy case (t' non-empty). *)

Lemma eject_struct_seq_triple_easy :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X)),
    buf6_eject t = Some (t', XBase8 x) ->
    buf6_is_empty t' = false ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list (K8Triple h m t') ++ [x].
Proof.
  intros X h m t x t' Het He.
  rewrite !kcad8_to_list_triple.
  apply buf6_eject_some_elems in Het.
  rewrite (kelem8_flat_list_inject_form _ t' t x Het).
  rewrite !app_assoc. reflexivity.
Qed.

(** ** Eject — K8Triple, rebalance with middle empty. *)

Lemma eject_struct_seq_triple_rebalance_m_empty :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X)),
    buf6_eject t = Some (t', XBase8 x) ->
    buf6_is_empty t' = true ->
    buf6_eject m = None ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list (kcad8_simple_or_empty h) ++ [x].
Proof.
  intros X h m t x t' Het Hte Hme.
  rewrite kcad8_to_list_triple.
  apply buf6_eject_some_elems in Het.
  apply buf6_eject_none_empty in Hme.
  apply (stored8_flat_list_nil _ m) in Hme.
  apply (kelem8_flat_list_nil _ t') in Hte.
  rewrite (kelem8_flat_list_inject_form _ t' t x Het).
  rewrite Hte, Hme. cbn [app].
  unfold kcad8_simple_or_empty.
  destruct (buf6_is_empty h) eqn:Hh.
  - apply (kelem8_flat_list_nil _ h) in Hh. rewrite Hh. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
Qed.

(** ** Eject — reassemble flat. *)

Lemma reassemble_after_eject_unfold_flat :
  forall (X : Type) (h : Buf6 (KElem8 X))
         (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X)
         (suf : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    kcad8_to_list (reassemble_after_eject_unfold h pre sub suf m_rest)
    = kelem8_flat_list (buf6_elems h)
      ++ stored8_flat_list (buf6_elems m_rest)
      ++ kelem8_flat_list (buf6_elems pre)
      ++ kcad8_to_list sub
      ++ kelem8_flat_list (buf6_elems suf).
Proof.
  intros X h pre sub suf m_rest.
  unfold reassemble_after_eject_unfold.
  cbv zeta.
  rewrite kcad8_to_list_triple.
  destruct (buf6_is_empty pre) eqn:Hpre;
    destruct sub as [|sb|sh sm st]; cbn [kcad8_to_list].
  - apply (kelem8_flat_list_nil _ pre) in Hpre.
    rewrite Hpre. cbn [app]. reflexivity.
  - apply (kelem8_flat_list_nil _ pre) in Hpre.
    rewrite Hpre. cbn [app].
    rewrite stored8_flat_list_inject. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - apply (kelem8_flat_list_nil _ pre) in Hpre.
    rewrite Hpre. cbn [app].
    rewrite stored8_flat_list_inject. rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    unfold buf6_elems at 2 4; cbn [kelem8_flat_list].
    rewrite !app_nil_r.
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored8_flat_list_inject. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored8_flat_list_inject. cbn [stored8_to_list].
    rewrite stored8_flat_list_inject. cbn [stored8_to_list].
    rewrite <- !app_assoc. reflexivity.
  - rewrite stored8_flat_list_inject. rewrite stored8_to_list_big.
    rewrite kcad8_to_list_triple.
    rewrite stored8_flat_list_inject. cbn [stored8_to_list].
    unfold buf6_elems at 2 4; cbn [kelem8_flat_list].
    rewrite !app_nil_r.
    rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Eject — rebalance, StoredSmall case. *)

Lemma eject_struct_seq_triple_rebalance_small :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X))
         (b : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    buf6_eject t = Some (t', XBase8 x) ->
    buf6_is_empty t' = true ->
    buf6_eject m = Some (m_rest, StoredSmall8 b) ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list
        (reassemble_after_eject_unfold h b K8Empty (mkBuf6 []) m_rest)
      ++ [x].
Proof.
  intros X h m t x t' b m_rest Het Hte Hme.
  rewrite kcad8_to_list_triple.
  apply buf6_eject_some_elems in Het.
  apply (kelem8_flat_list_nil _ t') in Hte.
  rewrite (kelem8_flat_list_inject_form _ t' t x Het).
  rewrite Hte. cbn [app].
  apply buf6_eject_some_elems in Hme.
  rewrite (stored8_flat_list_inject_form _ m_rest m (StoredSmall8 b) Hme).
  cbn [stored8_to_list].
  rewrite reassemble_after_eject_unfold_flat.
  cbn [kcad8_to_list].
  replace (kelem8_flat_list (buf6_elems (mkBuf6 (@nil (KElem8 X)))))
    with (@nil X) by reflexivity.
  cbn [app]. rewrite app_nil_r.
  rewrite !app_assoc. reflexivity.
Qed.

(** ** Eject — rebalance via the WC O(1) fix path (StoredSmall8
       promoted directly to new tail, bypassing reassemble). *)

Lemma eject_struct_seq_triple_rebalance_small_promote :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X))
         (b : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    buf6_eject t = Some (t', XBase8 x) ->
    buf6_is_empty t' = true ->
    buf6_eject m = Some (m_rest, StoredSmall8 b) ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list (K8Triple h m_rest b) ++ [x].
Proof.
  intros X h m t x t' b m_rest Het Hte Hme.
  rewrite !kcad8_to_list_triple.
  apply buf6_eject_some_elems in Het.
  apply (kelem8_flat_list_nil _ t') in Hte.
  rewrite (kelem8_flat_list_inject_form _ t' t x Het).
  rewrite Hte. cbn [app].
  apply buf6_eject_some_elems in Hme.
  rewrite (stored8_flat_list_inject_form _ m_rest m (StoredSmall8 b) Hme).
  cbn [stored8_to_list].
  rewrite !app_assoc. reflexivity.
Qed.

(** ** Eject — rebalance, StoredBig case. *)

Lemma eject_struct_seq_triple_rebalance_big :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (t' : Buf6 (KElem8 X))
         (pre : Buf6 (KElem8 X)) (sub : KCadeque8 X)
         (suf : Buf6 (KElem8 X)) (m_rest : Buf6 (Stored8 X)),
    buf6_eject t = Some (t', XBase8 x) ->
    buf6_is_empty t' = true ->
    buf6_eject m = Some (m_rest, StoredBig8 pre sub suf) ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list
        (reassemble_after_eject_unfold h pre sub suf m_rest)
      ++ [x].
Proof.
  intros X h m t x t' pre sub suf m_rest Het Hte Hme.
  rewrite kcad8_to_list_triple.
  apply buf6_eject_some_elems in Het.
  apply (kelem8_flat_list_nil _ t') in Hte.
  rewrite (kelem8_flat_list_inject_form _ t' t x Het).
  rewrite Hte. cbn [app].
  apply buf6_eject_some_elems in Hme.
  rewrite (stored8_flat_list_inject_form _ m_rest m
             (StoredBig8 pre sub suf) Hme).
  rewrite stored8_to_list_big.
  rewrite reassemble_after_eject_unfold_flat.
  rewrite !app_assoc. reflexivity.
Qed.

(** ** Eject — boundary fallbacks (t already empty).

    Note: for [StoredSmall8 b] in the rightmost stored cell, the unfold
    yields [suf = mkBuf6 []], whose eject is None — that case never
    fires, so we only need the [StoredBig8] case. *)

Lemma eject_struct_seq_triple_t_empty_big :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (pre : Buf6 (KElem8 X))
         (sub : KCadeque8 X) (suf : Buf6 (KElem8 X))
         (m_rest : Buf6 (Stored8 X)) (x : X) (suf' : Buf6 (KElem8 X)),
    buf6_eject t = None ->
    buf6_eject m = Some (m_rest, StoredBig8 pre sub suf) ->
    buf6_eject suf = Some (suf', XBase8 x) ->
    kcad8_to_list (K8Triple h m t)
    = kcad8_to_list
        (reassemble_after_eject_unfold h pre sub suf' m_rest)
      ++ [x].
Proof.
  intros X h m t pre sub suf m_rest x suf' Ht Hm Hsf.
  rewrite kcad8_to_list_triple.
  apply buf6_eject_none_empty in Ht.
  apply (kelem8_flat_list_nil _ t) in Ht. rewrite Ht. rewrite app_nil_r.
  apply buf6_eject_some_elems in Hm.
  rewrite (stored8_flat_list_inject_form _ m_rest m
             (StoredBig8 pre sub suf) Hm).
  rewrite stored8_to_list_big.
  apply buf6_eject_some_elems in Hsf.
  rewrite (kelem8_flat_list_inject_form _ suf' suf x Hsf).
  rewrite reassemble_after_eject_unfold_flat.
  rewrite !app_assoc. reflexivity.
Qed.

Lemma eject_struct_seq_triple_t_m_empty_h :
  forall (X : Type) (h : Buf6 (KElem8 X)) (m : Buf6 (Stored8 X))
         (t : Buf6 (KElem8 X)) (x : X) (h' : Buf6 (KElem8 X)),
    buf6_eject t = None ->
    buf6_eject m = None ->
    buf6_eject h = Some (h', XBase8 x) ->
    kcad8_to_list (K8Triple h m t)
    = (if buf6_is_empty h' then []
       else kcad8_to_list (K8Simple h')) ++ [x].
Proof.
  intros X h m t x h' Ht Hm Hh.
  rewrite kcad8_to_list_triple.
  apply buf6_eject_none_empty in Ht.
  apply (kelem8_flat_list_nil _ t) in Ht. rewrite Ht. rewrite app_nil_r.
  apply buf6_eject_none_empty in Hm.
  apply (stored8_flat_list_nil _ m) in Hm. rewrite Hm. rewrite app_nil_r.
  apply buf6_eject_some_elems in Hh.
  rewrite (kelem8_flat_list_inject_form _ h' h x Hh).
  destruct (buf6_is_empty h') eqn:Hhe.
  - apply (kelem8_flat_list_nil _ h') in Hhe. rewrite Hhe. reflexivity.
  - rewrite kcad8_to_list_simple. reflexivity.
Qed.

(** ** Composition: structural eject preserves the sequence. *)

Theorem kcad8_eject_struct_seq :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject_struct k = Some (k', x) ->
    kcad8_to_list k = kcad8_to_list k' ++ [x].
Proof.
  intros X k k' x H.
  destruct k as [|b|h m t].
  - discriminate.
  - apply eject_struct_seq_simple, H.
  - cbn [kcad8_eject_struct] in H.
    destruct (buf6_eject t) as [[t' e]|] eqn:Het.
    + destruct e as [xv|sv].
      2: { discriminate H. }
      destruct (buf6_is_empty t') eqn:Hte.
      * unfold rebalance_after_t_empty in H.
        destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
        -- destruct (stored_sub_right_safe s) eqn:Hsrs.
           ++ destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
              ** injection H as Hk' Hxv. subst xv k'.
                 apply eject_struct_seq_triple_rebalance_small
                   with (t' := t'); assumption.
              ** injection H as Hk' Hxv. subst xv k'.
                 apply eject_struct_seq_triple_rebalance_big
                   with (t' := t'); assumption.
           ++ (* WC O(1) fix path: StoredSmall8 promoted to new tail. *)
              destruct s as [b|pre sub suf]; cbn in H.
              ** injection H as Hk' Hxv. subst xv k'.
                 apply eject_struct_seq_triple_rebalance_small_promote
                   with (t' := t'); assumption.
              ** discriminate H.
        -- injection H as Hk' Hxv. subst xv k'.
           apply eject_struct_seq_triple_rebalance_m_empty
             with (t' := t'); assumption.
      * injection H as Hk' Hxv. subst xv k'.
        apply eject_struct_seq_triple_easy with (t' := t'); assumption.
    + destruct (buf6_eject m) as [[m_rest s]|] eqn:Hmp.
      * destruct s as [b|pre sub suf]; cbn [unfold_stored] in H.
        -- (* StoredSmall — suf is empty; eject returns None, so
              H is None = Some (k', x) which discriminates. *)
           cbn in H. discriminate H.
        -- destruct (buf6_eject suf) as [[suf' e]|] eqn:Hsp.
           2: { discriminate H. }
           destruct e as [xv|sv].
           2: { discriminate H. }
           injection H as Hk' Hxv. subst xv k'.
           apply eject_struct_seq_triple_t_empty_big
             with (pre := pre) (sub := sub) (suf := suf); assumption.
      * destruct (buf6_eject h) as [[h' e]|] eqn:Hhp.
        2: { discriminate H. }
        destruct e as [xv|sv].
        2: { discriminate H. }
        injection H as Hk' Hxv. subst xv k'.
        rewrite (eject_struct_seq_triple_t_m_empty_h _ _ _ _ x h' Het Hmp Hhp).
        destruct (buf6_is_empty h') eqn:Hhe; reflexivity.
Qed.

(** ** Public eject preserves the sequence. *)

Theorem kcad8_eject_seq :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject k = Some (k', x) ->
    kcad8_to_list k = kcad8_to_list k' ++ [x].
Proof.
  intros X k k' x H. unfold kcad8_eject in H.
  destruct (kcad8_eject_struct k) as [[k0 x0]|] eqn:Hstr.
  - injection H as Hk Hx. subst x0 k0.
    apply kcad8_eject_struct_seq, Hstr.
  - destruct (List.rev (kcad8_to_list k)) as [|y ys] eqn:Hrev;
      [discriminate|].
    injection H as Hk Hx. subst y k'.
    rewrite kcad8_to_list_from_list.
    (* Goal: kcad8_to_list k = List.rev ys ++ [x] *)
    apply (f_equal (@List.rev X)) in Hrev.
    rewrite rev_involutive in Hrev. cbn in Hrev.
    rewrite Hrev. reflexivity.
Qed.
