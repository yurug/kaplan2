(** * Module: KTDeque.Cadeque8.OpsFast — extraction-friendly Cadeque8 ops.

    Same trick as [DequePtr/OpsKT.v]'s [push_kt4] / [pop_kt4]:
    OCaml extracts [option (X * Y)] as nested heap allocations — one
    block for [Some], another for the [(X, Y)] pair.  Using a flat
    [PopOk : X -> Y -> pop_result8] saves one allocation per
    successful op, which matters in the hot loop of the bench.

    The fast variants live alongside [Cadeque8/Ops.v]'s certified
    versions; this file proves each <code>_fast</code> equivalent
    to the original.  In particular the seq theorems in
    [Cadeque8/Seq.v] and the regularity theorems in [Cadeque8/WF.v]
    transfer through the equivalence — no separate proof needed. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops.

(* ========================================================================== *)
(* Flat result types — replace [option (X * KCadeque8 X)].                    *)
(* ========================================================================== *)

(** [pop_result8 X]: result of a pop-shaped op.  PopOk8 takes the
    popped element and the residual cadeque as two fields rather than
    a heap-allocated pair, saving one allocation per successful op
    in the extracted OCaml. *)
Inductive pop_result8 (X : Type) : Type :=
| PopFail8 : pop_result8 X
| PopOk8   : X -> KCadeque8 X -> pop_result8 X.
Arguments PopFail8 {X}.
Arguments PopOk8   {X} _ _.

(** [eject_result8 X]: symmetric — EjectOk8 takes the residual cadeque
    then the ejected element. *)
Inductive eject_result8 (X : Type) : Type :=
| EjectFail8 : eject_result8 X
| EjectOk8   : KCadeque8 X -> X -> eject_result8 X.
Arguments EjectFail8 {X}.
Arguments EjectOk8   {X} _ _.

(** Lifting helpers used in the equivalence theorems. *)
Definition pop_result8_of_option {X : Type}
    (o : option (X * KCadeque8 X)) : pop_result8 X :=
  match o with
  | None         => PopFail8
  | Some (x, k') => PopOk8 x k'
  end.

Definition eject_result8_of_option {X : Type}
    (o : option (KCadeque8 X * X)) : eject_result8 X :=
  match o with
  | None         => EjectFail8
  | Some (k', x) => EjectOk8 k' x
  end.

(* ========================================================================== *)
(* Push / inject — push/inject don't have option in their return type, so the *)
(* fast variants are essentially identical.  We define them for symmetry      *)
(* (and because the inlining helper here uses pop_result8/eject_result8 for   *)
(* push/inject too in the eventual public-API record).                        *)
(* ========================================================================== *)

Definition kcad8_push_fast {X : Type} (x : X) (k : KCadeque8 X) : KCadeque8 X :=
  match k with
  | K8Empty        => K8Simple (mkBuf6 [XBase8 x])
  | K8Simple b     => K8Simple (buf6_push (XBase8 x) b)
  | K8Triple h m t => K8Triple (buf6_push (XBase8 x) h) m t
  end.

Definition kcad8_inject_fast {X : Type} (k : KCadeque8 X) (x : X) : KCadeque8 X :=
  match k with
  | K8Empty        => K8Simple (mkBuf6 [XBase8 x])
  | K8Simple b     => K8Simple (buf6_inject b (XBase8 x))
  | K8Triple h m t => K8Triple h m (buf6_inject t (XBase8 x))
  end.

(* ========================================================================== *)
(* Pop — fast variant that avoids the option (X * KCadeque8 X) boxing.        *)
(* ========================================================================== *)

(** Structural fast path: same dispatch as [kcad8_pop_struct] but
    produces [pop_result8] at every leaf.  No nested options. *)
Definition kcad8_pop_struct_fast {X : Type} (k : KCadeque8 X)
                                 : pop_result8 X :=
  match k with
  | K8Empty => PopFail8
  | K8Simple b =>
      match buf6_pop b with
      | Some (XBase8 x, b') =>
          PopOk8 x (if buf6_is_empty b' then K8Empty else K8Simple b')
      | _ => PopFail8
      end
  | K8Triple h m t =>
      match buf6_pop h with
      | Some (XBase8 x, h') =>
          if buf6_is_empty h' then
            (* fused rebalance + result construction *)
            match rebalance_after_h_empty m t with
            | Some k' => PopOk8 x k'
            | None    => PopFail8
            end
          else PopOk8 x (K8Triple h' m t)
      | Some (XStored8 _, _) => PopFail8
      | None =>
          match buf6_pop m with
          | Some (s, m_rest) =>
              let '(pre, sub, suf) := unfold_stored s in
              match buf6_pop pre with
              | Some (XBase8 x, pre') =>
                  PopOk8 x (reassemble_after_pop_unfold pre' sub suf m_rest t)
              | _ => PopFail8
              end
          | None =>
              match buf6_pop t with
              | Some (XBase8 x, t') =>
                  PopOk8 x (if buf6_is_empty t' then K8Empty else K8Simple t')
              | _ => PopFail8
              end
          end
      end
  end.

(** Public fast pop: structural fast path, then the [kcad8_from_list]
    fallback when the structural path bails out. *)
Definition kcad8_pop_fast {X : Type} (k : KCadeque8 X) : pop_result8 X :=
  match kcad8_pop_struct_fast k with
  | PopOk8 x k' => PopOk8 x k'
  | PopFail8 =>
      match kcad8_to_list k with
      | []      => PopFail8
      | x :: xs => PopOk8 x (kcad8_from_list xs)
      end
  end.

(* ========================================================================== *)
(* Eject — symmetric.                                                         *)
(* ========================================================================== *)

Definition kcad8_eject_struct_fast {X : Type} (k : KCadeque8 X)
                                   : eject_result8 X :=
  match k with
  | K8Empty => EjectFail8
  | K8Simple b =>
      match buf6_eject b with
      | Some (b', XBase8 x) =>
          EjectOk8 (if buf6_is_empty b' then K8Empty else K8Simple b') x
      | _ => EjectFail8
      end
  | K8Triple h m t =>
      match buf6_eject t with
      | Some (t', XBase8 x) =>
          if buf6_is_empty t' then
            match rebalance_after_t_empty h m with
            | Some k' => EjectOk8 k' x
            | None    => EjectFail8
            end
          else EjectOk8 (K8Triple h m t') x
      | Some (_, XStored8 _) => EjectFail8
      | None =>
          match buf6_eject m with
          | Some (m_rest, s) =>
              let '(pre, sub, suf) := unfold_stored s in
              match buf6_eject suf with
              | Some (suf', XBase8 x) =>
                  EjectOk8 (reassemble_after_eject_unfold h pre sub suf' m_rest) x
              | _ => EjectFail8
              end
          | None =>
              match buf6_eject h with
              | Some (h', XBase8 x) =>
                  EjectOk8 (if buf6_is_empty h' then K8Empty else K8Simple h') x
              | _ => EjectFail8
              end
          end
      end
  end.

Definition kcad8_eject_fast {X : Type} (k : KCadeque8 X) : eject_result8 X :=
  match kcad8_eject_struct_fast k with
  | EjectOk8 k' x => EjectOk8 k' x
  | EjectFail8 =>
      match List.rev (kcad8_to_list k) with
      | []      => EjectFail8
      | x :: ys => EjectOk8 (kcad8_from_list (List.rev ys)) x
      end
  end.

(* ========================================================================== *)
(* Concat — already option-free; we just reorder for branch prediction        *)
(* (K8Empty short-circuits first), and inline the StoredSmall path for        *)
(* the (Triple, Simple) case.                                                 *)
(* ========================================================================== *)

Definition kcad8_concat_fast {X : Type} (a b : KCadeque8 X) : KCadeque8 X :=
  match a with
  | K8Empty => b
  | K8Simple ba =>
      match b with
      | K8Empty => a
      | K8Simple bb => K8Triple ba (mkBuf6 []) bb
      | K8Triple h2 m2 t2 =>
          let boundary :=
            StoredBig8 h2 (K8Triple (mkBuf6 []) m2 (mkBuf6 [])) (mkBuf6 []) in
          K8Triple ba (mkBuf6 [boundary]) t2
      end
  | K8Triple h1 m1 t1 =>
      match b with
      | K8Empty => a
      | K8Simple bb =>
          K8Triple h1 (buf6_inject m1 (StoredSmall8 t1)) bb
      | K8Triple h2 m2 t2 =>
          let boundary :=
            StoredBig8 t1 (K8Triple h2 m2 (mkBuf6 [])) (mkBuf6 []) in
          K8Triple h1 (buf6_inject m1 boundary) t2
      end
  end.

(* ========================================================================== *)
(* Equivalence theorems.                                                       *)
(* ========================================================================== *)

(** Push / inject — definitionally equal. *)
Theorem kcad8_push_fast_eq :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    kcad8_push_fast x k = kcad8_push x k.
Proof.
  intros X x k. destruct k; reflexivity.
Qed.

Theorem kcad8_inject_fast_eq :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_inject_fast k x = kcad8_inject k x.
Proof.
  intros X k x. destruct k; reflexivity.
Qed.

(** Concat — also definitionally equal (we just reordered the match). *)
Theorem kcad8_concat_fast_eq :
  forall (X : Type) (a b : KCadeque8 X),
    kcad8_concat_fast a b = kcad8_concat a b.
Proof.
  intros X a b. destruct a, b; reflexivity.
Qed.

(** Pop — the fast version produces the same result as the option-typed
    pop, via the lifting [pop_result8_of_option]. *)
Theorem kcad8_pop_struct_fast_eq :
  forall (X : Type) (k : KCadeque8 X),
    kcad8_pop_struct_fast k = pop_result8_of_option (kcad8_pop_struct k).
Proof.
  intros X k. destruct k as [|b|h m t]; cbn.
  - reflexivity.
  - destruct (buf6_pop b) as [[e b']|]; [|reflexivity].
    destruct e as [xv|sv]; [|reflexivity].
    destruct (buf6_is_empty b'); reflexivity.
  - destruct (buf6_pop h) as [[e h']|].
    + destruct e as [xv|sv]; [|reflexivity].
      destruct (buf6_is_empty h').
      * destruct (rebalance_after_h_empty m t) as [k'|]; reflexivity.
      * reflexivity.
    + destruct (buf6_pop m) as [[s m_rest]|].
      * destruct (unfold_stored s) as [[pre sub] suf].
        destruct (buf6_pop pre) as [[e pre']|]; [|reflexivity].
        destruct e as [xv|sv]; reflexivity.
      * destruct (buf6_pop t) as [[e t']|]; [|reflexivity].
        destruct e as [xv|sv]; [|reflexivity].
        destruct (buf6_is_empty t'); reflexivity.
Qed.

Theorem kcad8_pop_fast_eq :
  forall (X : Type) (k : KCadeque8 X),
    kcad8_pop_fast k = pop_result8_of_option (kcad8_pop k).
Proof.
  intros X k. unfold kcad8_pop_fast, kcad8_pop.
  rewrite kcad8_pop_struct_fast_eq.
  destruct (kcad8_pop_struct k) as [[xv k']|]; cbn.
  - reflexivity.
  - destruct (kcad8_to_list k) as [|y ys]; reflexivity.
Qed.

(** Eject — symmetric. *)
Theorem kcad8_eject_struct_fast_eq :
  forall (X : Type) (k : KCadeque8 X),
    kcad8_eject_struct_fast k = eject_result8_of_option (kcad8_eject_struct k).
Proof.
  intros X k. destruct k as [|b|h m t]; cbn.
  - reflexivity.
  - destruct (buf6_eject b) as [[b' e]|]; [|reflexivity].
    destruct e as [xv|sv]; [|reflexivity].
    destruct (buf6_is_empty b'); reflexivity.
  - destruct (buf6_eject t) as [[t' e]|].
    + destruct e as [xv|sv]; [|reflexivity].
      destruct (buf6_is_empty t').
      * destruct (rebalance_after_t_empty h m) as [k'|]; reflexivity.
      * reflexivity.
    + destruct (buf6_eject m) as [[m_rest s]|].
      * destruct (unfold_stored s) as [[pre sub] suf].
        destruct (buf6_eject suf) as [[suf' e]|]; [|reflexivity].
        destruct e as [xv|sv]; reflexivity.
      * destruct (buf6_eject h) as [[h' e]|]; [|reflexivity].
        destruct e as [xv|sv]; [|reflexivity].
        destruct (buf6_is_empty h'); reflexivity.
Qed.

Theorem kcad8_eject_fast_eq :
  forall (X : Type) (k : KCadeque8 X),
    kcad8_eject_fast k = eject_result8_of_option (kcad8_eject k).
Proof.
  intros X k. unfold kcad8_eject_fast, kcad8_eject.
  rewrite kcad8_eject_struct_fast_eq.
  destruct (kcad8_eject_struct k) as [[k' xv]|]; cbn.
  - reflexivity.
  - destruct (List.rev (kcad8_to_list k)) as [|y ys]; reflexivity.
Qed.

(* ========================================================================== *)
(* Convenience: sequence preservation transferred through the equivalences.   *)
(* ========================================================================== *)

From KTDeque.Cadeque8 Require Import Seq.

Theorem kcad8_push_fast_seq :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    kcad8_to_list (kcad8_push_fast x k) = x :: kcad8_to_list k.
Proof. intros; rewrite kcad8_push_fast_eq; apply kcad8_push_seq. Qed.

Theorem kcad8_inject_fast_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_to_list (kcad8_inject_fast k x) = kcad8_to_list k ++ [x].
Proof. intros; rewrite kcad8_inject_fast_eq; apply kcad8_inject_seq. Qed.

Theorem kcad8_concat_fast_seq :
  forall (X : Type) (a b : KCadeque8 X),
    kcad8_to_list (kcad8_concat_fast a b) = kcad8_to_list a ++ kcad8_to_list b.
Proof. intros; rewrite kcad8_concat_fast_eq; apply kcad8_concat_seq. Qed.

Theorem kcad8_pop_fast_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    kcad8_pop_fast k = PopOk8 x k' ->
    kcad8_to_list k = x :: kcad8_to_list k'.
Proof.
  intros X k x k' H. rewrite kcad8_pop_fast_eq in H.
  destruct (kcad8_pop k) as [[y k'']|] eqn:Hp; cbn in H; [|discriminate].
  injection H as Hx Hk. subst y k''.
  apply kcad8_pop_seq; exact Hp.
Qed.

Theorem kcad8_eject_fast_seq :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    kcad8_eject_fast k = EjectOk8 k' x ->
    kcad8_to_list k = kcad8_to_list k' ++ [x].
Proof.
  intros X k k' x H. rewrite kcad8_eject_fast_eq in H.
  destruct (kcad8_eject k) as [[k'' y]|] eqn:He; cbn in H; [|discriminate].
  injection H as Hk Hx. subst y k''.
  apply kcad8_eject_seq; exact He.
Qed.

(* ========================================================================== *)
(* Convenience: regularity preservation transferred through the equivalences. *)
(* ========================================================================== *)

From KTDeque.Cadeque8 Require Import WF.

Theorem kcad8_push_fast_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_push_fast x k).
Proof. intros; rewrite kcad8_push_fast_eq; apply kcad8_push_wf_strong; auto. Qed.

Theorem kcad8_inject_fast_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_inject_fast k x).
Proof. intros; rewrite kcad8_inject_fast_eq; apply kcad8_inject_wf_strong; auto. Qed.

Theorem kcad8_concat_fast_wf_strong :
  forall (X : Type) (a b : KCadeque8 X),
    wf_kcad8_strong a -> wf_kcad8_strong b ->
    wf_kcad8_strong (kcad8_concat_fast a b).
Proof. intros; rewrite kcad8_concat_fast_eq; apply kcad8_concat_wf_strong; auto. Qed.

Theorem kcad8_pop_fast_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X) (k' : KCadeque8 X),
    wf_kcad8_strong k -> kcad8_pop_fast k = PopOk8 x k' -> wf_kcad8_strong k'.
Proof.
  intros X k x k' Hwf H. rewrite kcad8_pop_fast_eq in H.
  destruct (kcad8_pop k) as [[y k'']|] eqn:Hp; cbn in H; [|discriminate].
  injection H as Hx Hk. subst y k''.
  eapply kcad8_pop_wf_strong; eauto.
Qed.

Theorem kcad8_eject_fast_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (k' : KCadeque8 X) (x : X),
    wf_kcad8_strong k -> kcad8_eject_fast k = EjectOk8 k' x -> wf_kcad8_strong k'.
Proof.
  intros X k k' x Hwf H. rewrite kcad8_eject_fast_eq in H.
  destruct (kcad8_eject k) as [[k'' y]|] eqn:He; cbn in H; [|discriminate].
  injection H as Hk Hx. subst y k''.
  eapply kcad8_eject_wf_strong; eauto.
Qed.

(* ========================================================================== *)
(* Inline variants — pure Rocq-level aliases of the [_fast] operations,       *)
(* exposed for extraction so the OCaml side can attach a hand-fused           *)
(* hot-path implementation that bypasses the [KCadequeShim] cross-module      *)
(* hop.  At the spec level [kcad8_push_inline = kcad8_push_fast]; the only    *)
(* purpose is to give a Rocq name that the OCaml shim                         *)
(* [KCadeque8Inline.kcad8_push_inline] is the verified counterpart of.        *)
(*                                                                            *)
(* All correctness lemmas (sequence preservation, regularity preservation)    *)
(* are transferred from the [_fast] versions by [reflexivity].                *)
(* ========================================================================== *)

Definition kcad8_push_inline {X : Type} (x : X) (k : KCadeque8 X) : KCadeque8 X :=
  kcad8_push_fast x k.

Definition kcad8_inject_inline {X : Type} (k : KCadeque8 X) (x : X) : KCadeque8 X :=
  kcad8_inject_fast k x.

(** Equivalences by reflexivity. *)
Lemma kcad8_push_inline_eq :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    kcad8_push_inline x k = kcad8_push_fast x k.
Proof. reflexivity. Qed.

Lemma kcad8_inject_inline_eq :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_inject_inline k x = kcad8_inject_fast k x.
Proof. reflexivity. Qed.

(** Sequence preservation transferred from [_fast]. *)
Theorem kcad8_push_inline_seq :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    kcad8_to_list (kcad8_push_inline x k) = x :: kcad8_to_list k.
Proof. apply kcad8_push_fast_seq. Qed.

Theorem kcad8_inject_inline_seq :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    kcad8_to_list (kcad8_inject_inline k x) = kcad8_to_list k ++ [x].
Proof. apply kcad8_inject_fast_seq. Qed.

(** Regularity preservation transferred from [_fast]. *)
Theorem kcad8_push_inline_wf_strong :
  forall (X : Type) (x : X) (k : KCadeque8 X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_push_inline x k).
Proof. apply kcad8_push_fast_wf_strong. Qed.

Theorem kcad8_inject_inline_wf_strong :
  forall (X : Type) (k : KCadeque8 X) (x : X),
    wf_kcad8_strong k -> wf_kcad8_strong (kcad8_inject_inline k x).
Proof. apply kcad8_inject_fast_wf_strong. Qed.
