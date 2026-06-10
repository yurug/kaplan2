(** * KTDeque.Catenable.SeqLemmas — sequence algebra for the op layer.

    The workhorses for the keystone discharge: [root_and_child] and
    [tree_of] are sequence-INVERSE re-bundlings (unconditionally — they only
    move constructors), and the buffer receivers prepend/append under the
    side conditions [J] supplies. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops.

Set Implicit Arguments.

(* ========================================================================== *)
(* Definitional unfoldings (the nested buffer folds, named).                   *)
(* ========================================================================== *)

Lemma cnode_seq_eq :
  forall A k (p s : buffer (stored A)) (mid : list A),
    cnode_seq (Node k p s) mid
    = buf_stored_seq p ++ mid ++ buf_stored_seq s.
Proof. reflexivity. Qed.

Lemma buf_stored_seq_app :
  forall A (a b : buffer (stored A)),
    buf_stored_seq (a ++ b) = buf_stored_seq a ++ buf_stored_seq b.
Proof.
  intros A a b. induction a as [|x r IH]; cbn.
  - reflexivity.
  - unfold buf_stored_seq in IH. rewrite IH. apply app_assoc.
Qed.

(* ========================================================================== *)
(* The re-bundling pair is sequence-neutral.                                   *)
(* ========================================================================== *)

Lemma root_and_child_seq :
  forall A (p : cpacket A) (rest : cchain A),
    cchain_seq (CSingle p rest)
    = cnode_seq (fst (root_and_child p rest))
        (cchain_seq (snd (root_and_child p rest))).
Proof.
  intros A [b n] rest.
  destruct b as [|hn b'|hn b' rc|hn lc b']; cbn; reflexivity.
Qed.

Lemma tree_of_seq :
  forall A (n : cnode A) (child : cchain A),
    cchain_seq (tree_of n child) = cnode_seq n (cchain_seq child).
Proof.
  intros A n child.
  unfold tree_of.
  destruct (node_color (chain_has_node child) n);
    destruct child as [|[cb cn] crest|l r]; cbn; try reflexivity.
  - (* CY, CPair: left side must expose a packet *)
    destruct l as [|[lb ln] lrest|? ?]; cbn; reflexivity.
  - (* CO, CPair: right side must expose a packet *)
    destruct r as [|[rb rn] rrest|? ?]; cbn; reflexivity.
Qed.

Lemma pkt_update_seq :
  forall A (upd : cnode A -> cnode A) (p : cpacket A) (rest : cchain A),
    cchain_seq (pkt_update upd p rest)
    = cnode_seq (upd (fst (root_and_child p rest)))
        (cchain_seq (snd (root_and_child p rest))).
Proof.
  intros A upd p rest.
  unfold pkt_update.
  destruct (root_and_child p rest) as [n child]; cbn.
  apply tree_of_seq.
Qed.

(* ========================================================================== *)
(* Buffer receivers.                                                           *)
(* ========================================================================== *)

(** Pushing prepends, provided the prefix is nonempty OR the node's middle
    content is empty (the childless one-sided-suffix case). *)
Lemma node_push_seq :
  forall A (s : stored A) (k : kind) (p suf : buffer (stored A))
         (mid : list A),
    p <> [] \/ mid = [] ->
    cnode_seq (node_push s (Node k p suf)) mid
    = stored_seq s ++ cnode_seq (Node k p suf) mid.
Proof.
  intros A s k p suf mid Hside.
  destruct p as [|a p'].
  - destruct Hside as [Hp | Hmid]; [congruence | subst mid].
    cbn. reflexivity.
  - cbn. rewrite <- app_assoc. reflexivity.
Qed.

(** Injecting appends, provided the suffix is nonempty OR the middle is
    empty. *)
Lemma node_inject_seq :
  forall A (s : stored A) (k : kind) (p suf : buffer (stored A))
         (mid : list A),
    suf <> [] \/ mid = [] ->
    cnode_seq (node_inject (Node k p suf) s) mid
    = cnode_seq (Node k p suf) mid ++ stored_seq s.
Proof.
  intros A s k p suf mid Hside.
  destruct suf as [|a suf'].
  - destruct Hside as [Hs | Hmid]; [congruence | subst mid].
    cbn [node_inject].
    rewrite !cnode_seq_eq, buf_stored_seq_app.
    cbn. rewrite !app_nil_r. reflexivity.
  - cbn [node_inject].
    rewrite !cnode_seq_eq, buf_stored_seq_app.
    cbn [buf_stored_seq]. rewrite !app_nil_r. rewrite !app_assoc. reflexivity.
Qed.
