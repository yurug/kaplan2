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

(* ========================================================================== *)
(* Op-level sequence lemmas (under [chain_wf]).                                *)
(* ========================================================================== *)

Definition node_prefix {A : Type} (n : cnode A) : buffer (stored A) :=
  match n with Node _ p _ => p end.

Definition node_suffix {A : Type} (n : cnode A) : buffer (stored A) :=
  match n with Node _ _ s => s end.

Lemma nonnil_of_length :
  forall (X : Type) (n : nat) (l : list X), S n <= length l -> l <> [].
Proof. intros X n [|x r] H; [cbn in H; lia | congruence]. Qed.

(** [chain_wf] guarantees the push side condition at the root: the receiving
    prefix is nonempty, or the root is the childless one-sided-suffix only
    node (whose child — and hence middle content — is empty). *)
Lemma chain_wf_root_prefix :
  forall A (k : kind) (p : cpacket A) (rest : cchain A),
    chain_wf k (CSingle p rest) ->
    node_prefix (fst (root_and_child p rest)) <> [] \/
    snd (root_and_child p rest) = CEmpty.
Proof.
  intros A k [b n] rest Hwf.
  destruct b as [|hn b'|hn b' rc|hn lc b']; cbn in Hwf |- *.
  - (* BHole: root = terminal node *)
    destruct Hwf as [_ [_ [Hsz _]]].
    destruct n as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[Hp _] | [Hchild Hone]].
      * left. cbn. eapply nonnil_of_length; eauto.
      * destruct Hone as [[Hp _] | [_ Hp]].
        -- right. destruct rest; cbn in Hchild; congruence.
        -- left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn.
      destruct pp; [cbn in Hp; congruence | congruence].
  - (* BSingle *)
    destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[Hp _] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn.
      destruct pp; [cbn in Hp; congruence | congruence].
  - (* BPairY *)
    destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[Hp _] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn.
      destruct pp; [cbn in Hp; congruence | congruence].
  - (* BPairO *)
    destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[Hp _] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [Hp _]. left. cbn.
      destruct pp; [cbn in Hp; congruence | congruence].
Qed.

(** Mirror: the inject side condition at the root. *)
Lemma chain_wf_root_suffix :
  forall A (k : kind) (p : cpacket A) (rest : cchain A),
    chain_wf k (CSingle p rest) ->
    node_suffix (fst (root_and_child p rest)) <> [] \/
    snd (root_and_child p rest) = CEmpty.
Proof.
  intros A k [b n] rest Hwf.
  destruct b as [|hn b'|hn b' rc|hn lc b']; cbn in Hwf |- *.
  - destruct Hwf as [_ [_ [Hsz _]]].
    destruct n as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[_ Hs] | [Hchild Hone]].
      * left. cbn. eapply nonnil_of_length; eauto.
      * destruct Hone as [[_ Hs] | [Hs _]].
        -- left. cbn. eapply nonnil_of_length; eauto.
        -- right. destruct rest; cbn in Hchild; congruence.
    + destruct Hsz as [_ Hs]. left. cbn.
      destruct ss; [cbn in Hs; congruence | congruence].
    + destruct Hsz as [_ Hs]. left. cbn. eapply nonnil_of_length; eauto.
  - destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[_ Hs] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [_ Hs]. left. cbn.
      destruct ss; [cbn in Hs; congruence | congruence].
    + destruct Hsz as [_ Hs]. left. cbn. eapply nonnil_of_length; eauto.
  - destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[_ Hs] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [_ Hs]. left. cbn.
      destruct ss; [cbn in Hs; congruence | congruence].
    + destruct Hsz as [_ Hs]. left. cbn. eapply nonnil_of_length; eauto.
  - destruct Hwf as [[_ [Hsz _]] _].
    destruct hn as [k0 pp ss]; destruct k0; cbn in Hsz.
    + destruct Hsz as [[_ Hs] | [Hfalse _]]; [| congruence].
      left. cbn. eapply nonnil_of_length; eauto.
    + destruct Hsz as [_ Hs]. left. cbn.
      destruct ss; [cbn in Hs; congruence | congruence].
    + destruct Hsz as [_ Hs]. left. cbn. eapply nonnil_of_length; eauto.
Qed.

Lemma push_chain_seq :
  forall A (s : stored A) (c : cchain A) (k : kind),
    chain_wf k c ->
    cchain_seq (push_chain s c) = stored_seq s ++ cchain_seq c.
Proof.
  intros A s c.
  induction c as [| p rest _ | l IHl r _]; intros k Hwf.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [push_chain].
    rewrite pkt_update_seq.
    rewrite (root_and_child_seq p rest).
    pose proof (@chain_wf_root_prefix A k p rest Hwf) as Hside.
    destruct (root_and_child p rest) as [n child]; cbn in Hside |- *.
    destruct n as [k0 pp ss].
    apply node_push_seq.
    destruct Hside as [Hp | Hc]; [left; exact Hp | right; subst child].
    reflexivity.
  - cbn in Hwf. destruct Hwf as [_ [_ [Hl _]]].
    cbn [push_chain]. cbn [cchain_seq].
    rewrite (IHl KLeft Hl). rewrite <- app_assoc. reflexivity.
Qed.

Lemma inject_chain_seq :
  forall A (s : stored A) (c : cchain A) (k : kind),
    chain_wf k c ->
    cchain_seq (inject_chain c s) = cchain_seq c ++ stored_seq s.
Proof.
  intros A s c.
  induction c as [| p rest _ | l _ r IHr]; intros k Hwf.
  - cbn. rewrite !app_nil_r. reflexivity.
  - cbn [inject_chain].
    rewrite pkt_update_seq.
    rewrite (root_and_child_seq p rest).
    pose proof (@chain_wf_root_suffix A k p rest Hwf) as Hside.
    destruct (root_and_child p rest) as [n child]; cbn in Hside |- *.
    destruct n as [k0 pp ss].
    apply node_inject_seq.
    destruct Hside as [Hs | Hc]; [left; exact Hs | right; subst child].
    reflexivity.
  - cbn in Hwf. destruct Hwf as [_ [_ [_ Hr]]].
    cbn [inject_chain]. cbn [cchain_seq].
    rewrite (IHr KRight Hr). rewrite app_assoc. reflexivity.
Qed.
