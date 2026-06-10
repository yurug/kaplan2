(** * KTDeque.Catenable.WfLemmas — invariant algebra for the op layer.

    The [J]-preservation workhorses, mirroring SeqLemmas: [root_and_child]
    exposes the facts [chain_wf] holds at a packet root, and [tree_of]
    rebuilds a well-formed tree from a (possibly updated) root given the
    per-colour side facts:
    - a RED root needs its child chain's paths green (regularity clause 1);
    - an ORANGE pair root needs its parked LEFT tree green (clause 2);
    - YELLOW and GREEN roots need nothing extra.

    [cont_green] names the continuation side a colour selects, giving the
    top-path-greenness ([chain_ends_green]) of the rebuilt tree. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* What chain_wf yields at a root.                                             *)
(* ========================================================================== *)

Definition root_color_facts {A : Type}
    (n : cnode A) (child : cchain A) : Prop :=
  match node_color (chain_has_node child) n with
  | CG | CY => True
  | CO => match child with CPair l _ => chain_ends_green l | _ => True end
  | CR => chain_ends_green child
  end.

Lemma root_and_child_facts :
  forall A (k : kind) (p : cpacket A) (rest : cchain A),
    chain_wf k (CSingle p rest) ->
    node_kind (fst (root_and_child p rest)) = k /\
    node_sizes (chain_has_node (snd (root_and_child p rest)))
      (fst (root_and_child p rest)) /\
    cnode_wf (fst (root_and_child p rest)) /\
    chain_wf KOnly (snd (root_and_child p rest)) /\
    root_color_facts (fst (root_and_child p rest))
      (snd (root_and_child p rest)).
Proof.
  intros A k [b n] rest Hwf.
  destruct b as [|hn b'|hn b' rc|hn lc b'];
    cbn [chain_wf cbody_wf body_out_kind is_single] in Hwf;
    cbn [root_and_child fst snd].
  - (* BHole: root is the terminal *)
    destruct Hwf as [_ [Hk [Hsz [Hn [Hcol Hrest]]]]].
    split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
    split; [exact Hrest|].
    unfold root_color_facts.
    destruct Hcol as [Hg | [Hr Hgreen]];
      [rewrite Hg; exact I | rewrite Hr; exact Hgreen].
  - (* BSingle: child is a single-packet only chain *)
    destruct Hwf as [[Hk [Hsz [Hn [Hcol Hb']]]]
                     [Hkind [Hnsz [Hnwf [Hncol Hrest]]]]].
    split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
    split.
    + cbn. repeat split; try assumption.
    + unfold root_color_facts. cbn [chain_has_node].
      destruct Hcol as [Hy | Ho]; [rewrite Hy; exact I | rewrite Ho; exact I].
  - (* BPairY: child is a pair (preferred-left continuation, parked right) *)
    destruct Hwf as [[Hk [Hsz [Hn [Hcol [Hrs [Hrc Hb']]]]]]
                     [Hkind [Hnsz [Hnwf [Hncol Hrest]]]]].
    split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
    split.
    + cbn. repeat split; try assumption.
    + unfold root_color_facts. cbn [chain_has_node].
      rewrite Hcol. exact I.
  - (* BPairO: child is a pair (parked green left, preferred-right cont.) *)
    destruct Hwf as [[Hk [Hsz [Hn [Hcol [Hls [Hlc [Hlg Hb']]]]]]]
                     [Hkind [Hnsz [Hnwf [Hncol Hrest]]]]].
    split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
    split.
    + cbn. repeat split; try assumption.
    + unfold root_color_facts. cbn [chain_has_node].
      rewrite Hcol. exact Hlg.
Qed.

(* ========================================================================== *)
(* tree_of rebuilds chain_wf.                                                  *)
(* ========================================================================== *)

Lemma tree_of_wf :
  forall A (k : kind) (n : cnode A) (child : cchain A),
    node_kind n = k ->
    node_sizes (chain_has_node child) n ->
    cnode_wf n ->
    chain_wf KOnly child ->
    root_color_facts n child ->
    chain_wf k (tree_of n child).
Proof.
  intros A k n child Hk Hsz Hn Hchild Hcf.
  unfold root_color_facts in Hcf.
  unfold tree_of.
  destruct child as [|[cb cn] crest|l r];
    cbn [chain_has_node] in Hcf |- *.
  - (* CEmpty child: colour computes to CG *)
    cbn [node_color negb].
    split; [exact I|]. split; [exact Hk|]. split; [exact Hsz|].
    split; [exact Hn|]. split; [left; reflexivity|]. exact I.
  - (* CSingle child *)
    destruct (node_color true n) eqn:Hcol.
    + (* CG *)
      split; [exact I|]. split; [exact Hk|]. split; [exact Hsz|].
      split; [exact Hn|]. split; [left; exact Hcol|]. exact Hchild.
    + (* CY: prepend to the child packet *)
      destruct Hchild as [Hcb [Hck [Hcsz [Hcw [Hccol Hcrest]]]]].
      split.
      { split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
        split; [left; exact Hcol|]. exact Hcb. }
      split; [exact Hck|]. split; [exact Hcsz|]. split; [exact Hcw|].
      split; [exact Hccol|]. exact Hcrest.
    + (* CO: prepend to the child packet (single-child orange) *)
      destruct Hchild as [Hcb [Hck [Hcsz [Hcw [Hccol Hcrest]]]]].
      split.
      { split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
        split; [right; exact Hcol|]. exact Hcb. }
      split; [exact Hck|]. split; [exact Hcsz|]. split; [exact Hcw|].
      split; [exact Hccol|]. exact Hcrest.
    + (* CR *)
      split; [exact I|]. split; [exact Hk|]. split; [exact Hsz|].
      split; [exact Hn|]. split; [right; split; [exact Hcol | exact Hcf]|].
      exact Hchild.
  - (* CPair child *)
    destruct (node_color true n) eqn:Hcol.
    + (* CG *)
      split; [exact I|]. split; [exact Hk|]. split; [exact Hsz|].
      split; [exact Hn|]. split; [left; exact Hcol|]. exact Hchild.
    + (* CY: inline the left single *)
      destruct Hchild as [Hls [Hrs [Hl Hr]]].
      destruct l as [|[lb ln] lrest|? ?]; cbn in Hls; try congruence.
      destruct Hl as [Hlb [Hlk [Hlsz [Hlw [Hlcol Hlrest]]]]].
      split.
      { split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
        split; [exact Hcol|]. split; [exact Hrs|]. split; [exact Hr|].
        exact Hlb. }
      split; [exact Hlk|]. split; [exact Hlsz|]. split; [exact Hlw|].
      split; [exact Hlcol|]. exact Hlrest.
    + (* CO: inline the right single; park the (green) left *)
      destruct Hchild as [Hls [Hrs [Hl Hr]]].
      destruct r as [|[rb rn] rrest|? ?]; cbn in Hrs; try congruence.
      destruct Hr as [Hrb [Hrk [Hrsz [Hrw [Hrcol Hrrest]]]]].
      split.
      { split; [exact Hk|]. split; [exact Hsz|]. split; [exact Hn|].
        split; [exact Hcol|]. split; [exact Hls|]. split; [exact Hl|].
        split; [exact Hcf|]. exact Hrb. }
      split; [exact Hrk|]. split; [exact Hrsz|]. split; [exact Hrw|].
      split; [exact Hrcol|]. exact Hrrest.
    + (* CR *)
      split; [exact I|]. split; [exact Hk|]. split; [exact Hsz|].
      split; [exact Hn|]. split; [right; split; [exact Hcol | exact Hcf]|].
      exact Hchild.
Qed.

(* ========================================================================== *)
(* tree_of's top path is green when the selected continuation is.              *)
(* ========================================================================== *)

(** The continuation side a colour selects: green/red terminate the path at
    the node itself; yellow continues left/only; orange right/only. *)
Definition cont_green {A : Type} (g : gyor) (child : cchain A) : Prop :=
  match g with
  | CG => True
  | CY =>
      match child with
      | CSingle _ _ => chain_ends_green child
      | CPair l _ => chain_ends_green l
      | CEmpty => True
      end
  | CO =>
      match child with
      | CSingle _ _ => chain_ends_green child
      | CPair _ r => chain_ends_green r
      | CEmpty => True
      end
  | CR => False
  end.

Lemma tree_of_ends_green :
  forall A (n : cnode A) (child : cchain A),
    chain_wf KOnly child ->
    cont_green (node_color (chain_has_node child) n) child ->
    chain_ends_green (tree_of n child).
Proof.
  intros A n child Hchild Hcg.
  unfold cont_green in Hcg.
  unfold tree_of.
  destruct child as [|[cb cn] crest|l r];
    cbn [chain_has_node] in Hcg |- *.
  - cbn [node_color negb]. reflexivity.
  - destruct (node_color true n) eqn:Hcol.
    + exact Hcol.
    + exact Hcg.
    + exact Hcg.
    + contradiction.
  - destruct (node_color true n) eqn:Hcol.
    + exact Hcol.
    + (* CY: the left single's terminal *)
      destruct Hchild as [Hls [Hrs [Hl Hr]]].
      destruct l as [|[lb ln] lrest|? ?].
      * cbn in Hls. congruence.
      * exact Hcg.
      * cbn in Hls. congruence.
    + (* CO: the right single's terminal *)
      destruct Hchild as [Hls [Hrs [Hl Hr]]].
      destruct r as [|[rb rn] rrest|? ?].
      * cbn in Hrs. congruence.
      * exact Hcg.
      * cbn in Hrs. congruence.
    + contradiction.
Qed.

(* ========================================================================== *)
(* Receiver fact preservation + colour monotonicity (push/inject assembly).    *)
(* ========================================================================== *)

Definition gyor_rank (g : gyor) : nat :=
  match g with CR => 0 | CO => 1 | CY => 2 | CG => 3 end.

(** The §6.1 colour ladder as a function of the measure. *)
Definition gyor_of (m : nat) : gyor :=
  if 8 <=? m then CG else if m =? 7 then CY else if m =? 6 then CO else CR.

Lemma gyor_of_mono :
  forall a b, a <= b -> gyor_rank (gyor_of a) <= gyor_rank (gyor_of b).
Proof.
  intros a b Hab. unfold gyor_of.
  destruct (8 <=? b) eqn:Hb8.
  - destruct (8 <=? a); [cbn; lia|].
    destruct (a =? 7); [cbn; lia|]. destruct (a =? 6); cbn; lia.
  - apply Nat.leb_gt in Hb8.
    destruct (8 <=? a) eqn:Ha8;
      [apply Nat.leb_le in Ha8; lia |].
    destruct (b =? 7) eqn:Hb7.
    + destruct (a =? 7); [cbn; lia|]. destruct (a =? 6); cbn; lia.
    + apply Nat.eqb_neq in Hb7.
      destruct (a =? 7) eqn:Ha7.
      * apply Nat.eqb_eq in Ha7.
        destruct (b =? 6) eqn:Hb6;
          [cbn; apply Nat.eqb_eq in Hb6; lia | apply Nat.eqb_neq in Hb6; lia].
      * destruct (a =? 6) eqn:Ha6.
        -- apply Nat.eqb_eq in Ha6.
           destruct (b =? 6) eqn:Hb6; [cbn; lia |].
           apply Nat.eqb_neq in Hb6. lia.
        -- destruct (b =? 6); cbn; lia.
Qed.

Definition node_measure {A : Type} (n : cnode A) : nat :=
  match n with
  | Node KOnly p s => Nat.min (length p) (length s)
  | Node KLeft p _ => length p
  | Node KRight _ s => length s
  end.

Lemma node_color_measure :
  forall A (n : cnode A),
    node_color true n = gyor_of (node_measure n).
Proof. intros A [k p s]; destruct k; reflexivity. Qed.

Lemma node_push_measure :
  forall A (s : stored A) (n : cnode A),
    node_measure n <= node_measure (node_push s n).
Proof.
  intros A s [k p suf]; destruct k; destruct p;
    cbn [node_push node_measure length]; lia.
Qed.

Lemma node_inject_measure :
  forall A (s : stored A) (n : cnode A),
    node_measure n <= node_measure (node_inject n s).
Proof.
  intros A s [k p suf]; destruct k; destruct suf;
    cbn [node_inject node_measure];
    rewrite ?length_app; cbn [length]; lia.
Qed.

Lemma node_push_color_mono :
  forall A (s : stored A) (n : cnode A),
    gyor_rank (node_color true n)
    <= gyor_rank (node_color true (node_push s n)).
Proof.
  intros A s n. rewrite !node_color_measure.
  apply gyor_of_mono, node_push_measure.
Qed.

Lemma node_inject_color_mono :
  forall A (s : stored A) (n : cnode A),
    gyor_rank (node_color true n)
    <= gyor_rank (node_color true (node_inject n s)).
Proof.
  intros A s n. rewrite !node_color_measure.
  apply gyor_of_mono, node_inject_measure.
Qed.

Lemma node_push_kind :
  forall A (s : stored A) (n : cnode A),
    node_kind (node_push s n) = node_kind n.
Proof. intros A s [k p suf]; destruct p; reflexivity. Qed.

Lemma node_inject_kind :
  forall A (s : stored A) (n : cnode A),
    node_kind (node_inject n s) = node_kind n.
Proof. intros A s [k p suf]; destruct suf; reflexivity. Qed.

Lemma node_push_sizes :
  forall A (s : stored A) (hc : bool) (k : kind)
         (p suf : buffer (stored A)),
    k <> KRight ->
    node_sizes hc (Node k p suf) ->
    node_sizes hc (node_push s (Node k p suf)).
Proof.
  intros A s hc k p suf Hk Hsz.
  destruct k; [| | congruence]; destruct p as [|a p']; cbn in Hsz |- *.
  - (* KOnly, empty prefix: childless one-sided suffix *)
    destruct Hsz as [[Hp _] | [Hc Hone]]; [cbn in Hp; lia |].
    right. split; [exact Hc|].
    destruct Hone as [[_ Hs] | [Hs _]];
      [left; split; [reflexivity | cbn; lia] | left; split; [reflexivity |]].
    subst suf. cbn. lia.
  - (* KOnly, nonempty prefix *)
    destruct Hsz as [[Hp Hs] | [Hc Hone]].
    + left. split; [cbn in Hp |- *; lia | exact Hs].
    + destruct Hone as [[Hp _] | [Hs Hp]]; [congruence |].
      right. split; [exact Hc|]. right. split; [exact Hs | cbn in Hp |- *; lia].
  - (* KLeft, empty prefix: sizes impossible *)
    destruct Hsz as [Hp _]. cbn in Hp. lia.
  - (* KLeft, nonempty prefix *)
    destruct Hsz as [Hp Hs2]. split; [cbn in Hp |- *; lia | exact Hs2].
Qed.

Lemma node_inject_sizes :
  forall A (s : stored A) (hc : bool) (k : kind)
         (p suf : buffer (stored A)),
    k <> KLeft ->
    node_sizes hc (Node k p suf) ->
    node_sizes hc (node_inject (Node k p suf) s).
Proof.
  intros A s hc k p suf Hk Hsz.
  destruct k; [| congruence |]; destruct suf as [|a suf']; cbn in Hsz |- *.
  - (* KOnly, empty suffix: childless one-sided prefix *)
    destruct Hsz as [[_ Hs] | [Hc Hone]]; [cbn in Hs; lia |].
    right. split; [exact Hc|].
    destruct Hone as [[_ Hs1] | [_ Hp]]; [cbn in Hs1; lia |].
    right. split; [reflexivity | rewrite length_app; cbn; lia].
  - (* KOnly, nonempty suffix *)
    destruct Hsz as [[Hp Hs] | [Hc Hone]].
    + left. split; [exact Hp | cbn in Hs |- *; rewrite length_app; cbn; lia].
    + destruct Hone as [[Hp Hs] | [Hs _]]; [| congruence].
      right. split; [exact Hc|]. left.
      split; [exact Hp | cbn in Hs |- *; rewrite length_app; cbn; lia].
  - (* KRight, empty suffix: sizes impossible *)
    destruct Hsz as [_ Hs]. cbn in Hs. lia.
  - (* KRight, nonempty suffix *)
    destruct Hsz as [Hp2 Hs]. split;
      [exact Hp2 | cbn in Hs |- *; rewrite length_app; cbn; lia].
Qed.

(** Stored-wf of buffers, for the receiver cnode_wf preservation. *)
Lemma node_push_cnode_wf :
  forall A (s : stored A) (n : cnode A),
    stored_wf s -> cnode_wf n -> cnode_wf (node_push s n).
Proof.
  intros A s [k p suf] Hs Hn.
  destruct p; cbn in Hn |- *;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; assumption.
Qed.

Lemma buf_all_stored_wf_app :
  forall A (a b : buffer (stored A)),
    (fix all (l : list (stored A)) : Prop :=
       match l with [] => True | x :: r => stored_wf x /\ all r end) a ->
    (fix all (l : list (stored A)) : Prop :=
       match l with [] => True | x :: r => stored_wf x /\ all r end) b ->
    (fix all (l : list (stored A)) : Prop :=
       match l with [] => True | x :: r => stored_wf x /\ all r end) (a ++ b).
Proof.
  intros A a b Ha Hb. induction a as [|x r IH]; cbn in *.
  - exact Hb.
  - destruct Ha as [Hx Hr]. split; [exact Hx | exact (IH Hr)].
Qed.

Lemma node_inject_cnode_wf :
  forall A (s : stored A) (n : cnode A),
    stored_wf s -> cnode_wf n -> cnode_wf (node_inject n s).
Proof.
  intros A s [k p suf] Hs Hn.
  destruct Hn as [Hp Hsf].
  destruct suf as [|a suf'].
  - split.
    + apply buf_all_stored_wf_app; [exact Hp | cbn; tauto].
    + exact I.
  - split; [exact Hp |].
    apply buf_all_stored_wf_app; [exact Hsf | cbn; tauto].
Qed.

(** tree_of always yields a single-packet chain (needed for CPair shapes). *)
Lemma tree_of_is_single :
  forall A (n : cnode A) (child : cchain A),
    is_single (tree_of n child) = true.
Proof.
  intros A n child. unfold tree_of.
  destruct (node_color (chain_has_node child) n);
    destruct child as [|[cb cn] crest|l r]; cbn; try reflexivity.
  - destruct l as [|[lb ln] lrest|? ?]; reflexivity.
  - destruct r as [|[rb rn] rrest|? ?]; reflexivity.
Qed.

Lemma pkt_update_is_single :
  forall A (upd : cnode A -> cnode A) (p : cpacket A) (rest : cchain A),
    is_single (pkt_update upd p rest) = true.
Proof.
  intros A upd p rest. unfold pkt_update.
  destruct (root_and_child p rest) as [n child]. apply tree_of_is_single.
Qed.

(* ========================================================================== *)
(* The central assembly: pkt_update preserves chain_wf + chain_ends_green.     *)
(* Generic over the updater; the caller supplies kind/sizes/wf preservation    *)
(* and colour monotonicity (push and inject both qualify).                     *)
(* ========================================================================== *)

Lemma pkt_update_preserves :
  forall A (upd : cnode A -> cnode A) (k : kind)
         (p : cpacket A) (rest : cchain A),
    (forall n0, node_kind (upd n0) = node_kind n0) ->
    (forall hc pp ss,
        node_sizes hc (Node k pp ss) -> node_sizes hc (upd (Node k pp ss))) ->
    (forall n0, cnode_wf n0 -> cnode_wf (upd n0)) ->
    (forall n0,
        gyor_rank (node_color true n0)
        <= gyor_rank (node_color true (upd n0))) ->
    chain_wf k (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    chain_wf k (pkt_update upd p rest) /\
    chain_ends_green (pkt_update upd p rest).
Proof.
  intros A upd k p rest Hupk Hupsz Hupwf Hupmono Hwf Hgreen.
  pose proof (root_and_child_facts Hwf) as [Hk [Hsz [Hn [Hchild Hcf]]]].
  unfold pkt_update.
  destruct p as [b n0].
  destruct b as [|hn b'|hn b' rc|hn lc b'];
    cbn [root_and_child fst snd] in Hk, Hsz, Hn, Hchild, Hcf |- *;
    cbn [chain_wf cbody_wf body_out_kind is_single] in Hwf;
    cbn [chain_ends_green] in Hgreen.
  - (* BHole: the root is the (green, by ends_green) terminal *)
    destruct n0 as [k0 pp ss]. cbn [node_kind] in Hk. subst k0.
    destruct rest as [|rp rrest|rl rr].
    + (* CEmpty child: colour stays CG definitionally *)
      split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact I
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite node_color_no_child; exact I].
      * apply tree_of_ends_green; [exact I |].
        cbn [chain_has_node]. rewrite node_color_no_child. exact I.
    + (* CSingle child *)
      cbn [chain_has_node] in Hsz, Hgreen |- *.
      destruct (node_color true (upd (Node k pp ss))) eqn:Hnew.
      * split.
        -- apply tree_of_wf;
             [rewrite Hupk; reflexivity
             | apply Hupsz; exact Hsz
             | apply Hupwf; exact Hn
             | exact Hchild
             | unfold root_color_facts; cbn [chain_has_node];
               rewrite Hnew; exact I].
        -- apply tree_of_ends_green; [exact Hchild |].
           cbn [chain_has_node]. rewrite Hnew. exact I.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
    + (* CPair child *)
      cbn [chain_has_node] in Hsz, Hgreen |- *.
      destruct (node_color true (upd (Node k pp ss))) eqn:Hnew.
      * split.
        -- apply tree_of_wf;
             [rewrite Hupk; reflexivity
             | apply Hupsz; exact Hsz
             | apply Hupwf; exact Hn
             | exact Hchild
             | unfold root_color_facts; cbn [chain_has_node];
               rewrite Hnew; exact I].
        -- apply tree_of_ends_green; [exact Hchild |].
           cbn [chain_has_node]. rewrite Hnew. exact I.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
      * pose proof (Hupmono (Node k pp ss)) as Hm.
        rewrite Hgreen, Hnew in Hm. cbn in Hm. lia.
  - (* BSingle head: old colour CY or CO; child is the single-packet chain *)
    destruct Hwf as [[HkS [HszS [HnS [HcolS Hb']]]] _].
    destruct hn as [k0 pp ss]. cbn [node_kind] in HkS. subst k0.
    cbn [chain_has_node] in Hsz |- *.
    destruct (node_color true (upd (Node k pp ss))) eqn:Hnew.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact I.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact Hgreen.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact Hgreen.
    + pose proof (Hupmono (Node k pp ss)) as Hm.
      destruct HcolS as [Hc | Hc]; rewrite Hc, Hnew in Hm; cbn in Hm; lia.
  - (* BPairY head: old colour CY *)
    destruct Hwf as [[HkS [HszS [HnS [HcolS [Hrs [Hrc Hb']]]]]] _].
    destruct hn as [k0 pp ss]. cbn [node_kind] in HkS. subst k0.
    cbn [chain_has_node] in Hsz |- *.
    destruct (node_color true (upd (Node k pp ss))) eqn:Hnew.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact I.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact Hgreen.
    + pose proof (Hupmono (Node k pp ss)) as Hm.
      rewrite HcolS, Hnew in Hm. cbn in Hm. lia.
    + pose proof (Hupmono (Node k pp ss)) as Hm.
      rewrite HcolS, Hnew in Hm. cbn in Hm. lia.
  - (* BPairO head: old colour CO; parked left is a green-path tree *)
    destruct Hwf as [[HkS [HszS [HnS [HcolS [Hls [Hlc [Hlg Hb']]]]]]] _].
    destruct hn as [k0 pp ss]. cbn [node_kind] in HkS. subst k0.
    cbn [chain_has_node] in Hsz |- *.
    destruct (node_color true (upd (Node k pp ss))) eqn:Hnew.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact I.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact Hlg.
    + split.
      * apply tree_of_wf;
          [rewrite Hupk; reflexivity
          | apply Hupsz; exact Hsz
          | apply Hupwf; exact Hn
          | exact Hchild
          | unfold root_color_facts; cbn [chain_has_node];
            rewrite Hnew; exact Hlg].
      * apply tree_of_ends_green; [exact Hchild |].
        cbn [chain_has_node]. rewrite Hnew. exact Hgreen.
    + pose proof (Hupmono (Node k pp ss)) as Hm.
      rewrite HcolS, Hnew in Hm. cbn in Hm. lia.
Qed.

(* ========================================================================== *)
(* Chain-level preservation and the public push/inject J facts.                *)
(* ========================================================================== *)

Lemma push_chain_preserves :
  forall A (s : stored A) (c : cchain A) (k : kind),
    k <> KRight ->
    (c = CEmpty -> k = KOnly) ->
    stored_wf s ->
    chain_wf k c ->
    chain_ends_green c ->
    chain_wf k (push_chain s c) /\ chain_ends_green (push_chain s c).
Proof.
  intros A s c.
  induction c as [| p rest _ | l IHl r _]; intros k Hk Hke Hs Hwf Hg.
  - (* CEmpty: the singleton *)
    rewrite (Hke eq_refl). cbn [push_chain].
    split.
    + split; [exact I|]. split; [reflexivity|].
      split.
      * right. split; [reflexivity|]. right.
        split; [reflexivity | cbn; lia].
      * split; [cbn; tauto|]. split; [left; reflexivity | exact I].
    + reflexivity.
  - (* CSingle: the packet update *)
    cbn [push_chain].
    apply pkt_update_preserves; try assumption.
    + intros n0. apply node_push_kind.
    + intros hc pp ss. apply node_push_sizes. exact Hk.
    + intros n0. apply node_push_cnode_wf. exact Hs.
    + intros n0. apply node_push_color_mono.
  - (* CPair: descend left *)
    cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    destruct (IHl KLeft) as [Hwf' Hg'];
      [congruence
      | intros Heq; subst l; cbn in Hls; congruence
      | exact Hs | exact Hl | exact Hgl |].
    cbn [push_chain]. split.
    + cbn [chain_wf].
      split.
      * destruct l as [|lp lrest|? ?]; cbn in Hls; try congruence.
        cbn [push_chain]. apply pkt_update_is_single.
      * split; [exact Hrs|]. split; [exact Hwf' | exact Hr].
    + cbn [chain_ends_green]. split; [exact Hg' | exact Hgr].
Qed.

Lemma inject_chain_preserves :
  forall A (s : stored A) (c : cchain A) (k : kind),
    k <> KLeft ->
    (c = CEmpty -> k = KOnly) ->
    stored_wf s ->
    chain_wf k c ->
    chain_ends_green c ->
    chain_wf k (inject_chain c s) /\ chain_ends_green (inject_chain c s).
Proof.
  intros A s c.
  induction c as [| p rest _ | l _ r IHr]; intros k Hk Hke Hs Hwf Hg.
  - rewrite (Hke eq_refl). cbn [inject_chain].
    split.
    + split; [exact I|]. split; [reflexivity|].
      split.
      * right. split; [reflexivity|]. left.
        split; [reflexivity | cbn; lia].
      * split; [cbn; tauto|]. split; [left; reflexivity | exact I].
    + reflexivity.
  - cbn [inject_chain].
    apply pkt_update_preserves; try assumption.
    + intros n0. apply node_inject_kind.
    + intros hc pp ss Hszs. apply node_inject_sizes; [exact Hk | exact Hszs].
    + intros n0. apply node_inject_cnode_wf. exact Hs.
    + intros n0. apply node_inject_color_mono.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    destruct (IHr KRight) as [Hwf' Hg'];
      [congruence
      | intros Heq; subst r; cbn in Hrs; congruence
      | exact Hs | exact Hr | exact Hgr |].
    cbn [inject_chain]. split.
    + cbn [chain_wf].
      split; [exact Hls|].
      split.
      * destruct r as [|rp rrest|? ?]; cbn in Hrs; try congruence.
        cbn [inject_chain]. apply pkt_update_is_single.
      * split; [exact Hl | exact Hwf'].
    + cbn [chain_ends_green]. split; [exact Hgl | exact Hg'].
Qed.
