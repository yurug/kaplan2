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
