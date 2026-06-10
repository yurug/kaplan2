(** * KTDeque.Catenable.SRLemmas — semiregular concat (Lemma 6.2's weak half).

    Piece (A) of the pop/eject campaign: [cad_concat] on SEMIREGULAR
    (chain_wf, no ends_green) inputs is total and semiregular.  Repair feeds
    it possibly-red-topped chains (a popped SBig's child, a pop remainder),
    and its result lands under a green or red-claused root, so no greenness
    is concluded.  Levels are covered by the colour-blind *_leveled twins in
    ConcatLemmas, unchanged.

    The colour bundles collapse (SESSION_STATE, SR-CONCAT SIMPLIFICATION):
    tree_of_wf only demands facts at new-CO-pair and new-CR; builder
    colour-mono pins old in {CO,CR} there; and the old root's facts in
    exactly that shape are [root_color_facts] — the 5th component of
    [root_and_child_facts], proven from [chain_wf] alone. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas
  ConcatLemmas PopLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* The keyed SR bundle: root_color_facts' body, parameterised by colour.       *)
(* ========================================================================== *)

Definition sr_facts {A : Type} (g : gyor) (child : cchain A) : Prop :=
  match g with
  | CG | CY => True
  | CO => match child with CPair l _ => chain_ends_green l | _ => True end
  | CR => chain_ends_green child
  end.

Lemma root_color_facts_sr :
  forall A (n : cnode A) (child : cchain A),
    root_color_facts n child ->
    sr_facts (node_color (chain_has_node child) n) child.
Proof.
  intros A n child H. unfold root_color_facts in H.
  destruct (node_color (chain_has_node child) n); exact H.
Qed.

Lemma sr_facts_mono :
  forall A (g g' : gyor) (d : cchain A),
    gyor_rank g <= gyor_rank g' ->
    sr_facts g d -> sr_facts g' d.
Proof.
  intros A g g' d Hle Hf.
  destruct g.
  - destruct g'; cbn [gyor_rank] in Hle; try lia. exact I.
  - destruct g'; cbn [gyor_rank] in Hle; try lia; exact I.
  - destruct g'; cbn [gyor_rank] in Hle; try lia; try exact I.
    exact Hf.
  - destruct g'; cbn [sr_facts] in Hf |- *; try exact I.
    + destruct d as [|? ?|l r]; try exact I.
      cbn [chain_ends_green] in Hf. destruct Hf as [Hl _]. exact Hl.
    + exact Hf.
Qed.

Lemma is_single_has_node :
  forall A (c : cchain A), is_single c = true -> chain_has_node c = true.
Proof. intros A [|? ?|? ?] H; cbn in *; congruence. Qed.

(* ========================================================================== *)
(* SR rebuild cores: one colour dispatch each; CR threads the full ends      *)
(* through the strong whole-chain preserve, CO uses the pair's left.          *)
(* ========================================================================== *)

Lemma left_rebuild_sr :
  forall A (p1 : buffer (stored A)) (y z : stored A)
         (cell : stored A) (d1 : cchain A),
    5 <= length p1 -> buf_stored_all_wf p1 ->
    stored_wf y -> stored_wf z -> stored_wf cell ->
    chain_wf KOnly d1 -> d1 <> CEmpty ->
    sr_facts (gyor_of (length p1)) d1 ->
    chain_wf KLeft
      (tree_of (Node KLeft p1 [y; z]) (inject_chain d1 cell)) /\
    cchain_seq (tree_of (Node KLeft p1 [y; z]) (inject_chain d1 cell))
    = buf_stored_seq p1 ++ cchain_seq d1 ++ stored_seq cell
      ++ stored_seq y ++ stored_seq z.
Proof.
  intros A p1 y z cell d1 Hp5 Hpw Hyw Hzw Hcw Hd1 Hne Hsr.
  assert (Hwf' : chain_wf KOnly (inject_chain d1 cell)).
  { apply (@inject_chain_preserves_wf A cell d1 KOnly);
      [congruence
      | intros Heq; exfalso; apply Hne; exact Heq
      | exact Hcw | exact Hd1]. }
  assert (Hseq' : cchain_seq (inject_chain d1 cell)
                  = cchain_seq d1 ++ stored_seq cell)
    by (rewrite (inject_chain_seq cell Hd1); reflexivity).
  assert (Hhc : chain_has_node (inject_chain d1 cell) = true).
  { destruct d1 as [|? ?|? ?]; [congruence | | reflexivity].
    cbn [inject_chain].
    apply is_single_has_node, pkt_update_is_single. }
  assert (Hnewc : node_color
            (chain_has_node (inject_chain d1 cell))
            (Node KLeft p1 [y; z]) = gyor_of (length p1))
    by (rewrite Hhc, node_color_measure; reflexivity).
  assert (Hrcf : root_color_facts (Node KLeft p1 [y; z])
                   (inject_chain d1 cell)).
  { unfold root_color_facts. rewrite Hnewc.
    destruct (gyor_of (length p1)) eqn:Hg.
    - exact I.
    - exact I.
    - (* CO: the pair's left is untouched by the rightward inject *)
      destruct d1 as [|d1p d1r|d1l d1r]; [congruence | |].
      + pose proof (@pkt_update_is_single A
                      (fun n => node_inject n cell) d1p d1r) as Hs.
        cbn [inject_chain].
        destruct (pkt_update (fun n => node_inject n cell) d1p d1r);
          cbn in Hs; try congruence.
        exact I.
      + cbn [inject_chain]. cbn [sr_facts] in Hsr. exact Hsr.
    - (* CR: full ends via the strong preserve *)
      cbn [sr_facts] in Hsr.
      destruct (@inject_chain_preserves A cell d1 KOnly
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hne; exact Heq)
                  Hcw Hd1 Hsr) as [_ Hge'].
      exact Hge'. }
  split.
  - apply tree_of_wf;
      [reflexivity
      | rewrite Hhc; cbn [node_sizes]; split; [lia | reflexivity]
      | split; [exact Hpw | cbn; repeat split; assumption]
      | exact Hwf'
      | exact Hrcf].
  - rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
Qed.

Lemma right_rebuild_sr :
  forall A (s2 : buffer (stored A)) (x y : stored A)
         (cell : stored A) (d2 : cchain A),
    5 <= length s2 -> buf_stored_all_wf s2 ->
    stored_wf x -> stored_wf y -> stored_wf cell ->
    chain_wf KOnly d2 -> d2 <> CEmpty ->
    sr_facts (gyor_of (length s2)) d2 ->
    chain_wf KRight
      (tree_of (Node KRight [x; y] s2) (push_chain cell d2)) /\
    cchain_seq (tree_of (Node KRight [x; y] s2) (push_chain cell d2))
    = stored_seq x ++ stored_seq y ++ stored_seq cell
      ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A s2 x y cell d2 Hs5 Hsw Hxw Hyw Hcw Hd2 Hne Hsr.
  assert (Hwf' : chain_wf KOnly (push_chain cell d2)).
  { apply (@push_chain_preserves_wf A cell d2 KOnly);
      [congruence
      | intros Heq; exfalso; apply Hne; exact Heq
      | exact Hcw | exact Hd2]. }
  assert (Hseq' : cchain_seq (push_chain cell d2)
                  = stored_seq cell ++ cchain_seq d2)
    by (rewrite (push_chain_seq cell Hd2); reflexivity).
  assert (Hhc : chain_has_node (push_chain cell d2) = true).
  { destruct d2 as [|? ?|? ?]; [congruence | | reflexivity].
    cbn [push_chain].
    apply is_single_has_node, pkt_update_is_single. }
  assert (Hnewc : node_color
            (chain_has_node (push_chain cell d2))
            (Node KRight [x; y] s2) = gyor_of (length s2))
    by (rewrite Hhc, node_color_measure; reflexivity).
  assert (Hrcf : root_color_facts (Node KRight [x; y] s2)
                   (push_chain cell d2)).
  { unfold root_color_facts. rewrite Hnewc.
    destruct (gyor_of (length s2)) eqn:Hg.
    - exact I.
    - exact I.
    - (* CO: the push went LEFT — its greenness must be restored by the
         strong preserve from the parked clause *)
      destruct d2 as [|d2p d2r|d2l d2r]; [congruence | |].
      + pose proof (@pkt_update_is_single A (node_push cell) d2p d2r)
          as Hs.
        cbn [push_chain].
        destruct (pkt_update (node_push cell) d2p d2r);
          cbn in Hs; try congruence.
        exact I.
      + cbn [push_chain].
        pose proof Hd2 as Hd2'. cbn [chain_wf] in Hd2'.
        destruct Hd2' as [Hls [_ [Hl _]]].
        assert (Hlne : d2l <> CEmpty)
          by (destruct d2l; cbn in Hls; congruence).
        cbn [sr_facts] in Hsr.
        destruct (@push_chain_preserves A cell d2l KLeft
                    ltac:(congruence)
                    ltac:(intros Heq; exfalso; apply Hlne; exact Heq)
                    Hcw Hl Hsr) as [_ Hgl'].
        exact Hgl'.
    - (* CR: full ends via the strong preserve *)
      cbn [sr_facts] in Hsr.
      destruct (@push_chain_preserves A cell d2 KOnly
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hne; exact Heq)
                  Hcw Hd2 Hsr) as [_ Hge'].
      exact Hge'. }
  split.
  - apply tree_of_wf;
      [reflexivity
      | rewrite Hhc; cbn [node_sizes]; split; [reflexivity | lia]
      | split; [cbn; repeat split; assumption | exact Hsw]
      | exact Hwf'
      | exact Hrcf].
  - rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
Qed.
