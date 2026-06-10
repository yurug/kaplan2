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

Lemma only_push_rebuild_sr :
  forall A (p3 s2 : buffer (stored A)) (cell : stored A) (d2 : cchain A),
    8 <= length p3 -> 5 <= length s2 ->
    buf_stored_all_wf p3 -> buf_stored_all_wf s2 ->
    stored_wf cell ->
    chain_wf KOnly d2 -> d2 <> CEmpty ->
    sr_facts (gyor_of (length s2)) d2 ->
    chain_wf KOnly
      (tree_of (Node KOnly p3 s2) (push_chain cell d2)) /\
    cchain_seq (tree_of (Node KOnly p3 s2) (push_chain cell d2))
    = buf_stored_seq p3 ++ stored_seq cell
      ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A p3 s2 cell d2 Hp8 Hs5 Hpw Hsw Hcw Hd2 Hne Hsr.
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
            (Node KOnly p3 s2) = gyor_of (length s2)).
  { rewrite Hhc, node_color_measure. cbn [node_measure].
    apply gyor_of_min_big. lia. }
  assert (Hrcf : root_color_facts (Node KOnly p3 s2)
                   (push_chain cell d2)).
  { unfold root_color_facts. rewrite Hnewc.
    destruct (gyor_of (length s2)) eqn:Hg.
    - exact I.
    - exact I.
    - destruct d2 as [|d2p d2r|d2l d2r]; [congruence | |].
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
    - cbn [sr_facts] in Hsr.
      destruct (@push_chain_preserves A cell d2 KOnly
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hne; exact Heq)
                  Hcw Hd2 Hsr) as [_ Hge'].
      exact Hge'. }
  split.
  - apply tree_of_wf;
      [reflexivity
      | rewrite Hhc; cbn [node_sizes]; left; split; lia
      | split; [exact Hpw | exact Hsw]
      | exact Hwf'
      | exact Hrcf].
  - rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
Qed.

Lemma only_inject_rebuild_sr :
  forall A (p1 s3 : buffer (stored A)) (cell : stored A) (d1 : cchain A),
    5 <= length p1 -> 8 <= length s3 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s3 ->
    stored_wf cell ->
    chain_wf KOnly d1 -> d1 <> CEmpty ->
    sr_facts (gyor_of (length p1)) d1 ->
    chain_wf KOnly
      (tree_of (Node KOnly p1 s3) (inject_chain d1 cell)) /\
    cchain_seq (tree_of (Node KOnly p1 s3) (inject_chain d1 cell))
    = buf_stored_seq p1 ++ cchain_seq d1 ++ stored_seq cell
      ++ buf_stored_seq s3.
Proof.
  intros A p1 s3 cell d1 Hp5 Hs8 Hpw Hsw Hcw Hd1 Hne Hsr.
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
            (Node KOnly p1 s3) = gyor_of (length p1)).
  { rewrite Hhc, node_color_measure. cbn [node_measure].
    apply gyor_of_min_big_r. lia. }
  assert (Hrcf : root_color_facts (Node KOnly p1 s3)
                   (inject_chain d1 cell)).
  { unfold root_color_facts. rewrite Hnewc.
    destruct (gyor_of (length p1)) eqn:Hg.
    - exact I.
    - exact I.
    - destruct d1 as [|d1p d1r|d1l d1r]; [congruence | |].
      + pose proof (@pkt_update_is_single A
                      (fun n => node_inject n cell) d1p d1r) as Hs.
        cbn [inject_chain].
        destruct (pkt_update (fun n => node_inject n cell) d1p d1r);
          cbn in Hs; try congruence.
        exact I.
      + cbn [inject_chain]. cbn [sr_facts] in Hsr. exact Hsr.
    - cbn [sr_facts] in Hsr.
      destruct (@inject_chain_preserves A cell d1 KOnly
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hne; exact Heq)
                  Hcw Hd1 Hsr) as [_ Hge'].
      exact Hge'. }
  split.
  - apply tree_of_wf;
      [reflexivity
      | rewrite Hhc; cbn [node_sizes]; left; split; lia
      | split; [exact Hpw | exact Hsw]
      | exact Hwf'
      | exact Hrcf].
  - rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
Qed.

(* ========================================================================== *)
(* SR only-builders (Cases 1c/1d on semiregular input).                        *)
(* ========================================================================== *)

Lemma make_left_only_sr :
  forall A (p1 : buffer (stored A)) (d1 : cchain A)
         (s1 : buffer (stored A)),
    5 <= length p1 -> 5 <= length s1 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    chain_wf KOnly d1 ->
    (d1 <> CEmpty ->
       sr_facts (gyor_of (Nat.min (length p1) (length s1))) d1) ->
    exists t,
      make_left_only p1 d1 s1 = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1.
Proof.
  intros A p1 d1 s1 Hp5 Hs5 Hpw Hsw Hd1 Hbk.
  unfold make_left_only.
  destruct d1 as [|d1p d1r|d1l d1rr].
  - destruct (length s1 <=? 8) eqn:H8.
    + destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
        as [s1' [y [z He]]].
      rewrite He.
      pose proof (buf_eject2_inv He) as Hb.
      pose proof (buf_eject2_length He) as Hlen.
      assert (Hsw' : buf_stored_all_wf (s1' ++ [y; z]))
        by (rewrite <- Hb; exact Hsw).
      apply buf_all_wf_app_inv in Hsw'. destruct Hsw' as [Hs1'w Hyz].
      cbn in Hyz. destruct Hyz as [Hyw [Hzw _]].
      exists (tree_of (Node KLeft (p1 ++ s1') [y; z]) CEmpty).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split.
      * apply tree_of_wf;
          [reflexivity
          | cbn [chain_has_node node_sizes];
            split; [rewrite length_app; lia | reflexivity]
          | split; [exact (buf_all_wf_app Hpw Hs1'w)
                   | cbn; repeat split; assumption]
          | exact I
          | exact I].
      * rewrite tree_of_seq, cnode_seq_eq, Hb. seq_normalize.
    + destruct s1 as [|a [|b2 [|c2 srest]]];
        try (cbn [length] in Hs5; lia).
      destruct (@buf_eject2_total (stored A) srest
                  ltac:(apply Nat.leb_gt in H8; cbn [length] in H8; lia))
        as [smid [y [z He]]].
      rewrite He.
      pose proof (buf_eject2_inv He) as Hb.
      pose proof (buf_eject2_length He) as Hlen.
      cbn in Hsw. destruct Hsw as [Haw [Hbw [Hcw2 Hrest]]].
      assert (Hrest' : buf_stored_all_wf (smid ++ [y; z]))
        by (rewrite <- Hb; exact Hrest).
      apply buf_all_wf_app_inv in Hrest'. destruct Hrest' as [Hsm Hyz].
      cbn in Hyz. destruct Hyz as [Hyw [Hzw _]].
      assert (Hsmlen : 3 <= length smid).
      { apply Nat.leb_gt in H8. cbn [length] in H8.
        assert (length srest = length smid + 2)
          by (rewrite Hb, length_app; cbn; lia).
        lia. }
      destruct (small_singleton_wf Hsmlen Hsm) as [Hcwf [Hcg Hcseq]].
      assert (Hnewc : node_color
                (chain_has_node (push_chain (SSmall smid) (@CEmpty A)))
                (Node KLeft (p1 ++ [a; b2; c2]) [y; z]) = CG).
      { cbn [push_chain chain_has_node].
        rewrite node_color_measure. cbn [node_measure].
        apply gyor_of_big. rewrite length_app. cbn [length]. lia. }
      exists (tree_of (Node KLeft (p1 ++ [a; b2; c2]) [y; z])
                (push_chain (SSmall smid) CEmpty)).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split.
      * apply tree_of_wf;
          [reflexivity
          | cbn [push_chain chain_has_node node_sizes];
            split; [rewrite length_app; cbn [length]; lia | reflexivity]
          | split;
              [apply buf_all_wf_app;
                 [exact Hpw | cbn; repeat split; assumption]
              | cbn; repeat split; assumption]
          | exact Hcwf
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * rewrite tree_of_seq, cnode_seq_eq, Hcseq, Hb. seq_normalize.
  - destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
      as [s1' [y [z He]]].
    rewrite He.
    pose proof (buf_eject2_inv He) as Hb.
    assert (Hsw' : buf_stored_all_wf (s1' ++ [y; z]))
      by (rewrite <- Hb; exact Hsw).
    apply buf_all_wf_app_inv in Hsw'. destruct Hsw' as [Hs1'w Hyz].
    cbn in Hyz. destruct Hyz as [Hyw [Hzw _]].
    assert (Hcellw : stored_wf (SSmall s1')).
    { cbn [stored_wf]. split; [| exact Hs1'w].
      pose proof (buf_eject2_length He). lia. }
    assert (Hbk' : sr_facts (gyor_of (length p1)) (CSingle d1p d1r)).
    { apply (@sr_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_l
        | exact (Hbk ltac:(discriminate))]. }
    destruct (left_rebuild_sr Hp5 Hpw Hyw Hzw Hcellw Hd1
                ltac:(discriminate) Hbk') as [Hwt Hseqt].
    exists (tree_of (Node KLeft p1 [y; z])
              (inject_chain (CSingle d1p d1r) (SSmall s1'))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
  - destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
      as [s1' [y [z He]]].
    rewrite He.
    pose proof (buf_eject2_inv He) as Hb.
    assert (Hsw' : buf_stored_all_wf (s1' ++ [y; z]))
      by (rewrite <- Hb; exact Hsw).
    apply buf_all_wf_app_inv in Hsw'. destruct Hsw' as [Hs1'w Hyz].
    cbn in Hyz. destruct Hyz as [Hyw [Hzw _]].
    assert (Hcellw : stored_wf (SSmall s1')).
    { cbn [stored_wf]. split; [| exact Hs1'w].
      pose proof (buf_eject2_length He). lia. }
    assert (Hbk' : sr_facts (gyor_of (length p1)) (CPair d1l d1rr)).
    { apply (@sr_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_l
        | exact (Hbk ltac:(discriminate))]. }
    destruct (left_rebuild_sr Hp5 Hpw Hyw Hzw Hcellw Hd1
                ltac:(discriminate) Hbk') as [Hwt Hseqt].
    exists (tree_of (Node KLeft p1 [y; z])
              (inject_chain (CPair d1l d1rr) (SSmall s1'))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
Qed.

Lemma make_right_only_sr :
  forall A (p1 : buffer (stored A)) (d1 : cchain A)
         (s1 : buffer (stored A)),
    5 <= length p1 -> 5 <= length s1 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    chain_wf KOnly d1 ->
    (d1 <> CEmpty ->
       sr_facts (gyor_of (Nat.min (length p1) (length s1))) d1) ->
    exists t,
      make_right_only p1 d1 s1 = Some t /\
      is_single t = true /\
      chain_wf KRight t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1.
Proof.
  intros A p1 d1 s1 Hp5 Hs5 Hpw Hsw Hd1 Hbk.
  unfold make_right_only.
  destruct d1 as [|d1p d1r|d1l d1rr].
  - destruct (length p1 <=? 8) eqn:H8.
    + destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
        as [x [y [p1' He]]].
      rewrite He.
      pose proof (buf_pop2_inv He) as Hb.
      rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
      exists (tree_of (Node KRight [x; y] (p1' ++ s1)) CEmpty).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split.
      * apply tree_of_wf;
          [reflexivity
          | cbn [chain_has_node node_sizes];
            split; [reflexivity | rewrite length_app; lia]
          | split; [cbn; repeat split; assumption
                   | exact (buf_all_wf_app Hp1'w Hsw)]
          | exact I
          | exact I].
      * rewrite tree_of_seq, cnode_seq_eq, Hb. seq_normalize.
    + destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
        as [x [y [p1' He]]].
      rewrite He.
      pose proof (buf_pop2_inv He) as Hb.
      assert (Hlen1 : length p1 = S (S (length p1')))
        by (rewrite Hb; reflexivity).
      apply Nat.leb_gt in H8.
      destruct (@buf_eject3_total (stored A) p1' ltac:(lia))
        as [pmid [a [b2 [c2 He3]]]].
      rewrite He3.
      pose proof (buf_eject3_inv He3) as Hb3.
      rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
      assert (Hp1'w' : buf_stored_all_wf (pmid ++ [a; b2; c2]))
        by (rewrite <- Hb3; exact Hp1'w).
      apply buf_all_wf_app_inv in Hp1'w'.
      destruct Hp1'w' as [Hmw Habc].
      cbn in Habc. destruct Habc as [Haw [Hbw [Hcw2 _]]].
      assert (Hmlen : 3 <= length pmid).
      { assert (Hl3 : length p1' = length pmid + 3)
          by (rewrite Hb3, length_app; cbn; lia). lia. }
      destruct (small_singleton_wf Hmlen Hmw) as [Hcwf [Hcg Hcseq]].
      assert (Hsufw : buf_stored_all_wf ([a; b2; c2] ++ s1)).
      { apply buf_all_wf_app;
          [cbn; repeat split; assumption | exact Hsw]. }
      assert (Hnewc : node_color
                (chain_has_node (push_chain (SSmall pmid) (@CEmpty A)))
                (Node KRight [x; y] ([a; b2; c2] ++ s1)) = CG).
      { cbn [push_chain chain_has_node].
        rewrite node_color_measure. cbn [node_measure].
        apply gyor_of_big. rewrite length_app. cbn [length]. lia. }
      exists (tree_of (Node KRight [x; y] ([a; b2; c2] ++ s1))
                (push_chain (SSmall pmid) CEmpty)).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split.
      * apply tree_of_wf;
          [reflexivity
          | cbn [push_chain chain_has_node node_sizes];
            split; [reflexivity | rewrite length_app; cbn [length]; lia]
          | split; [cbn; repeat split; assumption | exact Hsufw]
          | exact Hcwf
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * rewrite tree_of_seq, cnode_seq_eq, Hcseq, Hb, Hb3. seq_normalize.
  - destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
      as [x [y [p1' He]]].
    rewrite He.
    pose proof (buf_pop2_inv He) as Hb.
    assert (Hlen1 : length p1 = S (S (length p1')))
      by (rewrite Hb; reflexivity).
    rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
    assert (Hcellw : stored_wf (SSmall p1')).
    { cbn [stored_wf]. split; [lia | exact Hp1'w]. }
    assert (Hbk' : sr_facts (gyor_of (length s1)) (CSingle d1p d1r)).
    { apply (@sr_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_r
        | exact (Hbk ltac:(discriminate))]. }
    destruct (right_rebuild_sr Hs5 Hsw Hxw Hyw Hcellw Hd1
                ltac:(discriminate) Hbk') as [Hwt Hseqt].
    exists (tree_of (Node KRight [x; y] s1)
              (push_chain (SSmall p1') (CSingle d1p d1r))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
  - destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
      as [x [y [p1' He]]].
    rewrite He.
    pose proof (buf_pop2_inv He) as Hb.
    assert (Hlen1 : length p1 = S (S (length p1')))
      by (rewrite Hb; reflexivity).
    rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
    assert (Hcellw : stored_wf (SSmall p1')).
    { cbn [stored_wf]. split; [lia | exact Hp1'w]. }
    assert (Hbk' : sr_facts (gyor_of (length s1)) (CPair d1l d1rr)).
    { apply (@sr_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_r
        | exact (Hbk ltac:(discriminate))]. }
    destruct (right_rebuild_sr Hs5 Hsw Hxw Hyw Hcellw Hd1
                ltac:(discriminate) Hbk') as [Hwt Hseqt].
    exists (tree_of (Node KRight [x; y] s1)
              (push_chain (SSmall p1') (CPair d1l d1rr))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
Qed.

(* ========================================================================== *)
(* SR pair cores and dispatch (Cases 1a/1b on semiregular input).              *)
(* ========================================================================== *)

Lemma make_left_pair_core_sr :
  forall A (p1 s1 p2 s2 : buffer (stored A)) (d1 d2 : cchain A),
    5 <= length p1 -> length s1 = 2 ->
    length p2 = 2 -> 5 <= length s2 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    buf_stored_all_wf p2 -> buf_stored_all_wf s2 ->
    chain_wf KOnly d1 -> d1 <> CEmpty -> chain_wf KOnly d2 ->
    sr_facts (gyor_of (length p1)) d1 ->
    exists t,
      match buf_eject2 s2 with
      | Some (s2', y, z) =>
          Some (tree_of (Node KLeft p1 [y; z])
                  (inject_chain d1 (SBig (s1 ++ p2) d2 s2')))
      | None => None
      end = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1
        ++ buf_stored_seq p2 ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A p1 s1 p2 s2 d1 d2 Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
    Hd1 Hne Hd2 Hsr.
  destruct (@buf_eject2_total (stored A) s2 ltac:(lia))
    as [s2' [y [z He]]].
  rewrite He.
  pose proof (buf_eject2_inv He) as Hb.
  pose proof (buf_eject2_length He) as Hlen.
  assert (Hs2w' : buf_stored_all_wf (s2' ++ [y; z]))
    by (rewrite <- Hb; exact Hs2w).
  apply buf_all_wf_app_inv in Hs2w'.
  destruct Hs2w' as [Hs2'w Hyz]. cbn in Hyz.
  destruct Hyz as [Hyw [Hzw _]].
  assert (Hcellw : stored_wf (SBig (s1 ++ p2) d2 s2')).
  { cbn [stored_wf]. split; [rewrite length_app; lia |].
    split; [lia |].
    split; [exact (buf_all_wf_app Hs1w Hp2w) |].
    split; [exact Hs2'w | exact Hd2]. }
  destruct (left_rebuild_sr Hp1 Hp1w Hyw Hzw Hcellw Hd1 Hne Hsr)
    as [Hwt Hseqt].
  exists (tree_of (Node KLeft p1 [y; z])
            (inject_chain d1 (SBig (s1 ++ p2) d2 s2'))).
  split; [reflexivity |].
  split; [apply tree_of_is_single |].
  split; [exact Hwt |].
  rewrite Hseqt, Hb, stored_seq_SBig. seq_normalize.
Qed.

Lemma make_right_pair_core_sr :
  forall A (p1 s1 p2 s2 : buffer (stored A)) (d1 d2 : cchain A),
    5 <= length p1 -> length s1 = 2 ->
    length p2 = 2 -> 5 <= length s2 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    buf_stored_all_wf p2 -> buf_stored_all_wf s2 ->
    chain_wf KOnly d1 -> chain_wf KOnly d2 -> d2 <> CEmpty ->
    sr_facts (gyor_of (length s2)) d2 ->
    exists t,
      match buf_pop2 p1 with
      | Some (x, y, p1') =>
          Some (tree_of (Node KRight [x; y] s2)
                  (push_chain (SBig p1' d1 (s1 ++ p2)) d2))
      | None => None
      end = Some t /\
      is_single t = true /\
      chain_wf KRight t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1
        ++ buf_stored_seq p2 ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A p1 s1 p2 s2 d1 d2 Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
    Hd1 Hd2 Hne Hsr.
  destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
    as [x [y [p1' He]]].
  rewrite He.
  pose proof (buf_pop2_inv He) as Hb.
  assert (Hlen1 : length p1 = S (S (length p1')))
    by (rewrite Hb; reflexivity).
  rewrite Hb in Hp1w. cbn in Hp1w. destruct Hp1w as [Hxw [Hyw Hp1'w]].
  assert (Hcellw : stored_wf (SBig p1' d1 (s1 ++ p2))).
  { cbn [stored_wf]. split; [lia |].
    split; [rewrite length_app; lia |].
    split; [exact Hp1'w |].
    split; [exact (buf_all_wf_app Hs1w Hp2w) | exact Hd1]. }
  destruct (right_rebuild_sr Hs2 Hs2w Hxw Hyw Hcellw Hd2 Hne Hsr)
    as [Hwt Hseqt].
  exists (tree_of (Node KRight [x; y] s2)
            (push_chain (SBig p1' d1 (s1 ++ p2)) d2)).
  split; [reflexivity |].
  split; [apply tree_of_is_single |].
  split; [exact Hwt |].
  rewrite Hseqt, Hb, stored_seq_SBig. seq_normalize.
Qed.

Lemma make_left_sr :
  forall A (d : cchain A),
    chain_wf KOnly d ->
    d <> CEmpty -> degenerate_buf d = None ->
    exists t,
      make_left d = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\
      cchain_seq t = cchain_seq d.
Proof.
  intros A d Hwf Hne Hdeg.
  destruct d as [|p r|dl dr]; [congruence | |].
  - cbn [make_left].
    destruct (root_and_child p r) as [[k0 pp ss] child] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hfacts.
    rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
    destruct Hfacts as [Hk [_ [Hnw [Hcw Hrcf]]]].
    cbn [node_kind] in Hk. subst k0.
    destruct (root_two_sided Hrc Hwf Hdeg) as [Hp5 Hs5].
    cbn [cnode_wf] in Hnw. destruct Hnw as [Hpw Hsw].
    apply root_color_facts_sr in Hrcf.
    assert (Hbk : child <> CEmpty ->
        sr_facts (gyor_of (Nat.min (length pp) (length ss))) child).
    { intros Hcne.
      assert (Hhc : chain_has_node child = true)
        by (destruct child; [congruence | reflexivity | reflexivity]).
      rewrite Hhc, node_color_measure in Hrcf.
      cbn [node_measure] in Hrcf. exact Hrcf. }
    destruct (make_left_only_sr Hp5 Hs5 Hpw Hsw Hcw Hbk)
      as [t [Hmk [Hsing [Hwt Hseq]]]].
    exists t.
    split; [exact Hmk |]. split; [exact Hsing |].
    split; [exact Hwt |].
    rewrite Hseq.
    rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    cbn [make_left].
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 Hrcf1]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 Hrcf2]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [Hp1 Hs1]. destruct Hsz2 as [Hp2 Hs2].
    cbn [cnode_wf] in Hnw1, Hnw2.
    destruct Hnw1 as [Hp1w Hs1w]. destruct Hnw2 as [Hp2w Hs2w].
    apply root_color_facts_sr in Hrcf1, Hrcf2.
    destruct d1 as [|d1p d1r|d1l d1rr].
    + assert (Hp5 : 5 <= length (p1 ++ s1 ++ p2))
        by (rewrite !length_app; lia).
      assert (Hpw : buf_stored_all_wf (p1 ++ s1 ++ p2)).
      { apply buf_all_wf_app; [exact Hp1w |].
        apply buf_all_wf_app; [exact Hs1w | exact Hp2w]. }
      assert (Hbk : d2 <> CEmpty ->
          sr_facts
            (gyor_of (Nat.min (length (p1 ++ s1 ++ p2)) (length s2))) d2).
      { intros Hcne.
        rewrite gyor_of_min_big by (rewrite !length_app; lia).
        assert (Hhc : chain_has_node d2 = true)
          by (destruct d2; [congruence | reflexivity | reflexivity]).
        rewrite Hhc, node_color_measure in Hrcf2.
        cbn [node_measure] in Hrcf2. exact Hrcf2. }
      destruct (make_left_only_sr Hp5 Hs2 Hpw Hs2w Hcw2 Hbk)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + cbn [chain_has_node] in Hrcf1.
      rewrite node_color_measure in Hrcf1.
      cbn [node_measure] in Hrcf1.
      destruct (make_left_pair_core_sr Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w
                  Hs2w Hcw1 ltac:(discriminate) Hcw2 Hrcf1)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + cbn [chain_has_node] in Hrcf1.
      rewrite node_color_measure in Hrcf1.
      cbn [node_measure] in Hrcf1.
      destruct (make_left_pair_core_sr Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w
                  Hs2w Hcw1 ltac:(discriminate) Hcw2 Hrcf1)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
Qed.

Lemma make_right_sr :
  forall A (e : cchain A),
    chain_wf KOnly e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists t,
      make_right e = Some t /\
      is_single t = true /\
      chain_wf KRight t /\
      cchain_seq t = cchain_seq e.
Proof.
  intros A e Hwf Hne Hdeg.
  destruct e as [|p r|dl dr]; [congruence | |].
  - cbn [make_right].
    destruct (root_and_child p r) as [[k0 pp ss] child] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hfacts.
    rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
    destruct Hfacts as [Hk [_ [Hnw [Hcw Hrcf]]]].
    cbn [node_kind] in Hk. subst k0.
    destruct (root_two_sided Hrc Hwf Hdeg) as [Hp5 Hs5].
    cbn [cnode_wf] in Hnw. destruct Hnw as [Hpw Hsw].
    apply root_color_facts_sr in Hrcf.
    assert (Hbk : child <> CEmpty ->
        sr_facts (gyor_of (Nat.min (length pp) (length ss))) child).
    { intros Hcne.
      assert (Hhc : chain_has_node child = true)
        by (destruct child; [congruence | reflexivity | reflexivity]).
      rewrite Hhc, node_color_measure in Hrcf.
      cbn [node_measure] in Hrcf. exact Hrcf. }
    destruct (make_right_only_sr Hp5 Hs5 Hpw Hsw Hcw Hbk)
      as [t [Hmk [Hsing [Hwt Hseq]]]].
    exists t.
    split; [exact Hmk |]. split; [exact Hsing |].
    split; [exact Hwt |].
    rewrite Hseq.
    rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    cbn [make_right].
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 Hrcf1]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 Hrcf2]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [Hp1 Hs1]. destruct Hsz2 as [Hp2 Hs2].
    cbn [cnode_wf] in Hnw1, Hnw2.
    destruct Hnw1 as [Hp1w Hs1w]. destruct Hnw2 as [Hp2w Hs2w].
    apply root_color_facts_sr in Hrcf1, Hrcf2.
    destruct d2 as [|d2p d2r|d2l d2rr].
    + assert (Hs5 : 5 <= length (s1 ++ p2 ++ s2))
        by (rewrite !length_app; lia).
      assert (Hsw : buf_stored_all_wf (s1 ++ p2 ++ s2)).
      { apply buf_all_wf_app; [exact Hs1w |].
        apply buf_all_wf_app; [exact Hp2w | exact Hs2w]. }
      assert (Hbk : d1 <> CEmpty ->
          sr_facts
            (gyor_of (Nat.min (length p1) (length (s1 ++ p2 ++ s2)))) d1).
      { intros Hcne.
        rewrite gyor_of_min_big_r by (rewrite !length_app; lia).
        assert (Hhc : chain_has_node d1 = true)
          by (destruct d1; [congruence | reflexivity | reflexivity]).
        rewrite Hhc, node_color_measure in Hrcf1.
        cbn [node_measure] in Hrcf1. exact Hrcf1. }
      destruct (make_right_only_sr Hp1 Hs5 Hp1w Hsw Hcw1 Hbk)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + cbn [chain_has_node] in Hrcf2.
      rewrite node_color_measure in Hrcf2.
      cbn [node_measure] in Hrcf2.
      destruct (make_right_pair_core_sr Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w
                  Hs2w Hcw1 Hcw2 ltac:(discriminate) Hrcf2)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + cbn [chain_has_node] in Hrcf2.
      rewrite node_color_measure in Hrcf2.
      cbn [node_measure] in Hrcf2.
      destruct (make_right_pair_core_sr Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w
                  Hs2w Hcw1 Hcw2 ltac:(discriminate) Hrcf2)
        as [t [Hmk [Hsing [Hwt Hseq]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
Qed.

(* ========================================================================== *)
(* SR small-side concat and the dispatch.                                      *)
(* ========================================================================== *)

Lemma fold_push_wf :
  forall A (b : buffer (stored A)) (c : cchain A),
    buf_stored_all_wf b -> chain_wf KOnly c ->
    chain_wf KOnly (fold_right push_chain c b).
Proof.
  intros A b. induction b as [|x rb IH]; intros c Hb Hc;
    cbn [fold_right].
  - exact Hc.
  - destruct Hb as [Hx Hrb].
    apply (@push_chain_preserves_wf A x
             (fold_right push_chain c rb) KOnly);
      [congruence | intros _; reflexivity | exact Hx
      | apply IH; assumption].
Qed.

Lemma fold_inject_wf :
  forall A (b : buffer (stored A)) (c : cchain A),
    chain_wf KOnly c -> buf_stored_all_wf b ->
    chain_wf KOnly (fold_left inject_chain b c).
Proof.
  intros A b. induction b as [|x rb IH]; intros c Hc Hb;
    cbn [fold_left].
  - exact Hc.
  - destruct Hb as [Hx Hrb].
    apply IH; [| exact Hrb].
    apply (@inject_chain_preserves_wf A x c KOnly);
      [congruence | intros _; reflexivity | exact Hx | exact Hc].
Qed.

Lemma fold_push_wf_seq :
  forall A (l : buffer (stored A)) (c : cchain A),
    buf_stored_all_wf l -> chain_wf KOnly c ->
    chain_wf KOnly (fold_right push_chain c l) /\
    cchain_seq (fold_right push_chain c l)
    = buf_stored_seq l ++ cchain_seq c.
Proof.
  intros A l. induction l as [|x r IH]; intros c Hl Hwf.
  - cbn. split; [exact Hwf | reflexivity].
  - destruct Hl as [Hx Hr].
    destruct (IH c Hr Hwf) as [Hwf' Hseq'].
    cbn [fold_right].
    split.
    + apply (@push_chain_preserves_wf A x
               (fold_right push_chain c r) KOnly);
        [congruence | intros _; reflexivity | exact Hx | exact Hwf'].
    + rewrite (push_chain_seq x Hwf').
      rewrite Hseq'. cbn [buf_stored_seq].
      rewrite app_assoc. reflexivity.
Qed.

Lemma fold_inject_wf_seq :
  forall A (l : buffer (stored A)) (c : cchain A),
    buf_stored_all_wf l -> chain_wf KOnly c ->
    chain_wf KOnly (fold_left inject_chain l c) /\
    cchain_seq (fold_left inject_chain l c)
    = cchain_seq c ++ buf_stored_seq l.
Proof.
  intros A l. induction l as [|x r IH]; intros c Hl Hwf.
  - cbn. split; [exact Hwf | rewrite app_nil_r; reflexivity].
  - destruct Hl as [Hx Hr].
    assert (Hwf1 : chain_wf KOnly (inject_chain c x)).
    { apply (@inject_chain_preserves_wf A x c KOnly);
        [congruence | intros _; reflexivity | exact Hx | exact Hwf]. }
    destruct (IH (inject_chain c x) Hr Hwf1) as [Hwf' Hseq'].
    cbn [fold_left].
    split; [exact Hwf' |].
    rewrite Hseq'.
    rewrite (inject_chain_seq x Hwf).
    cbn [buf_stored_seq].
    rewrite <- !app_assoc. reflexivity.
Qed.

Lemma concat_small_left_sr :
  forall A (p3 : buffer (stored A)) (e : cchain A),
    1 <= length p3 -> buf_stored_all_wf p3 ->
    chain_wf KOnly e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists f,
      concat_small_left p3 e = Some f /\
      chain_wf KOnly f /\
      cchain_seq f = buf_stored_seq p3 ++ cchain_seq e.
Proof.
  intros A p3 e Hp Hpw Hwf Hne Hdeg.
  unfold concat_small_left.
  destruct (length p3 <? 8) eqn:H8.
  - destruct (fold_push_wf_seq Hpw Hwf) as [Hwf' Hseq'].
    eexists. split; [reflexivity |]. split; assumption.
  - apply Nat.ltb_ge in H8.
    destruct e as [|p r|el er]; [congruence | |].
    + destruct (root_and_child p r) as [[k0 p2 s2] d2] eqn:Hrc.
      cbn [fst snd].
      pose proof (root_and_child_facts Hwf) as Hfacts.
      rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
      destruct Hfacts as [Hk [_ [Hnw [Hcw Hrcf]]]].
      cbn [node_kind] in Hk. subst k0.
      destruct (root_two_sided Hrc Hwf Hdeg) as [Hp2 Hs2].
      cbn [cnode_wf] in Hnw. destruct Hnw as [Hp2w Hs2w].
      apply root_color_facts_sr in Hrcf.
      assert (Hseq0 : cchain_seq (CSingle p r)
                      = buf_stored_seq p2 ++ cchain_seq d2
                        ++ buf_stored_seq s2).
      { rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
        rewrite cnode_seq_eq. reflexivity. }
      destruct d2 as [|d2p d2r|d2l d2rr].
      * (* childless: the eject2-lift branch — CY/CG result *)
        destruct (@buf_eject2_total (stored A) p2 ltac:(lia))
          as [p2' [y [z He]]].
        rewrite He.
        pose proof (buf_eject2_inv He) as Hb.
        pose proof (buf_eject2_length He) as Hlen.
        assert (Hp2w' : buf_stored_all_wf (p2' ++ [y; z]))
          by (rewrite <- Hb; exact Hp2w).
        apply buf_all_wf_app_inv in Hp2w'.
        destruct Hp2w' as [Hp2'w Hyz].
        cbn in Hyz. destruct Hyz as [Hyw [Hzw _]].
        assert (Hp2'len : 3 <= length p2') by lia.
        destruct (small_singleton_wf Hp2'len Hp2'w)
          as [Hcwf [Hcg Hcseq]].
        assert (Hsw' : buf_stored_all_wf (y :: z :: s2))
          by (cbn; repeat split; assumption).
        assert (Hmin7 : 7 <= Nat.min (length p3)
                               (length (y :: z :: s2)))
          by (cbn [length]; apply Nat.min_glb; lia).
        assert (Hnewc : node_color
                  (chain_has_node (push_chain (SSmall p2') (@CEmpty A)))
                  (Node KOnly p3 (y :: z :: s2))
                = gyor_of (Nat.min (length p3)
                             (length (y :: z :: s2)))).
        { cbn [push_chain chain_has_node].
          rewrite node_color_measure. cbn [node_measure]. reflexivity. }
        eexists. split; [reflexivity |].
        split.
        -- apply tree_of_wf;
             [reflexivity
             | cbn [push_chain chain_has_node node_sizes]; left;
               split; [lia | cbn [length]; lia]
             | split; [exact Hpw | exact Hsw']
             | exact Hcwf
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of_ge7 Hmin7) as [Hcol|Hcol];
               rewrite Hcol; exact I].
        -- rewrite tree_of_seq, cnode_seq_eq, Hcseq.
           rewrite Hseq0, Hb. seq_normalize.
      * (* rooted: only_push_rebuild_sr *)
        assert (Hcellw : stored_wf (SSmall p2))
          by (cbn [stored_wf]; split; [lia | exact Hp2w]).
        assert (Hbk : sr_facts (gyor_of (length s2)) (CSingle d2p d2r)).
        { apply (@sr_facts_mono A
                   (gyor_of (Nat.min (length p2) (length s2))));
            [apply gyor_of_mono; apply Nat.le_min_r |].
          cbn [chain_has_node] in Hrcf.
          rewrite node_color_measure in Hrcf.
          cbn [node_measure] in Hrcf. exact Hrcf. }
        destruct (only_push_rebuild_sr H8 Hs2 Hpw Hs2w Hcellw Hcw
                    ltac:(discriminate) Hbk) as [Hwt Hseqt].
        eexists. split; [reflexivity |].
        split; [exact Hwt |].
        rewrite Hseqt, stored_seq_SSmall, Hseq0. seq_normalize.
      * assert (Hcellw : stored_wf (SSmall p2))
          by (cbn [stored_wf]; split; [lia | exact Hp2w]).
        assert (Hbk : sr_facts (gyor_of (length s2)) (CPair d2l d2rr)).
        { apply (@sr_facts_mono A
                   (gyor_of (Nat.min (length p2) (length s2))));
            [apply gyor_of_mono; apply Nat.le_min_r |].
          cbn [chain_has_node] in Hrcf.
          rewrite node_color_measure in Hrcf.
          cbn [node_measure] in Hrcf. exact Hrcf. }
        destruct (only_push_rebuild_sr H8 Hs2 Hpw Hs2w Hcellw Hcw
                    ltac:(discriminate) Hbk) as [Hwt Hseqt].
        eexists. split; [reflexivity |].
        split; [exact Hwt |].
        rewrite Hseqt, stored_seq_SSmall, Hseq0. seq_normalize.
    + (* pair: rebuild the left component over the parked SSmall *)
      cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
      destruct el as [|pl rl|? ?]; cbn [is_single] in Hls;
        try discriminate.
      destruct (root_and_child pl rl) as [[k1 p2 s2] d2] eqn:Hrc1.
      cbn [fst snd].
      pose proof (root_and_child_facts Hl) as Hf1.
      rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
      destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 _]]]].
      cbn [node_kind] in Hk1. subst k1.
      cbn [node_sizes] in Hsz1. destruct Hsz1 as [Hp2 Hs2].
      cbn [cnode_wf] in Hnw1. destruct Hnw1 as [Hp2w Hs2w].
      assert (Hcellw : stored_wf (SSmall p2))
        by (cbn [stored_wf]; split; [lia | exact Hp2w]).
      assert (Hwf2 : chain_wf KOnly (push_chain (SSmall p2) d2)).
      { apply (@push_chain_preserves_wf A (SSmall p2) d2 KOnly);
          [congruence | intros _; reflexivity
          | exact Hcellw | exact Hcw1]. }
      assert (Hseq2 : cchain_seq (push_chain (SSmall p2) d2)
                      = buf_stored_seq p2 ++ cchain_seq d2)
        by (rewrite (push_chain_seq (SSmall p2) Hcw1); reflexivity).
      assert (Hnewc : node_color
                (chain_has_node (push_chain (SSmall p2) d2))
                (Node KLeft p3 s2) = CG).
      { destruct (chain_has_node (push_chain (SSmall p2) d2)).
        - rewrite node_color_measure. cbn [node_measure].
          apply gyor_of_big. lia.
        - apply node_color_no_child. }
      eexists. split; [reflexivity |].
      split.
      * cbn [chain_wf].
        split; [apply tree_of_is_single |].
        split; [exact Hrs |].
        split; [| exact Hr].
        apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | exact Hs2]
          | split; [exact Hpw | exact Hs2w]
          | exact Hwf2
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * rewrite (cchain_seq_pair
          (tree_of (Node KLeft p3 s2) (push_chain (SSmall p2) d2)) er).
        rewrite (cchain_seq_pair (CSingle pl rl) er).
        rewrite tree_of_seq, cnode_seq_eq, Hseq2.
        rewrite (root_and_child_seq pl rl), Hrc1. cbn [fst snd].
        rewrite cnode_seq_eq. seq_normalize.
Qed.

Lemma concat_small_right_sr :
  forall A (d : cchain A) (s3 : buffer (stored A)),
    1 <= length s3 -> buf_stored_all_wf s3 ->
    chain_wf KOnly d ->
    d <> CEmpty -> degenerate_buf d = None ->
    exists f,
      concat_small_right d s3 = Some f /\
      chain_wf KOnly f /\
      cchain_seq f = cchain_seq d ++ buf_stored_seq s3.
Proof.
  intros A d s3 Hs Hsw Hwf Hne Hdeg.
  unfold concat_small_right.
  destruct (length s3 <? 8) eqn:H8.
  - destruct (fold_inject_wf_seq Hsw Hwf) as [Hwf' Hseq'].
    eexists. split; [reflexivity |]. split; assumption.
  - apply Nat.ltb_ge in H8.
    destruct d as [|p r|dl dr]; [congruence | |].
    + destruct (root_and_child p r) as [[k0 p1 s1] d1] eqn:Hrc.
      cbn [fst snd].
      pose proof (root_and_child_facts Hwf) as Hfacts.
      rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
      destruct Hfacts as [Hk [_ [Hnw [Hcw Hrcf]]]].
      cbn [node_kind] in Hk. subst k0.
      destruct (root_two_sided Hrc Hwf Hdeg) as [Hp1 Hs1].
      cbn [cnode_wf] in Hnw. destruct Hnw as [Hp1w Hs1w].
      apply root_color_facts_sr in Hrcf.
      assert (Hseq0 : cchain_seq (CSingle p r)
                      = buf_stored_seq p1 ++ cchain_seq d1
                        ++ buf_stored_seq s1).
      { rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
        rewrite cnode_seq_eq. reflexivity. }
      destruct d1 as [|d1p d1r|d1l d1rr].
      * (* childless: the pop2-lift branch *)
        destruct (@buf_pop2_total (stored A) s1 ltac:(lia))
          as [x [y [s1' He]]].
        rewrite He.
        pose proof (buf_pop2_inv He) as Hb.
        assert (Hlen : length s1 = S (S (length s1')))
          by (rewrite Hb; reflexivity).
        rewrite Hb in Hs1w. cbn in Hs1w.
        destruct Hs1w as [Hxw [Hyw Hs1'w]].
        assert (Hs1'len : 3 <= length s1') by lia.
        destruct (small_singleton_wf Hs1'len Hs1'w)
          as [Hcwf [Hcg Hcseq]].
        assert (Hplen : length (p1 ++ [x; y]) = length p1 + 2)
          by (rewrite length_app; reflexivity).
        assert (Hpw' : buf_stored_all_wf (p1 ++ [x; y])).
        { apply buf_all_wf_app;
            [exact Hp1w | cbn; repeat split; assumption]. }
        assert (Hmin7 : 7 <= Nat.min (length (p1 ++ [x; y]))
                               (length s3))
          by (rewrite Hplen; apply Nat.min_glb; lia).
        assert (Hnewc : node_color
                  (chain_has_node (push_chain (SSmall s1') (@CEmpty A)))
                  (Node KOnly (p1 ++ [x; y]) s3)
                = gyor_of (Nat.min (length (p1 ++ [x; y]))
                             (length s3))).
        { cbn [push_chain chain_has_node].
          rewrite node_color_measure. cbn [node_measure]. reflexivity. }
        eexists. split; [reflexivity |].
        split.
        -- apply tree_of_wf;
             [reflexivity
             | cbn [push_chain chain_has_node node_sizes]; left;
               split; [rewrite Hplen; lia | lia]
             | split; [exact Hpw' | exact Hsw]
             | exact Hcwf
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of_ge7 Hmin7) as [Hcol|Hcol];
               rewrite Hcol; exact I].
        -- rewrite tree_of_seq, cnode_seq_eq, Hcseq.
           rewrite Hseq0, Hb. seq_normalize.
      * (* rooted *)
        assert (Hcellw : stored_wf (SSmall s1))
          by (cbn [stored_wf]; split; [lia | exact Hs1w]).
        assert (Hbk : sr_facts (gyor_of (length p1)) (CSingle d1p d1r)).
        { apply (@sr_facts_mono A
                   (gyor_of (Nat.min (length p1) (length s1))));
            [apply gyor_of_mono; apply Nat.le_min_l |].
          cbn [chain_has_node] in Hrcf.
          rewrite node_color_measure in Hrcf.
          cbn [node_measure] in Hrcf. exact Hrcf. }
        destruct (only_inject_rebuild_sr Hp1 H8 Hp1w Hsw Hcellw Hcw
                    ltac:(discriminate) Hbk) as [Hwt Hseqt].
        eexists. split; [reflexivity |].
        split; [exact Hwt |].
        rewrite Hseqt, stored_seq_SSmall, Hseq0. seq_normalize.
      * assert (Hcellw : stored_wf (SSmall s1))
          by (cbn [stored_wf]; split; [lia | exact Hs1w]).
        assert (Hbk : sr_facts (gyor_of (length p1)) (CPair d1l d1rr)).
        { apply (@sr_facts_mono A
                   (gyor_of (Nat.min (length p1) (length s1))));
            [apply gyor_of_mono; apply Nat.le_min_l |].
          cbn [chain_has_node] in Hrcf.
          rewrite node_color_measure in Hrcf.
          cbn [node_measure] in Hrcf. exact Hrcf. }
        destruct (only_inject_rebuild_sr Hp1 H8 Hp1w Hsw Hcellw Hcw
                    ltac:(discriminate) Hbk) as [Hwt Hseqt].
        eexists. split; [reflexivity |].
        split; [exact Hwt |].
        rewrite Hseqt, stored_seq_SSmall, Hseq0. seq_normalize.
    + (* pair: rebuild the right component *)
      cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
      destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs;
        try discriminate.
      destruct (root_and_child pr rr) as [[k2 p1 s1] d1] eqn:Hrc2.
      cbn [fst snd].
      pose proof (root_and_child_facts Hr) as Hf2.
      rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
      destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 _]]]].
      cbn [node_kind] in Hk2. subst k2.
      cbn [node_sizes] in Hsz2. destruct Hsz2 as [Hp1 Hs1].
      cbn [cnode_wf] in Hnw2. destruct Hnw2 as [Hp1w Hs1w].
      assert (Hcellw : stored_wf (SSmall s1))
        by (cbn [stored_wf]; split; [lia | exact Hs1w]).
      assert (Hwf2 : chain_wf KOnly (inject_chain d1 (SSmall s1))).
      { apply (@inject_chain_preserves_wf A (SSmall s1) d1 KOnly);
          [congruence | intros _; reflexivity
          | exact Hcellw | exact Hcw2]. }
      assert (Hseq2 : cchain_seq (inject_chain d1 (SSmall s1))
                      = cchain_seq d1 ++ buf_stored_seq s1)
        by (rewrite (inject_chain_seq (SSmall s1) Hcw2); reflexivity).
      assert (Hnewc : node_color
                (chain_has_node (inject_chain d1 (SSmall s1)))
                (Node KRight p1 s3) = CG).
      { destruct (chain_has_node (inject_chain d1 (SSmall s1))).
        - rewrite node_color_measure. cbn [node_measure].
          apply gyor_of_big. lia.
        - apply node_color_no_child. }
      eexists. split; [reflexivity |].
      split.
      * cbn [chain_wf].
        split; [exact Hls |].
        split; [apply tree_of_is_single |].
        split; [exact Hl |].
        apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [exact Hp1 | lia]
          | split; [exact Hp1w | exact Hsw]
          | exact Hwf2
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * rewrite (cchain_seq_pair dl
          (tree_of (Node KRight p1 s3) (inject_chain d1 (SSmall s1)))).
        rewrite (cchain_seq_pair dl (CSingle pr rr)).
        rewrite tree_of_seq, cnode_seq_eq, Hseq2.
        rewrite (root_and_child_seq pr rr), Hrc2. cbn [fst snd].
        rewrite cnode_seq_eq. seq_normalize.
Qed.

(* ========================================================================== *)
(* The SR concat dispatch: Lemma 6.2's weak half.                              *)
(* ========================================================================== *)

Lemma cad_concat_sr :
  forall A (d e : cadeque A),
    chain_wf KOnly d -> chain_wf KOnly e ->
    exists f,
      cad_concat d e = Some f /\
      chain_wf KOnly f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof.
  intros A d e Hwfd Hwfe.
  assert (Hcore :
    forall (d' e' : cchain A),
      chain_wf KOnly d' -> chain_wf KOnly e' ->
      d' <> CEmpty -> e' <> CEmpty ->
      exists f,
        match degenerate_buf d', degenerate_buf e' with
        | Some p, Some s =>
            if (length p <? 8) || (length s <? 8)
            then Some (CSingle (Pkt BHole (Node KOnly (p ++ s) [])) CEmpty)
            else Some (CSingle (Pkt BHole (Node KOnly p s)) CEmpty)
        | Some p, None => concat_small_left p e'
        | None, Some s => concat_small_right d' s
        | None, None =>
            match make_left d', make_right e' with
            | Some t, Some u => Some (CPair t u)
            | _, _ => None
            end
        end = Some f /\
        chain_wf KOnly f /\
        cchain_seq f = cchain_seq d' ++ cchain_seq e').
  { intros d' e' Hwd Hwe Hned Hnee.
    destruct (degenerate_buf d') as [p|] eqn:Hdd;
      destruct (degenerate_buf e') as [s|] eqn:Hde.
    - destruct (degenerate_buf_facts Hwd Hdd) as [Hp1 [Hpw Hps]].
      destruct (degenerate_buf_facts Hwe Hde) as [Hs1 [Hsw Hss]].
      destruct (concat_case4 Hp1 Hs1 Hpw Hsw)
        as [f [Hf [Hw [_ Hs]]]].
      exists f. split; [exact Hf |]. split; [exact Hw |].
      rewrite Hs, Hps, Hss. reflexivity.
    - destruct (degenerate_buf_facts Hwd Hdd) as [Hp1 [Hpw Hps]].
      destruct (concat_small_left_sr Hp1 Hpw Hwe Hnee Hde)
        as [f [Hf [Hw Hs]]].
      exists f. split; [exact Hf |]. split; [exact Hw |].
      rewrite Hs, Hps. reflexivity.
    - destruct (degenerate_buf_facts Hwe Hde) as [Hs1 [Hsw Hss]].
      destruct (concat_small_right_sr Hs1 Hsw Hwd Hned Hdd)
        as [f [Hf [Hw Hs]]].
      exists f. split; [exact Hf |]. split; [exact Hw |].
      rewrite Hs, Hss. reflexivity.
    - destruct (make_left_sr Hwd Hned Hdd)
        as [t [Hmt [Hst [Hwt Hseqt]]]].
      destruct (make_right_sr Hwe Hnee Hde)
        as [u [Hmu [Hsu [Hwu Hsequ]]]].
      rewrite Hmt, Hmu.
      eexists. split; [reflexivity |].
      split.
      + cbn [chain_wf].
        split; [exact Hst |]. split; [exact Hsu |].
        split; [exact Hwt | exact Hwu].
      + rewrite (cchain_seq_pair t u), Hseqt, Hsequ. reflexivity. }
  unfold cad_concat, cad_to_list.
  destruct d as [|? ?|? ?].
  { exists e. split; [reflexivity |].
    split; [exact Hwfe | reflexivity]. }
  - destruct e as [|? ?|? ?].
    { eexists. split; [reflexivity |].
      split; [exact Hwfd |].
      cbn [cchain_seq]. rewrite app_nil_r. reflexivity. }
    + exact (Hcore _ _ Hwfd Hwfe
               ltac:(discriminate) ltac:(discriminate)).
    + exact (Hcore _ _ Hwfd Hwfe
               ltac:(discriminate) ltac:(discriminate)).
  - destruct e as [|? ?|? ?].
    { eexists. split; [reflexivity |].
      split; [exact Hwfd |].
      cbn [cchain_seq]. rewrite app_nil_r. reflexivity. }
    + exact (Hcore _ _ Hwfd Hwfe
               ltac:(discriminate) ltac:(discriminate)).
    + exact (Hcore _ _ Hwfd Hwfe
               ltac:(discriminate) ltac:(discriminate)).
Qed.
