(** * KTDeque.Catenable.RepairLemmas — §6 red-terminal repair (Phase 4b, C).

    A packet whose terminal went red after a raw removal is repaired by
    draining one stored cell from the terminal's child chain (full J by the
    red clause), splicing its buffer into the deficient side, and
    re-attaching its own child by ONE semiregular concat (cad_concat_sr).
    The repaired terminal is GREEN (5 + >=3 = >=8), restoring the top path.
    Non-recursive; constant buffer work. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas
  ConcatLemmas PopLemmas SRLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Front repair: refill a red prefix (KLeft, or KOnly with a big suffix).     *)
(* ========================================================================== *)

Lemma repair_front_total :
  forall A (kd0 : kind) (k0 : nat) (body : cbody A) (k : kind)
         (p1 s1 : buffer (stored A)) (rest : cchain A),
    cbody_wf kd0 body ->
    node_kind (Node k p1 s1) = body_out_kind kd0 body ->
    node_sizes (chain_has_node rest) (Node k p1 s1) ->
    cnode_wf (Node k p1 s1) ->
    node_color (chain_has_node rest) (Node k p1 s1) = CR ->
    chain_ends_green rest ->
    chain_wf KOnly rest ->
    cbody_leveled k0 body ->
    cnode_leveled (k0 + body_depth body) (Node k p1 s1) ->
    chain_leveled (S (k0 + body_depth body)) rest ->
    (k = KLeft \/ (k = KOnly /\ 8 <= length s1)) ->
    exists f,
      repair_front k body p1 s1 rest = Some f /\
      chain_wf kd0 f /\ chain_ends_green f /\ chain_leveled k0 f /\
      cchain_seq f = cchain_seq (CSingle (Pkt body (Node k p1 s1)) rest).
Proof.
  intros A kd0 k0 body k p1 s1 rest Hbw Hbk Hsz Hnw Hred Hgrest Hwrest
    Hbl Hnl Hrl Hkd.
  assert (Hne : rest <> CEmpty).
  { intros ->. cbn [chain_has_node] in Hred.
    rewrite node_color_no_child in Hred. discriminate. }
  assert (Hhc : chain_has_node rest = true)
    by (destruct rest; [congruence | reflexivity | reflexivity]).
  rewrite Hhc in Hred, Hsz.
  cbn [cnode_wf] in Hnw. destruct Hnw as [Hp1w Hs1w].
  cbn [cnode_leveled] in Hnl. destruct Hnl as [Hp1l Hs1l].
  assert (Hp15 : 5 <= length p1).
  { destruct Hkd as [-> | [-> Hs8]]; cbn [node_sizes] in Hsz.
    - destruct Hsz as [H1 _]. exact H1.
    - destruct Hsz as [[H1 _] | [Hc _]]; [exact H1 | discriminate]. }
  destruct (@pop_raw_J_total A (S (k0 + body_depth body)) rest
              Hwrest Hgrest Hrl Hne)
    as [cell [d1' [Hpop [Hcellw [Hcelll [Hwd1' [Hld1' Hseqp]]]]]]].
  unfold repair_front. rewrite Hpop.
  destruct cell as [g|b|p2 d2 s2].
  { cbn [stored_leveled] in Hcelll. discriminate. }
  - (* SSmall b: pure splice, no concat *)
    cbn [stored_wf] in Hcellw. destruct Hcellw as [Hb3 Hbw'].
    cbn [stored_leveled] in Hcelll.
    assert (Hvg : node_color (chain_has_node d1')
                    (Node k (p1 ++ b) s1) = CG).
    { destruct (chain_has_node d1').
      - rewrite node_color_measure.
        destruct Hkd as [-> | [-> Hs8]]; cbn [node_measure].
        + apply gyor_of_big. rewrite length_app. lia.
        + apply gyor_of_big. rewrite length_app.
          apply Nat.min_glb; lia.
      - apply node_color_no_child. }
    eexists. split; [reflexivity |].
    split; [| split; [| split]].
    + cbn [chain_wf].
      split; [exact Hbw |].
      split; [exact Hbk |].
      split.
      { destruct Hkd as [-> | [-> Hs8]]; cbn [node_sizes] in Hsz |- *.
        - destruct Hsz as [_ H2].
          split; [rewrite length_app; lia | exact H2].
        - left. split; [rewrite length_app; lia | lia]. }
      split.
      { split; [exact (buf_all_wf_app Hp1w Hbw') | exact Hs1w]. }
      split; [left; exact Hvg | exact Hwd1'].
    + cbn [chain_ends_green]. exact Hvg.
    + cbn [chain_leveled].
      split; [exact Hbl |].
      split.
      { cbn [cnode_leveled].
        split; [exact (buf_all_leveled_app Hp1l Hcelll) | exact Hs1l]. }
      exact Hld1'.
    + cbn [cchain_seq cpacket_seq].
      f_equal.
      rewrite !cnode_seq_eq, Hseqp.
      cbn [stored_seq]. seq_normalize.
  - (* SBig p2 d2 s2: splice the prefix, re-attach the rest by SR concat *)
    cbn [stored_wf] in Hcellw.
    destruct Hcellw as [Hp23 [Hs23 [Hp2w [Hs2w Hwd2]]]].
    cbn [stored_leveled] in Hcelll.
    destruct Hcelll as [Hp2l [Hs2l Hld2]].
    assert (Hcellw2 : stored_wf (SSmall s2))
      by (cbn [stored_wf]; split; [exact Hs23 | exact Hs2w]).
    assert (Hwpush : chain_wf KOnly (push_chain (SSmall s2) d1')).
    { apply (@push_chain_preserves_wf A (SSmall s2) d1' KOnly);
        [congruence | intros _; reflexivity
        | exact Hcellw2 | exact Hwd1']. }
    destruct (cad_concat_sr Hwd2 Hwpush) as [d3 [Hcc [Hwd3 Hseq3]]].
    rewrite Hcc.
    assert (Hld3 : chain_leveled (S (k0 + body_depth body)) d3).
    { apply (cad_concat_leveled Hld2
               (e:=push_chain (SSmall s2) d1') (f:=d3));
        [| exact Hcc].
      apply (push_chain_leveled (s:=SSmall s2)).
      - cbn [stored_leveled]. exact Hs2l.
      - exact Hld1'. }
    assert (Hvg : node_color (chain_has_node d3)
                    (Node k (p1 ++ p2) s1) = CG).
    { destruct (chain_has_node d3).
      - rewrite node_color_measure.
        destruct Hkd as [-> | [-> Hs8]]; cbn [node_measure].
        + apply gyor_of_big. rewrite length_app. lia.
        + apply gyor_of_big. rewrite length_app.
          apply Nat.min_glb; lia.
      - apply node_color_no_child. }
    eexists. split; [reflexivity |].
    split; [| split; [| split]].
    + cbn [chain_wf].
      split; [exact Hbw |].
      split; [exact Hbk |].
      split.
      { destruct Hkd as [-> | [-> Hs8]]; cbn [node_sizes] in Hsz |- *.
        - destruct Hsz as [_ H2].
          split; [rewrite length_app; lia | exact H2].
        - left. split; [rewrite length_app; lia | lia]. }
      split.
      { split; [exact (buf_all_wf_app Hp1w Hp2w) | exact Hs1w]. }
      split; [left; exact Hvg | exact Hwd3].
    + cbn [chain_ends_green]. exact Hvg.
    + cbn [chain_leveled].
      split; [exact Hbl |].
      split.
      { cbn [cnode_leveled].
        split; [exact (buf_all_leveled_app Hp1l Hp2l) | exact Hs1l]. }
      exact Hld3.
    + cbn [cchain_seq cpacket_seq].
      f_equal.
      rewrite !cnode_seq_eq, Hseqp.
      unfold cad_to_list in Hseq3. rewrite Hseq3.
      rewrite (push_chain_seq (SSmall s2) Hwd1').
      cbn [stored_seq]. seq_normalize.
Qed.

(* ========================================================================== *)
(* Back repair: refill a red suffix (KRight, or KOnly with a big prefix).     *)
(* ========================================================================== *)

Lemma repair_back_total :
  forall A (kd0 : kind) (k0 : nat) (body : cbody A) (k : kind)
         (p1 s1 : buffer (stored A)) (rest : cchain A),
    cbody_wf kd0 body ->
    node_kind (Node k p1 s1) = body_out_kind kd0 body ->
    node_sizes (chain_has_node rest) (Node k p1 s1) ->
    cnode_wf (Node k p1 s1) ->
    node_color (chain_has_node rest) (Node k p1 s1) = CR ->
    chain_ends_green rest ->
    chain_wf KOnly rest ->
    cbody_leveled k0 body ->
    cnode_leveled (k0 + body_depth body) (Node k p1 s1) ->
    chain_leveled (S (k0 + body_depth body)) rest ->
    (k = KRight \/ (k = KOnly /\ 8 <= length p1)) ->
    exists f,
      repair_back k body p1 s1 rest = Some f /\
      chain_wf kd0 f /\ chain_ends_green f /\ chain_leveled k0 f /\
      cchain_seq f = cchain_seq (CSingle (Pkt body (Node k p1 s1)) rest).
Proof.
  intros A kd0 k0 body k p1 s1 rest Hbw Hbk Hsz Hnw Hred Hgrest Hwrest
    Hbl Hnl Hrl Hkd.
  assert (Hne : rest <> CEmpty).
  { intros ->. cbn [chain_has_node] in Hred.
    rewrite node_color_no_child in Hred. discriminate. }
  assert (Hhc : chain_has_node rest = true)
    by (destruct rest; [congruence | reflexivity | reflexivity]).
  rewrite Hhc in Hred, Hsz.
  cbn [cnode_wf] in Hnw. destruct Hnw as [Hp1w Hs1w].
  cbn [cnode_leveled] in Hnl. destruct Hnl as [Hp1l Hs1l].
  assert (Hs15 : 5 <= length s1).
  { destruct Hkd as [-> | [-> Hp8]]; cbn [node_sizes] in Hsz.
    - destruct Hsz as [_ H2]. exact H2.
    - destruct Hsz as [[_ H2] | [Hc _]]; [exact H2 | discriminate]. }
  destruct (@eject_raw_J_total A (S (k0 + body_depth body)) rest
              Hwrest Hgrest Hrl Hne)
    as [d1' [cell [Hpop [Hcellw [Hcelll [Hwd1' [Hld1' Hseqp]]]]]]].
  unfold repair_back. rewrite Hpop.
  destruct cell as [g|b|p2 d2 s2].
  { cbn [stored_leveled] in Hcelll. discriminate. }
  - (* SSmall b: pure splice *)
    cbn [stored_wf] in Hcellw. destruct Hcellw as [Hb3 Hbw'].
    cbn [stored_leveled] in Hcelll.
    assert (Hvg : node_color (chain_has_node d1')
                    (Node k p1 (b ++ s1)) = CG).
    { destruct (chain_has_node d1').
      - rewrite node_color_measure.
        destruct Hkd as [-> | [-> Hp8]]; cbn [node_measure].
        + apply gyor_of_big. rewrite length_app. lia.
        + apply gyor_of_big. rewrite length_app.
          apply Nat.min_glb; lia.
      - apply node_color_no_child. }
    eexists. split; [reflexivity |].
    split; [| split; [| split]].
    + cbn [chain_wf].
      split; [exact Hbw |].
      split; [exact Hbk |].
      split.
      { destruct Hkd as [-> | [-> Hp8]]; cbn [node_sizes] in Hsz |- *.
        - destruct Hsz as [H1 _].
          split; [exact H1 | rewrite length_app; lia].
        - left. split; [lia | rewrite length_app; lia]. }
      split.
      { split; [exact Hp1w | exact (buf_all_wf_app Hbw' Hs1w)]. }
      split; [left; exact Hvg | exact Hwd1'].
    + cbn [chain_ends_green]. exact Hvg.
    + cbn [chain_leveled].
      split; [exact Hbl |].
      split.
      { cbn [cnode_leveled].
        split; [exact Hp1l | exact (buf_all_leveled_app Hcelll Hs1l)]. }
      exact Hld1'.
    + cbn [cchain_seq cpacket_seq].
      f_equal.
      rewrite !cnode_seq_eq, Hseqp.
      cbn [stored_seq]. seq_normalize.
  - (* SBig p2 d2 s2: splice the suffix, re-attach by SR concat *)
    cbn [stored_wf] in Hcellw.
    destruct Hcellw as [Hp23 [Hs23 [Hp2w [Hs2w Hwd2]]]].
    cbn [stored_leveled] in Hcelll.
    destruct Hcelll as [Hp2l [Hs2l Hld2]].
    assert (Hcellw2 : stored_wf (SSmall p2))
      by (cbn [stored_wf]; split; [exact Hp23 | exact Hp2w]).
    assert (Hwinj : chain_wf KOnly (inject_chain d1' (SSmall p2))).
    { apply (@inject_chain_preserves_wf A (SSmall p2) d1' KOnly);
        [congruence | intros _; reflexivity
        | exact Hcellw2 | exact Hwd1']. }
    destruct (cad_concat_sr Hwinj Hwd2) as [d3 [Hcc [Hwd3 Hseq3]]].
    rewrite Hcc.
    assert (Hld3 : chain_leveled (S (k0 + body_depth body)) d3).
    { apply (cad_concat_leveled
               (d:=inject_chain d1' (SSmall p2)) (e:=d2) (f:=d3));
        [| exact Hld2 | exact Hcc].
      apply (inject_chain_leveled (c:=d1') (s:=SSmall p2));
        [exact Hld1' |].
      cbn [stored_leveled]. exact Hp2l. }
    assert (Hvg : node_color (chain_has_node d3)
                    (Node k p1 (s2 ++ s1)) = CG).
    { destruct (chain_has_node d3).
      - rewrite node_color_measure.
        destruct Hkd as [-> | [-> Hp8]]; cbn [node_measure].
        + apply gyor_of_big. rewrite length_app. lia.
        + apply gyor_of_big. rewrite length_app.
          apply Nat.min_glb; lia.
      - apply node_color_no_child. }
    eexists. split; [reflexivity |].
    split; [| split; [| split]].
    + cbn [chain_wf].
      split; [exact Hbw |].
      split; [exact Hbk |].
      split.
      { destruct Hkd as [-> | [-> Hp8]]; cbn [node_sizes] in Hsz |- *.
        - destruct Hsz as [H1 _].
          split; [exact H1 | rewrite length_app; lia].
        - left. split; [lia | rewrite length_app; lia]. }
      split.
      { split; [exact Hp1w | exact (buf_all_wf_app Hs2w Hs1w)]. }
      split; [left; exact Hvg | exact Hwd3].
    + cbn [chain_ends_green]. exact Hvg.
    + cbn [chain_leveled].
      split; [exact Hbl |].
      split.
      { cbn [cnode_leveled].
        split; [exact Hp1l | exact (buf_all_leveled_app Hs2l Hs1l)]. }
      exact Hld3.
    + cbn [cchain_seq cpacket_seq].
      f_equal.
      rewrite !cnode_seq_eq, Hseqp.
      unfold cad_to_list in Hseq3. rewrite Hseq3.
      rewrite (inject_chain_seq (SSmall p2) Hwd1').
      cbn [stored_seq]. seq_normalize.
Qed.

(* ========================================================================== *)
(* The double-shrink rebundle: both root buffers lose one cell in one step,   *)
(* so the colour drops exactly one rank and the J child facts apply as in     *)
(* the single-shrink case.                                                     *)
(* ========================================================================== *)

Lemma popej_rebundle_total :
  forall A (k : nat) (pp' ss'' : buffer (stored A)) (a x : stored A)
         (child : cchain A),
    node_sizes true (Node KOnly (a :: pp') (ss'' ++ [x])) ->
    node_color (chain_has_node child)
      (Node KOnly (a :: pp') (ss'' ++ [x])) <> CR ->
    buf_stored_all_wf pp' -> buf_stored_all_wf ss'' ->
    buf_all_leveled k pp' -> buf_all_leveled k ss'' ->
    chain_wf KOnly child -> child <> CEmpty ->
    chain_leveled (S k) child ->
    child_color_facts
      (node_color (chain_has_node child)
         (Node KOnly (a :: pp') (ss'' ++ [x]))) child ->
    chain_wf KOnly (tree_of (Node KOnly pp' ss'') child) /\
    chain_leveled k (tree_of (Node KOnly pp' ss'') child) /\
    cchain_seq (tree_of (Node KOnly pp' ss'') child)
    = buf_stored_seq pp' ++ cchain_seq child ++ buf_stored_seq ss''.
Proof.
  intros A k pp' ss'' a x child Hsz Hnr Hpw Hsw Hpl Hsl Hcw Hne Hcl
    Hccf.
  assert (Hhc : chain_has_node child = true)
    by (destruct child; [congruence | reflexivity | reflexivity]).
  rewrite Hhc in Hnr, Hccf.
  rewrite node_color_measure in Hnr, Hccf.
  assert (Hm6 : 6 <= node_measure (Node KOnly (a :: pp') (ss'' ++ [x]))).
  { destruct (gyor_of (node_measure (Node KOnly (a :: pp') (ss'' ++ [x]))))
      eqn:Hold.
    - assert (H8 : 8 <= node_measure (Node KOnly (a :: pp') (ss'' ++ [x])))
        by exact (gyor_of_inv Hold). lia.
    - assert (H7 : node_measure (Node KOnly (a :: pp') (ss'' ++ [x])) = 7)
        by exact (gyor_of_inv Hold). lia.
    - assert (H6 : node_measure (Node KOnly (a :: pp') (ss'' ++ [x])) = 6)
        by exact (gyor_of_inv Hold). lia.
    - exfalso. apply Hnr. reflexivity. }
  assert (Hsz' : node_sizes true (Node KOnly pp' ss'')).
  { cbn [node_sizes] in Hsz |- *.
    destruct Hsz as [[H1 H2] | [Hcontra _]]; [| discriminate].
    left. cbn [node_measure] in Hm6.
    rewrite length_app in Hm6, H2. cbn [length] in Hm6, H2.
    split; lia. }
  assert (Hrcf' : root_color_facts (Node KOnly pp' ss'') child).
  { unfold root_color_facts. rewrite Hhc, node_color_measure.
    destruct (gyor_of (node_measure (Node KOnly pp' ss''))) eqn:Hnew.
    - exact I.
    - exact I.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct child as [|? ?|l r2]; [congruence | exact I |].
      destruct (gyor_of (node_measure (Node KOnly (a :: pp') (ss'' ++ [x]))))
        eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso.
        rewrite !length_app in Hold; cbn [length] in Hold, Hnew; lia.
      + cbn [child_color_facts cont_green] in Hccf. exact Hccf.
      + cbn [child_color_facts cont_green] in Hccf.
        destruct Hccf as [_ Hpk]. exact Hpk.
      + exfalso. apply Hnr. reflexivity.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct (gyor_of (node_measure (Node KOnly (a :: pp') (ss'' ++ [x]))))
        eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso.
        rewrite !length_app in Hold; cbn [length] in Hold, Hnew; lia.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso.
        rewrite !length_app in Hold; cbn [length] in Hold, Hnew; lia.
      + cbn [child_color_facts cont_green] in Hccf.
        destruct child as [|? ?|l r2]; [congruence | |].
        * destruct Hccf as [Hge _]. exact Hge.
        * destruct Hccf as [HgR HgL].
          split; [exact HgL | exact HgR].
      + exfalso. apply Hnr. reflexivity. }
  split; [| split].
  - apply tree_of_wf;
      [reflexivity
      | rewrite Hhc; exact Hsz'
      | split; [exact Hpw | exact Hsw]
      | exact Hcw
      | exact Hrcf'].
  - apply tree_of_leveled; [split; [exact Hpl | exact Hsl] | exact Hcl].
  - rewrite tree_of_seq, cnode_seq_eq. reflexivity.
Qed.
