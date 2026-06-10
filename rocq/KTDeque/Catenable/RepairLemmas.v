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

(* ========================================================================== *)
(* Dead-side recrowns: a drained pair component below its floor merges over   *)
(* the live sibling's peeled root.  The live root needs only chain_wf — its   *)
(* sr_facts key exactly the recrown colour (same one-sided measure).           *)
(* ========================================================================== *)

Lemma recrown_left_dead :
  forall A (k : nat) (lp ls : buffer (stored A)) (pr' : cpacket A)
         (rr' : cchain A),
    buf_stored_all_wf lp -> buf_stored_all_wf ls ->
    buf_all_leveled k lp -> buf_all_leveled k ls ->
    length ls = 2 -> length lp = 4 ->
    chain_wf KRight (CSingle pr' rr') ->
    chain_leveled k (CSingle pr' rr') ->
    exists t,
      match root_and_child pr' rr' with
      | (Node _ p2 s2, d2) =>
          Some (tree_of (Node KOnly (lp ++ ls ++ p2) s2) d2)
      end = Some t /\
      chain_wf KOnly t /\ chain_leveled k t /\
      cchain_seq t
      = buf_stored_seq lp ++ buf_stored_seq ls
        ++ cchain_seq (CSingle pr' rr').
Proof.
  intros A k lp ls pr' rr' Hlpw Hlsw Hlpl Hlsl Hls2 Hlp4 Hwf Hl.
  destruct (root_and_child pr' rr') as [[k2 p2 s2] d2] eqn:Hrc.
  pose proof (root_and_child_facts Hwf) as Hf.
  rewrite Hrc in Hf. cbn [fst snd] in Hf.
  destruct Hf as [Hk [Hsz [Hnw [Hcw Hrcf]]]].
  cbn [node_kind] in Hk. subst k2.
  cbn [node_sizes] in Hsz. destruct Hsz as [Hp22 Hs25].
  cbn [cnode_wf] in Hnw. destruct Hnw as [Hp2w Hs2w].
  pose proof (root_and_child_leveled Hl) as Hlf.
  rewrite Hrc in Hlf. cbn [fst snd] in Hlf.
  destruct Hlf as [Hnl Hdl].
  cbn [cnode_leveled] in Hnl. destruct Hnl as [Hp2l Hs2l].
  apply root_color_facts_sr in Hrcf.
  assert (Hnpw : buf_stored_all_wf (lp ++ ls ++ p2)).
  { apply buf_all_wf_app; [exact Hlpw |].
    apply buf_all_wf_app; [exact Hlsw | exact Hp2w]. }
  assert (Hnpl : buf_all_leveled k (lp ++ ls ++ p2)).
  { apply buf_all_leveled_app; [exact Hlpl |].
    apply buf_all_leveled_app; [exact Hlsl | exact Hp2l]. }
  assert (Hlen8 : length (lp ++ ls ++ p2) = 8)
    by (rewrite !length_app; lia).
  assert (Hseq0 : cchain_seq (CSingle pr' rr')
                  = buf_stored_seq p2 ++ cchain_seq d2
                    ++ buf_stored_seq s2).
  { rewrite (root_and_child_seq pr' rr'), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity. }
  destruct d2 as [|d2p d2r|d2l d2rr].
  - (* childless live root *)
    eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [lia | exact Hs25]
        | split; [exact Hnpw | exact Hs2w]
        | exact I
        | exact I].
    + apply tree_of_leveled; [split; [exact Hnpl | exact Hs2l] | exact I].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
  - (* rooted: sr-dispatch keyed at the live root's own colour *)
    assert (Hnewc : node_color (chain_has_node (CSingle d2p d2r))
              (Node KOnly (lp ++ ls ++ p2) s2) = gyor_of (length s2)).
    { cbn [chain_has_node]. rewrite node_color_measure.
      cbn [node_measure]. apply gyor_of_min_big. lia. }
    cbn [chain_has_node] in Hrcf.
    rewrite node_color_measure in Hrcf. cbn [node_measure] in Hrcf.
    eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [lia | exact Hs25]
        | split; [exact Hnpw | exact Hs2w]
        | exact Hcw
        | unfold root_color_facts; rewrite Hnewc;
          destruct (gyor_of (length s2)) eqn:Hg;
          [exact I | exact I | exact Hrcf | exact Hrcf]].
    + apply tree_of_leveled; [split; [exact Hnpl | exact Hs2l] | exact Hdl].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
  - assert (Hnewc : node_color (chain_has_node (CPair d2l d2rr))
              (Node KOnly (lp ++ ls ++ p2) s2) = gyor_of (length s2)).
    { cbn [chain_has_node]. rewrite node_color_measure.
      cbn [node_measure]. apply gyor_of_min_big. lia. }
    cbn [chain_has_node] in Hrcf.
    rewrite node_color_measure in Hrcf. cbn [node_measure] in Hrcf.
    eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [lia | exact Hs25]
        | split; [exact Hnpw | exact Hs2w]
        | exact Hcw
        | unfold root_color_facts; rewrite Hnewc;
          destruct (gyor_of (length s2)) eqn:Hg;
          [exact I | exact I | exact Hrcf | exact Hrcf]].
    + apply tree_of_leveled; [split; [exact Hnpl | exact Hs2l] | exact Hdl].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
Qed.

Lemma recrown_right_dead :
  forall A (k : nat) (rp rs : buffer (stored A)) (pl' : cpacket A)
         (rl' : cchain A),
    buf_stored_all_wf rp -> buf_stored_all_wf rs ->
    buf_all_leveled k rp -> buf_all_leveled k rs ->
    length rp = 2 -> length rs = 4 ->
    chain_wf KLeft (CSingle pl' rl') ->
    chain_leveled k (CSingle pl' rl') ->
    exists t,
      match root_and_child pl' rl' with
      | (Node _ p2 s2, d2) =>
          Some (tree_of (Node KOnly p2 (s2 ++ rp ++ rs)) d2)
      end = Some t /\
      chain_wf KOnly t /\ chain_leveled k t /\
      cchain_seq t
      = cchain_seq (CSingle pl' rl') ++ buf_stored_seq rp
        ++ buf_stored_seq rs.
Proof.
  intros A k rp rs pl' rl' Hrpw Hrsw Hrpl Hrsl Hrp2 Hrs4 Hwf Hl.
  destruct (root_and_child pl' rl') as [[k1 p2 s2] d2] eqn:Hrc.
  pose proof (root_and_child_facts Hwf) as Hf.
  rewrite Hrc in Hf. cbn [fst snd] in Hf.
  destruct Hf as [Hk [Hsz [Hnw [Hcw Hrcf]]]].
  cbn [node_kind] in Hk. subst k1.
  cbn [node_sizes] in Hsz. destruct Hsz as [Hp25 Hs22].
  cbn [cnode_wf] in Hnw. destruct Hnw as [Hp2w Hs2w].
  pose proof (root_and_child_leveled Hl) as Hlf.
  rewrite Hrc in Hlf. cbn [fst snd] in Hlf.
  destruct Hlf as [Hnl Hdl].
  cbn [cnode_leveled] in Hnl. destruct Hnl as [Hp2l Hs2l].
  apply root_color_facts_sr in Hrcf.
  assert (Hnsw : buf_stored_all_wf (s2 ++ rp ++ rs)).
  { apply buf_all_wf_app; [exact Hs2w |].
    apply buf_all_wf_app; [exact Hrpw | exact Hrsw]. }
  assert (Hnsl : buf_all_leveled k (s2 ++ rp ++ rs)).
  { apply buf_all_leveled_app; [exact Hs2l |].
    apply buf_all_leveled_app; [exact Hrpl | exact Hrsl]. }
  assert (Hlen8 : length (s2 ++ rp ++ rs) = 8)
    by (rewrite !length_app; lia).
  assert (Hseq0 : cchain_seq (CSingle pl' rl')
                  = buf_stored_seq p2 ++ cchain_seq d2
                    ++ buf_stored_seq s2).
  { rewrite (root_and_child_seq pl' rl'), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity. }
  destruct d2 as [|d2p d2r|d2l d2rr].
  - eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [exact Hp25 | lia]
        | split; [exact Hp2w | exact Hnsw]
        | exact I
        | exact I].
    + apply tree_of_leveled; [split; [exact Hp2l | exact Hnsl] | exact I].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
  - assert (Hnewc : node_color (chain_has_node (CSingle d2p d2r))
              (Node KOnly p2 (s2 ++ rp ++ rs)) = gyor_of (length p2)).
    { cbn [chain_has_node]. rewrite node_color_measure.
      cbn [node_measure]. apply gyor_of_min_big_r. lia. }
    cbn [chain_has_node] in Hrcf.
    rewrite node_color_measure in Hrcf. cbn [node_measure] in Hrcf.
    eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [exact Hp25 | lia]
        | split; [exact Hp2w | exact Hnsw]
        | exact Hcw
        | unfold root_color_facts; rewrite Hnewc;
          destruct (gyor_of (length p2)) eqn:Hg;
          [exact I | exact I | exact Hrcf | exact Hrcf]].
    + apply tree_of_leveled; [split; [exact Hp2l | exact Hnsl] | exact Hdl].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
  - assert (Hnewc : node_color (chain_has_node (CPair d2l d2rr))
              (Node KOnly p2 (s2 ++ rp ++ rs)) = gyor_of (length p2)).
    { cbn [chain_has_node]. rewrite node_color_measure.
      cbn [node_measure]. apply gyor_of_min_big_r. lia. }
    cbn [chain_has_node] in Hrcf.
    rewrite node_color_measure in Hrcf. cbn [node_measure] in Hrcf.
    eexists. split; [reflexivity |].
    split; [| split].
    + apply tree_of_wf;
        [reflexivity
        | cbn [chain_has_node node_sizes]; left; split; [exact Hp25 | lia]
        | split; [exact Hp2w | exact Hnsw]
        | exact Hcw
        | unfold root_color_facts; rewrite Hnewc;
          destruct (gyor_of (length p2)) eqn:Hg;
          [exact I | exact I | exact Hrcf | exact Hrcf]].
    + apply tree_of_leveled; [split; [exact Hp2l | exact Hnsl] | exact Hdl].
    + rewrite tree_of_seq, cnode_seq_eq, Hseq0. seq_normalize.
Qed.

(* ========================================================================== *)
(* drain_both: both end cells of a regular chain, plus a semiregular middle.  *)
(* ========================================================================== *)

Lemma drain_both_total :
  forall A (k : nat) (rest : cchain A),
    chain_wf KOnly rest -> chain_ends_green rest -> chain_leveled k rest ->
    rest <> CEmpty ->
    exists cellF ob mid,
      drain_both rest = Some (cellF, ob, mid) /\
      stored_wf cellF /\ stored_leveled k cellF /\
      chain_wf KOnly mid /\ chain_leveled k mid /\
      match ob with
      | Some cellB =>
          stored_wf cellB /\ stored_leveled k cellB /\
          cchain_seq rest
          = stored_seq cellF ++ cchain_seq mid ++ stored_seq cellB
      | None => cchain_seq rest = stored_seq cellF
      end.
Proof.
  intros A k rest Hwf Hg Hl Hne.
  destruct rest as [|p r|l r].
  { congruence. }
  - (* single: double-shrink the root *)
    cbn [drain_both].
    destruct (root_and_child p r) as [[kd pp ss] child] eqn:Hrc.
    cbn [fst snd].
    pose proof (root_and_child_facts Hwf) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [Hk [Hsz [Hnw [Hcw _]]]].
    cbn [node_kind] in Hk. subst kd.
    pose proof (root_and_child_leveled Hl) as Hlf.
    rewrite Hrc in Hlf. cbn [fst snd] in Hlf.
    destruct Hlf as [Hnl Hchl].
    cbn [cnode_wf] in Hnw. destruct Hnw as [Hppw Hssw].
    cbn [cnode_leveled] in Hnl. destruct Hnl as [Hppl Hssl].
    pose proof (root_not_red Hwf Hg) as Hnr.
    rewrite Hrc in Hnr. cbn [fst snd] in Hnr.
    pose proof (root_child_facts Hwf Hg) as Hccf.
    rewrite Hrc in Hccf. cbn [fst snd] in Hccf.
    assert (Hseq0 : cchain_seq (CSingle p r)
                    = buf_stored_seq pp ++ cchain_seq child
                      ++ buf_stored_seq ss).
    { rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
      rewrite cnode_seq_eq. reflexivity. }
    destruct child as [|cp cr|cl cr2].
    + (* childless root *)
      cbn [node_sizes chain_has_node] in Hsz.
      destruct pp as [|a pp'].
      * (* suffix-only root *)
        assert (Hss1 : 1 <= length ss).
        { destruct Hsz as [[H1 H2] | [_ [[Hpe H1] | [Hse H1]]]];
            [cbn in H1; lia | exact H1 | subst ss; cbn in H1; lia]. }
        destruct ss as [|b ss']; [cbn in Hss1; lia |].
        cbn in Hssw. destruct Hssw as [Hbw Hss'w].
        cbn in Hssl. destruct Hssl as [Hbl Hss'l].
        cbn [node_pop node_eject].
        destruct (rev ss') as [|x ss''] eqn:Hrs.
        { (* one-cell rest *)
          apply rev_nil_inv in Hrs. subst ss'.
          eexists. eexists. eexists.
          split; [reflexivity |].
          split; [exact Hbw |]. split; [exact Hbl |].
          split; [exact I |]. split; [exact I |].
          rewrite Hseq0. seq_normalize. }
        pose proof (rev_cons_inv Hrs) as Hb.
        assert (Hss'w2 : buf_stored_all_wf (rev ss'' ++ [x]))
          by (rewrite <- Hb; exact Hss'w).
        apply buf_all_wf_app_inv in Hss'w2.
        destruct Hss'w2 as [Hss''w Hxw']. cbn in Hxw'.
        destruct Hxw' as [Hxw _].
        assert (Hss'l2 : buf_all_leveled k (rev ss'' ++ [x]))
          by (rewrite <- Hb; exact Hss'l).
        apply buf_all_leveled_app_inv in Hss'l2.
        destruct Hss'l2 as [Hss''l Hxl']. cbn in Hxl'.
        destruct Hxl' as [Hxl _].
        destruct (@rebuild_childless_facts A k (Node KOnly [] (rev ss''))
                    ltac:(reflexivity)
                    ltac:(split; [exact I | exact Hss''w])
                    ltac:(split; [exact I | exact Hss''l]))
          as [Hw' [Hg' [Hl' Hs']]].
        eexists. eexists. eexists.
        split; [reflexivity |].
        split; [exact Hbw |]. split; [exact Hbl |].
        split; [exact Hw' |]. split; [exact Hl' |].
        split; [exact Hxw |]. split; [exact Hxl |].
        rewrite Hseq0, Hs', Hb.
        rewrite cnode_seq_eq. seq_normalize.
      * (* prefix head exists *)
        cbn in Hppw. destruct Hppw as [Haw Hpp'w].
        cbn in Hppl. destruct Hppl as [Hal Hpp'l].
        cbn [node_pop node_eject].
        destruct (rev ss) as [|x ss''] eqn:Hrs.
        { (* empty suffix: eject from the prefix tail *)
          apply rev_nil_inv in Hrs. subst ss.
          destruct (rev pp') as [|y pp''] eqn:Hrp.
          { (* one-cell rest *)
            apply rev_nil_inv in Hrp. subst pp'.
            eexists. eexists. eexists.
            split; [reflexivity |].
            split; [exact Haw |]. split; [exact Hal |].
            split; [exact I |]. split; [exact I |].
            rewrite Hseq0. seq_normalize. }
          pose proof (rev_cons_inv Hrp) as Hb.
          assert (Hpp'w2 : buf_stored_all_wf (rev pp'' ++ [y]))
            by (rewrite <- Hb; exact Hpp'w).
          apply buf_all_wf_app_inv in Hpp'w2.
          destruct Hpp'w2 as [Hpp''w Hyw']. cbn in Hyw'.
          destruct Hyw' as [Hyw _].
          assert (Hpp'l2 : buf_all_leveled k (rev pp'' ++ [y]))
            by (rewrite <- Hb; exact Hpp'l).
          apply buf_all_leveled_app_inv in Hpp'l2.
          destruct Hpp'l2 as [Hpp''l Hyl']. cbn in Hyl'.
          destruct Hyl' as [Hyl _].
          destruct (@rebuild_childless_facts A k
                      (Node KOnly (rev pp'') [])
                      ltac:(reflexivity)
                      ltac:(split; [exact Hpp''w | exact I])
                      ltac:(split; [exact Hpp''l | exact I]))
            as [Hw' [Hg' [Hl' Hs']]].
          eexists. eexists. eexists.
          split; [reflexivity |].
          split; [exact Haw |]. split; [exact Hal |].
          split; [exact Hw' |]. split; [exact Hl' |].
          split; [exact Hyw |]. split; [exact Hyl |].
          rewrite Hseq0, Hs', Hb.
          rewrite cnode_seq_eq. seq_normalize. }
        (* nonempty suffix *)
        pose proof (rev_cons_inv Hrs) as Hb.
        assert (Hssw2 : buf_stored_all_wf (rev ss'' ++ [x]))
          by (rewrite <- Hb; exact Hssw).
        apply buf_all_wf_app_inv in Hssw2.
        destruct Hssw2 as [Hss''w Hxw']. cbn in Hxw'.
        destruct Hxw' as [Hxw _].
        assert (Hssl2 : buf_all_leveled k (rev ss'' ++ [x]))
          by (rewrite <- Hb; exact Hssl).
        apply buf_all_leveled_app_inv in Hssl2.
        destruct Hssl2 as [Hss''l Hxl']. cbn in Hxl'.
        destruct Hxl' as [Hxl _].
        destruct (@rebuild_childless_facts A k
                    (Node KOnly pp' (rev ss''))
                    ltac:(reflexivity)
                    ltac:(split; [exact Hpp'w | exact Hss''w])
                    ltac:(split; [exact Hpp'l | exact Hss''l]))
          as [Hw' [Hg' [Hl' Hs']]].
        eexists. eexists. eexists.
        split; [reflexivity |].
        split; [exact Haw |]. split; [exact Hal |].
        split; [exact Hw' |]. split; [exact Hl' |].
        split; [exact Hxw |]. split; [exact Hxl |].
        rewrite Hseq0, Hs', Hb.
        rewrite cnode_seq_eq. seq_normalize.
    + (* with child, single: two-sided root, both shrinks *)
      cbn [node_sizes] in Hsz.
      pose proof Hsz as Hsz0.
      destruct Hsz0 as [[H1 H2] | [Hcontra _]]; [| discriminate].
      destruct pp as [|a pp']; [cbn in H1; lia |].
      cbn in Hppw. destruct Hppw as [Haw Hpp'w].
      cbn in Hppl. destruct Hppl as [Hal Hpp'l].
      cbn [node_pop node_eject].
      destruct (rev ss) as [|x ss''] eqn:Hrs.
      { apply rev_nil_inv in Hrs. subst ss. cbn in H2. lia. }
      pose proof (rev_cons_inv Hrs) as Hb.
      assert (Hssw2 : buf_stored_all_wf (rev ss'' ++ [x]))
        by (rewrite <- Hb; exact Hssw).
      apply buf_all_wf_app_inv in Hssw2.
      destruct Hssw2 as [Hss''w Hxw']. cbn in Hxw'.
      destruct Hxw' as [Hxw _].
      assert (Hssl2 : buf_all_leveled k (rev ss'' ++ [x]))
        by (rewrite <- Hb; exact Hssl).
      apply buf_all_leveled_app_inv in Hssl2.
      destruct Hssl2 as [Hss''l Hxl']. cbn in Hxl'.
      destruct Hxl' as [Hxl _].
      rewrite Hb in Hsz, Hnr, Hccf, Hseq0.
      destruct (@popej_rebundle_total A k pp' (rev ss'') a x
                  (CSingle cp cr) Hsz Hnr Hpp'w Hss''w Hpp'l Hss''l
                  Hcw ltac:(discriminate) Hchl Hccf)
        as [Hw' [Hl' Hs']].
      eexists. eexists. eexists.
      split; [reflexivity |].
      split; [exact Haw |]. split; [exact Hal |].
      split; [exact Hw' |]. split; [exact Hl' |].
      split; [exact Hxw |]. split; [exact Hxl |].
      rewrite Hseq0, Hs'. seq_normalize.
    + (* with child, pair *)
      cbn [node_sizes] in Hsz.
      pose proof Hsz as Hsz0.
      destruct Hsz0 as [[H1 H2] | [Hcontra _]]; [| discriminate].
      destruct pp as [|a pp']; [cbn in H1; lia |].
      cbn in Hppw. destruct Hppw as [Haw Hpp'w].
      cbn in Hppl. destruct Hppl as [Hal Hpp'l].
      cbn [node_pop node_eject].
      destruct (rev ss) as [|x ss''] eqn:Hrs.
      { apply rev_nil_inv in Hrs. subst ss. cbn in H2. lia. }
      pose proof (rev_cons_inv Hrs) as Hb.
      assert (Hssw2 : buf_stored_all_wf (rev ss'' ++ [x]))
        by (rewrite <- Hb; exact Hssw).
      apply buf_all_wf_app_inv in Hssw2.
      destruct Hssw2 as [Hss''w Hxw']. cbn in Hxw'.
      destruct Hxw' as [Hxw _].
      assert (Hssl2 : buf_all_leveled k (rev ss'' ++ [x]))
        by (rewrite <- Hb; exact Hssl).
      apply buf_all_leveled_app_inv in Hssl2.
      destruct Hssl2 as [Hss''l Hxl']. cbn in Hxl'.
      destruct Hxl' as [Hxl _].
      rewrite Hb in Hsz, Hnr, Hccf, Hseq0.
      destruct (@popej_rebundle_total A k pp' (rev ss'') a x
                  (CPair cl cr2) Hsz Hnr Hpp'w Hss''w Hpp'l Hss''l
                  Hcw ltac:(discriminate) Hchl Hccf)
        as [Hw' [Hl' Hs']].
      eexists. eexists. eexists.
      split; [reflexivity |].
      split; [exact Haw |]. split; [exact Hal |].
      split; [exact Hw' |]. split; [exact Hl' |].
      split; [exact Hxw |]. split; [exact Hxl |].
      rewrite Hseq0, Hs'. seq_normalize.
  - (* pair: drain the components independently *)
    cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hlw Hrw]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    cbn [chain_leveled] in Hl. destruct Hl as [Hll Hlr].
    destruct l as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct r as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    destruct (pop_raw_left_total Hlw Hgl Hll)
      as [cF [l' [HpopL [HFw [HFl [Hll' [HseqL HdisjL]]]]]]].
    destruct (eject_raw_right_total Hrw Hgr Hlr)
      as [r' [cB [HpopR [HBw [HBl [Hlr' [HseqR HdisjR]]]]]]].
    cbn [drain_both]. rewrite HpopL, HpopR.
    rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
    destruct HdisjL as
      [[lp [ls [-> [Hlpw [Hlsw [Hlpl [Hlsl [Hls2 [Hlp4 HseqCL]]]]]]]]]
       | [Hwfl' HguardL]];
      destruct HdisjR as
      [[rp [rs [-> [Hrpw [Hrsw [Hrpl [Hrsl [Hrp2 [Hrs4 HseqCR]]]]]]]]]
       | [Hwfr' HguardR]].
    + (* both childless *)
      destruct ((length lp <? 5) || (length rs <? 5)) eqn:Hsmall.
      * (* merge into one childless only node *)
        eexists. eexists. eexists.
        split; [reflexivity |].
        split; [exact HFw |]. split; [exact HFl |].
        split.
        { split; [exact I |].
          split; [reflexivity |].
          split.
          { left. split; rewrite length_app; lia. }
          split.
          { split; [exact (buf_all_wf_app Hlpw Hlsw)
                   | exact (buf_all_wf_app Hrpw Hrsw)]. }
          split; [left; reflexivity | exact I]. }
        split.
        { cbn [chain_leveled cbody_leveled body_depth].
          rewrite Nat.add_0_r.
          split; [exact I |].
          split; [| exact I].
          cbn [cnode_leveled].
          split; [exact (buf_all_leveled_app Hlpl Hlsl)
                 | exact (buf_all_leveled_app Hrpl Hrsl)]. }
        split; [exact HBw |]. split; [exact HBl |].
        rewrite HseqL, HseqR, HseqCL, HseqCR.
        cbn [cchain_seq cpacket_seq cbody_seq].
        rewrite cnode_seq_eq. seq_normalize.
      * (* both floors hold: keep the pair *)
        apply Bool.orb_false_elim in Hsmall.
        destruct Hsmall as [Hlp5 Hrs5].
        apply Nat.ltb_ge in Hlp5. apply Nat.ltb_ge in Hrs5.
        eexists. eexists. eexists.
        split; [reflexivity |].
        split; [exact HFw |]. split; [exact HFl |].
        split.
        { cbn [chain_wf is_single].
          split; [reflexivity |]. split; [reflexivity |].
          split.
          { split; [exact I |].
            split; [reflexivity |].
            split.
            { cbn [chain_has_node node_sizes].
              split; [exact Hlp5 | exact Hls2]. }
            split; [split; [exact Hlpw | exact Hlsw] |].
            split; [left; reflexivity | exact I]. }
          { split; [exact I |].
            split; [reflexivity |].
            split.
            { cbn [chain_has_node node_sizes].
              split; [exact Hrp2 | exact Hrs5]. }
            split; [split; [exact Hrpw | exact Hrsw] |].
            split; [left; reflexivity | exact I]. } }
        split.
        { cbn [chain_leveled].
          split; [exact Hll' | exact Hlr']. }
        split; [exact HBw |]. split; [exact HBl |].
        rewrite HseqL, HseqR.
        rewrite (cchain_seq_pair
          (CSingle (Pkt BHole (Node KLeft lp ls)) CEmpty)
          (CSingle (Pkt BHole (Node KRight rp rs)) CEmpty)).
        seq_normalize.
    + (* left childless, right alive *)
      destruct (length lp <? 5) eqn:Hlp5.
      * (* left dead: recrown over the right's peeled root *)
        apply Nat.ltb_lt in Hlp5.
        assert (Hlp4e : length lp = 4) by lia.
        destruct r' as [|pr' rr'|? ?]; [exfalso; exact HguardR |
          | exfalso; exact HguardR].
        destruct pr' as [bd0 n0]. destruct n0 as [kn0 pn0 sn0].
        destruct bd0; destruct rr';
          try (exfalso; exact HguardR);
          (destruct (recrown_left_dead Hlpw Hlsw Hlpl Hlsl Hls2 Hlp4e
                       Hwfr' Hlr') as [t [Hmk [Hwt [Hlt Hseqt]]]];
           lazymatch type of Hmk with
           | match ?rc with _ => _ end = _ =>
               destruct rc as [[k2 p2 s2] d2]
           end;
           injection Hmk as Hmk2; subst t;
           eexists; eexists; eexists;
           split; [reflexivity |];
           split; [exact HFw |]; split; [exact HFl |];
           split; [exact Hwt |]; split; [exact Hlt |];
           split; [exact HBw |]; split; [exact HBl |];
           rewrite HseqL, HseqR, HseqCL, Hseqt; seq_normalize).
      * (* left floor holds: keep the pair *)
        apply Nat.ltb_ge in Hlp5.
        destruct r' as [|pr' rr'|? ?]; [exfalso; exact HguardR |
          | exfalso; exact HguardR].
        destruct pr' as [bd0 n0]. destruct n0 as [kn0 pn0 sn0].
        destruct bd0; destruct rr';
          try (exfalso; exact HguardR);
          (eexists; eexists; eexists;
           split; [reflexivity |];
           split; [exact HFw |]; split; [exact HFl |];
           split;
             [cbn [chain_wf is_single];
              split; [reflexivity |]; split; [reflexivity |];
              split;
                [split; [exact I |];
                 split; [reflexivity |];
                 split;
                   [cbn [chain_has_node node_sizes];
                    split; [exact Hlp5 | exact Hls2] |];
                 split; [split; [exact Hlpw | exact Hlsw] |];
                 split; [left; reflexivity | exact I]
                | exact Hwfr'] |];
           split;
             [cbn [chain_leveled]; split; [exact Hll' | exact Hlr'] |];
           split; [exact HBw |]; split; [exact HBl |];
           rewrite HseqL, HseqR;
           match goal with
           | |- _ = _ ++ cchain_seq (CPair ?a ?b) ++ _ =>
               rewrite (cchain_seq_pair a b)
           end;
           seq_normalize).
    + (* left alive, right childless *)
      destruct (length rs <? 5) eqn:Hrs5.
      * apply Nat.ltb_lt in Hrs5.
        assert (Hrs4e : length rs = 4) by lia.
        destruct l' as [|pl' rl'|? ?]; [exfalso; exact HguardL |
          | exfalso; exact HguardL].
        destruct pl' as [bd0 n0]. destruct n0 as [kn0 pn0 sn0].
        destruct bd0; destruct rl';
          try (exfalso; exact HguardL);
          (destruct (recrown_right_dead Hrpw Hrsw Hrpl Hrsl Hrp2 Hrs4e
                       Hwfl' Hll') as [t [Hmk [Hwt [Hlt Hseqt]]]];
           lazymatch type of Hmk with
           | match ?rc with _ => _ end = _ =>
               destruct rc as [[k1 p2 s2] d2]
           end;
           injection Hmk as Hmk2; subst t;
           eexists; eexists; eexists;
           split; [reflexivity |];
           split; [exact HFw |]; split; [exact HFl |];
           split; [exact Hwt |]; split; [exact Hlt |];
           split; [exact HBw |]; split; [exact HBl |];
           rewrite HseqL, HseqR, HseqCR, Hseqt; seq_normalize).
      * apply Nat.ltb_ge in Hrs5.
        destruct l' as [|pl' rl'|? ?]; [exfalso; exact HguardL |
          | exfalso; exact HguardL].
        destruct pl' as [bd0 n0]. destruct n0 as [kn0 pn0 sn0].
        destruct bd0; destruct rl';
          try (exfalso; exact HguardL);
          (eexists; eexists; eexists;
           split; [reflexivity |];
           split; [exact HFw |]; split; [exact HFl |];
           split;
             [cbn [chain_wf is_single];
              split; [reflexivity |]; split; [reflexivity |];
              split;
                [exact Hwfl'
                | split; [exact I |];
                  split; [reflexivity |];
                  split;
                    [cbn [chain_has_node node_sizes];
                     split; [exact Hrp2 | exact Hrs5] |];
                  split; [split; [exact Hrpw | exact Hrsw] |];
                  split; [left; reflexivity | exact I]] |];
           split;
             [cbn [chain_leveled]; split; [exact Hll' | exact Hlr'] |];
           split; [exact HBw |]; split; [exact HBl |];
           rewrite HseqL, HseqR;
           match goal with
           | |- _ = _ ++ cchain_seq (CPair ?a ?b) ++ _ =>
               rewrite (cchain_seq_pair a b)
           end;
           seq_normalize).
    + (* both alive: keep the pair *)
      destruct l' as [|pl' rl'|? ?]; [exfalso; exact HguardL |
        | exfalso; exact HguardL].
      destruct r' as [|pr' rr'|? ?]; [exfalso; exact HguardR |
        | exfalso; exact HguardR].
      destruct pl' as [bdl nl]. destruct nl as [knl pnl snl].
      destruct pr' as [bdr nr]. destruct nr as [knr pnr snr].
      destruct bdl; destruct rl'; try (exfalso; exact HguardL);
        (destruct bdr; destruct rr'; try (exfalso; exact HguardR);
         (eexists; eexists; eexists;
          split; [reflexivity |];
          split; [exact HFw |]; split; [exact HFl |];
          split;
            [cbn [chain_wf is_single];
             split; [reflexivity |]; split; [reflexivity |];
             split; [exact Hwfl' | exact Hwfr'] |];
          split;
            [cbn [chain_leveled]; split; [exact Hll' | exact Hlr'] |];
          split; [exact HBw |]; split; [exact HBl |];
          rewrite HseqL, HseqR;
          match goal with
          | |- _ = _ ++ cchain_seq (CPair ?a ?b) ++ _ =>
              rewrite (cchain_seq_pair a b)
          end;
          seq_normalize)).
Qed.
