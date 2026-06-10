(** * KTDeque.Catenable.PopLemmas — pop_raw/eject_raw shape lemmas (Phase 4b).

    Piece (B) of the pop/eject campaign (SESSION_STATE map v2): on a regular
    leveled input, [pop_raw] is total, pops a level-k cell (SGround at the
    top), and returns a SEMIREGULAR leveled remainder whose new terminal is
    green-or-red-with-green-child — the red case being exactly what
    [repair_packet] consumes.  The recursion depth of [pop_raw] is one (a
    pair recurses into its single LEFT component), so the lemmas are stated
    per shape: KOnly singles (top and repair-level pops) and KLeft singles
    (the pair component). *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas
  ConcatLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Colour-measure inversions.                                                  *)
(* ========================================================================== *)

Lemma gyor_of_inv :
  forall m g,
    gyor_of m = g ->
    match g with
    | CG => 8 <= m | CY => m = 7 | CO => m = 6 | CR => m <= 5
    end.
Proof.
  intros m g <-. unfold gyor_of.
  destruct (8 <=? m) eqn:H8; [apply Nat.leb_le in H8; exact H8 |].
  apply Nat.leb_gt in H8.
  destruct (m =? 7) eqn:H7; [apply Nat.eqb_eq in H7; exact H7 |].
  apply Nat.eqb_neq in H7.
  destruct (m =? 6) eqn:H6; [apply Nat.eqb_eq in H6; exact H6 |].
  apply Nat.eqb_neq in H6. lia.
Qed.

(** Under a green top path the root (packet head) is never red: a BHole
    head IS the green terminal; body heads are yellow/orange by the body
    discipline. *)
Lemma root_not_red :
  forall A (kd : kind) (p : cpacket A) (rest : cchain A),
    chain_wf kd (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    node_color (chain_has_node (snd (root_and_child p rest)))
      (fst (root_and_child p rest)) <> CR.
Proof.
  intros A kd [b n] rest Hwf Hg.
  cbn [chain_wf] in Hwf.
  cbn [chain_ends_green] in Hg.
  destruct b as [|m b'|m b' rc|m lc b']; cbn [root_and_child fst snd].
  - rewrite Hg. discriminate.
  - destruct Hwf as [Hb _]. cbn [cbody_wf] in Hb.
    destruct Hb as [_ [_ [_ [Hcol _]]]].
    cbn [chain_has_node].
    destruct Hcol as [Hc|Hc]; rewrite Hc; discriminate.
  - destruct Hwf as [Hb _]. cbn [cbody_wf] in Hb.
    destruct Hb as [_ [_ [_ [Hcol _]]]].
    cbn [chain_has_node]. rewrite Hcol. discriminate.
  - destruct Hwf as [Hb _]. cbn [cbody_wf] in Hb.
    destruct Hb as [_ [_ [_ [Hcol _]]]].
    cbn [chain_has_node]. rewrite Hcol. discriminate.
Qed.

(* ========================================================================== *)
(* rebuild_childless: a popped childless KOnly node rebuilds to a legal       *)
(* (green) childless tree with the same sequence.                              *)
(* ========================================================================== *)

Lemma rebuild_childless_facts :
  forall A (k : nat) (n : cnode A),
    node_kind n = KOnly ->
    cnode_wf n -> cnode_leveled k n ->
    chain_wf KOnly (rebuild_childless n) /\
    chain_ends_green (rebuild_childless n) /\
    chain_leveled k (rebuild_childless n) /\
    cchain_seq (rebuild_childless n) = cnode_seq n [].
Proof.
  intros A k [kd p s] Hk Hw Hl.
  cbn [node_kind] in Hk. subst kd.
  cbn [cnode_wf] in Hw. destruct Hw as [Hpw Hsw].
  cbn [cnode_leveled] in Hl. destruct Hl as [Hpl Hsl].
  unfold rebuild_childless.
  destruct p as [|a p'].
  - destruct s as [|b s'].
    + (* both empty: CEmpty *)
      repeat split; reflexivity.
    + (* one-sided, suffix only *)
      split; [| split; [| split]].
      * split; [exact I |].
        split; [reflexivity |].
        split.
        { right. split; [reflexivity |].
          left. split; [reflexivity | cbn [length]; lia]. }
        split; [split; [exact I | exact Hsw] |].
        split; [left; reflexivity | exact I].
      * cbn [chain_ends_green chain_has_node].
        apply node_color_no_child.
      * cbn [chain_leveled cbody_leveled body_depth].
        rewrite Nat.add_0_r.
        split; [exact I |].
        split; [| exact I].
        cbn [cnode_leveled]. split; [exact I | exact Hsl].
      * cbn [cchain_seq cpacket_seq cbody_seq]. reflexivity.
  - destruct s as [|b s'].
    + (* one-sided, prefix only *)
      split; [| split; [| split]].
      * split; [exact I |].
        split; [reflexivity |].
        split.
        { right. split; [reflexivity |].
          right. split; [reflexivity | cbn [length]; lia]. }
        split; [split; [exact Hpw | exact I] |].
        split; [left; reflexivity | exact I].
      * cbn [chain_ends_green chain_has_node].
        apply node_color_no_child.
      * cbn [chain_leveled cbody_leveled body_depth].
        rewrite Nat.add_0_r.
        split; [exact I |].
        split; [| exact I].
        cbn [cnode_leveled]. split; [exact Hpl | exact I].
      * cbn [cchain_seq cpacket_seq cbody_seq]. reflexivity.
    + (* two-sided: merge if a floor broke, else keep *)
      destruct ((length (a :: p') <? 5) || (length (b :: s') <? 5))
        eqn:Hcond.
      * (* merged one-sided *)
        split; [| split; [| split]].
        -- split; [exact I |].
           split; [reflexivity |].
           split.
           { right. split; [reflexivity |].
             right. split; [reflexivity | rewrite length_app; cbn; lia]. }
           split;
             [split; [exact (buf_all_stored_wf_app (a:=a::p') (b:=b::s') Hpw Hsw) | exact I] |].
           split; [left; reflexivity | exact I].
        -- cbn [chain_ends_green chain_has_node].
           apply node_color_no_child.
        -- cbn [chain_leveled cbody_leveled body_depth].
           rewrite Nat.add_0_r.
           split; [exact I |].
           split; [| exact I].
           cbn [cnode_leveled].
           split; [exact (buf_all_leveled_app (a:=a::p') (b:=b::s') Hpl Hsl) | exact I].
        -- rewrite single_node_seq.
           rewrite cnode_seq_eq. seq_normalize.
      * (* kept two-sided: the if-condition gives both floors *)
        split; [| split; [| split]].
        -- split; [exact I |].
           split; [reflexivity |].
           split.
           { apply orb_false_iff in Hcond. destruct Hcond as [H1 H2].
             apply Nat.ltb_ge in H1. apply Nat.ltb_ge in H2.
             left. split; [exact H1 | exact H2]. }
           split; [split; [exact Hpw | exact Hsw] |].
           split; [left; reflexivity | exact I].
        -- cbn [chain_ends_green chain_has_node].
           apply node_color_no_child.
        -- cbn [chain_leveled cbody_leveled body_depth].
           rewrite Nat.add_0_r.
           split; [exact I |].
           split; [| exact I].
           cbn [cnode_leveled]. split; [exact Hpl | exact Hsl].
        -- rewrite single_node_seq.
           rewrite cnode_seq_eq. seq_normalize.
Qed.

(* ========================================================================== *)
(* The with-child pop rebundle: popping one cell off a non-red rooted node    *)
(* keeps semiregularity.  The new root drops at most one colour rank, so its  *)
(* CO/CR obligations are paid by the OLD root's child facts (CO's cont for    *)
(* CR's full greenness, CY's cont for CO's parked left).                       *)
(* ========================================================================== *)

Lemma pop_rebundle_total :
  forall A (k : nat) (kd : kind) (pp' ss : buffer (stored A))
         (a : stored A) (child : cchain A),
    (kd = KOnly \/ kd = KLeft) ->
    node_sizes true (Node kd (a :: pp') ss) ->
    node_color (chain_has_node child) (Node kd (a :: pp') ss) <> CR ->
    buf_stored_all_wf pp' -> buf_stored_all_wf ss ->
    buf_all_leveled k pp' -> buf_all_leveled k ss ->
    chain_wf KOnly child -> child <> CEmpty ->
    chain_leveled (S k) child ->
    child_color_facts
      (node_color (chain_has_node child) (Node kd (a :: pp') ss)) child ->
    chain_wf kd (tree_of (Node kd pp' ss) child) /\
    chain_leveled k (tree_of (Node kd pp' ss) child) /\
    cchain_seq (tree_of (Node kd pp' ss) child)
    = buf_stored_seq pp' ++ cchain_seq child ++ buf_stored_seq ss.
Proof.
  intros A k kd pp' ss a child Hkd Hsz Hnr Hpw Hsw Hpl Hsl Hcw Hne Hcl
    Hccf.
  assert (Hhc : chain_has_node child = true)
    by (destruct child; [congruence | reflexivity | reflexivity]).
  rewrite Hhc in Hnr, Hccf.
  rewrite node_color_measure in Hnr, Hccf.
  assert (Hm6 : 6 <= node_measure (Node kd (a :: pp') ss)).
  { destruct (gyor_of (node_measure (Node kd (a :: pp') ss))) eqn:Hold.
    - assert (H8 : 8 <= node_measure (Node kd (a :: pp') ss))
        by exact (gyor_of_inv Hold). lia.
    - assert (H7 : node_measure (Node kd (a :: pp') ss) = 7)
        by exact (gyor_of_inv Hold). lia.
    - assert (H6 : node_measure (Node kd (a :: pp') ss) = 6)
        by exact (gyor_of_inv Hold). lia.
    - exfalso. apply Hnr. reflexivity. }
  assert (Hsz' : node_sizes true (Node kd pp' ss)).
  { destruct Hkd as [-> | ->]; cbn [node_sizes] in Hsz |- *.
    - destruct Hsz as [[H1 H2] | [Hcontra _]]; [| discriminate].
      left. cbn [node_measure length] in Hm6. split; lia.
    - destruct Hsz as [H1 H2]. split; [| exact H2].
      cbn [node_measure length] in Hm6. lia. }
  assert (Hrcf' : root_color_facts (Node kd pp' ss) child).
  { unfold root_color_facts. rewrite Hhc, node_color_measure.
    destruct (gyor_of (node_measure (Node kd pp' ss))) eqn:Hnew.
    - exact I.
    - exact I.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct child as [|? ?|l r2]; [congruence | exact I |].
      destruct (gyor_of (node_measure (Node kd (a :: pp') ss))) eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure length] in Hold, Hnew; lia.
      + cbn [child_color_facts cont_green] in Hccf. exact Hccf.
      + cbn [child_color_facts cont_green] in Hccf.
        destruct Hccf as [_ Hpk]. exact Hpk.
      + exfalso. apply Hnr. reflexivity.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct (gyor_of (node_measure (Node kd (a :: pp') ss))) eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure length] in Hold, Hnew; lia.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure length] in Hold, Hnew; lia.
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
(* pop_raw on a KOnly single tree: total, level-k cell, semiregular leveled    *)
(* remainder, exact sequence.                                                  *)
(* ========================================================================== *)

Lemma pop_raw_only_total :
  forall A (k : nat) (p : cpacket A) (rest : cchain A),
    chain_wf KOnly (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    chain_leveled k (CSingle p rest) ->
    exists x c',
      pop_raw (CSingle p rest) = Some (x, c') /\
      stored_wf x /\ stored_leveled k x /\
      chain_wf KOnly c' /\
      chain_leveled k c' /\
      cchain_seq (CSingle p rest) = stored_seq x ++ cchain_seq c'.
Proof.
  intros A k p r Hwf Hg Hl.
  cbn [pop_raw].
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
  - (* childless root *)
    cbn [node_sizes chain_has_node] in Hsz.
    destruct pp as [|a pp'].
    + (* one-sided, pop the suffix head *)
      assert (Hss1 : 1 <= length ss).
      { destruct Hsz as [[H1 H2] | [_ [[_ H1] | [Hse H1]]]];
          [cbn in H1; lia | exact H1 |].
        subst ss. cbn in H1. lia. }
      destruct ss as [|b ss']; [cbn in Hss1; lia |].
      cbn in Hssw. destruct Hssw as [Hbw Hss'w].
      cbn in Hssl. destruct Hssl as [Hbl Hss'l].
      destruct (@rebuild_childless_facts A k (Node KOnly [] ss')
                  ltac:(reflexivity)
                  ltac:(split; [exact I | exact Hss'w])
                  ltac:(split; [exact I | exact Hss'l]))
        as [Hw' [Hg' [Hl' Hs']]].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hbw |]. split; [exact Hbl |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs'.
      rewrite cnode_seq_eq. seq_normalize.
    + (* two-sided or prefix-only: pop the prefix head *)
      cbn in Hppw. destruct Hppw as [Haw Hpp'w].
      cbn in Hppl. destruct Hppl as [Hal Hpp'l].
      destruct (@rebuild_childless_facts A k (Node KOnly pp' ss)
                  ltac:(reflexivity)
                  ltac:(split; [exact Hpp'w | exact Hssw])
                  ltac:(split; [exact Hpp'l | exact Hssl]))
        as [Hw' [Hg' [Hl' Hs']]].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Haw |]. split; [exact Hal |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs'.
      rewrite cnode_seq_eq. seq_normalize.
  - (* with child: single *)
    cbn [node_sizes] in Hsz.
    destruct Hsz as [[H1 H2] | [Hcontra _]]; [| discriminate].
    destruct pp as [|a pp']; [cbn in H1; lia |].
    cbn in Hppw. destruct Hppw as [Haw Hpp'w].
    cbn in Hppl. destruct Hppl as [Hal Hpp'l].
    destruct (@pop_rebundle_total A k KOnly pp' ss a (CSingle cp cr)
                ltac:(left; reflexivity)
                ltac:(cbn [node_sizes]; left; split; [exact H1 | exact H2])
                Hnr Hpp'w Hssw Hpp'l Hssl Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Haw |]. split; [exact Hal |].
    split; [exact Hw' |]. split; [exact Hl' |].
    rewrite Hseq0, Hs'. seq_normalize.
  - (* with child: pair *)
    cbn [node_sizes] in Hsz.
    destruct Hsz as [[H1 H2] | [Hcontra _]]; [| discriminate].
    destruct pp as [|a pp']; [cbn in H1; lia |].
    cbn in Hppw. destruct Hppw as [Haw Hpp'w].
    cbn in Hppl. destruct Hppl as [Hal Hpp'l].
    destruct (@pop_rebundle_total A k KOnly pp' ss a (CPair cl cr2)
                ltac:(left; reflexivity)
                ltac:(cbn [node_sizes]; left; split; [exact H1 | exact H2])
                Hnr Hpp'w Hssw Hpp'l Hssl Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Haw |]. split; [exact Hal |].
    split; [exact Hw' |]. split; [exact Hl' |].
    rewrite Hseq0, Hs'. seq_normalize.
Qed.

(* ========================================================================== *)
(* pop_raw on a KLeft single (a pair's left component): same as the KOnly     *)
(* case except the childless remainder is reported shape-explicitly — the     *)
(* pair parent dispatches on it (keep if the floor holds, collapse if not).   *)
(* ========================================================================== *)

Lemma pop_raw_left_total :
  forall A (k : nat) (p : cpacket A) (rest : cchain A),
    chain_wf KLeft (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    chain_leveled k (CSingle p rest) ->
    exists x c',
      pop_raw (CSingle p rest) = Some (x, c') /\
      stored_wf x /\ stored_leveled k x /\
      chain_leveled k c' /\
      cchain_seq (CSingle p rest) = stored_seq x ++ cchain_seq c' /\
      ((exists lp ls,
          c' = CSingle (Pkt BHole (Node KLeft lp ls)) CEmpty /\
          buf_stored_all_wf lp /\ buf_stored_all_wf ls /\
          buf_all_leveled k lp /\ buf_all_leveled k ls /\
          length ls = 2 /\ 4 <= length lp /\
          cchain_seq c' = buf_stored_seq lp ++ buf_stored_seq ls)
       \/ (chain_wf KLeft c' /\
           match c' with
           | CSingle (Pkt BHole _) CEmpty => False
           | CSingle _ _ => True
           | _ => False
           end)).
Proof.
  intros A k p r Hwf Hg Hl.
  cbn [pop_raw].
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
  cbn [node_sizes] in Hsz. destruct Hsz as [Hp5 Hs2].
  destruct pp as [|a pp']; [cbn in Hp5; lia |].
  cbn in Hppw. destruct Hppw as [Haw Hpp'w].
  cbn in Hppl. destruct Hppl as [Hal Hpp'l].
  destruct child as [|cp cr|cl cr2].
  - (* childless: rebuild keeps the KLeft node — report the shape *)
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Haw |]. split; [exact Hal |].
    assert (Hrb : rebuild_childless (Node KLeft pp' ss)
                  = CSingle (Pkt BHole (Node KLeft pp' ss)) CEmpty).
    { unfold rebuild_childless.
      destruct pp' as [|? ?]; destruct ss as [|? ?];
        try reflexivity.
      cbn [length] in Hs2. lia. }
    rewrite Hrb.
    split.
    { cbn [chain_leveled cbody_leveled body_depth].
      rewrite Nat.add_0_r.
      split; [exact I |].
      split; [| exact I].
      cbn [cnode_leveled]. split; [exact Hpp'l | exact Hssl]. }
    split.
    { rewrite Hseq0.
      cbn [cchain_seq cpacket_seq cbody_seq].
      rewrite cnode_seq_eq. seq_normalize. }
    left. exists pp', ss.
    split; [reflexivity |].
    split; [exact Hpp'w |]. split; [exact Hssw |].
    split; [exact Hpp'l |]. split; [exact Hssl |].
    split; [exact Hs2 |].
    split; [cbn [length] in Hp5; lia |].
    cbn [cchain_seq cpacket_seq cbody_seq].
    rewrite cnode_seq_eq. seq_normalize.
  - (* with child: single *)
    destruct (@pop_rebundle_total A k KLeft pp' ss a (CSingle cp cr)
                ltac:(right; reflexivity)
                ltac:(cbn [node_sizes]; split; [exact Hp5 | exact Hs2])
                Hnr Hpp'w Hssw Hpp'l Hssl Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Haw |]. split; [exact Hal |].
    split; [exact Hl' |].
    split; [rewrite Hseq0, Hs'; seq_normalize |].
    right. split; [exact Hw' |].
    unfold tree_of.
    destruct (node_color (chain_has_node (CSingle cp cr))
                (Node KLeft pp' ss));
      [| destruct cp as [cb cn] | destruct cp as [cb cn] |];
      cbn; exact I.
  - (* with child: pair *)
    destruct (@pop_rebundle_total A k KLeft pp' ss a (CPair cl cr2)
                ltac:(right; reflexivity)
                ltac:(cbn [node_sizes]; split; [exact Hp5 | exact Hs2])
                Hnr Hpp'w Hssw Hpp'l Hssl Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Haw |]. split; [exact Hal |].
    split; [exact Hl' |].
    split; [rewrite Hseq0, Hs'; seq_normalize |].
    right. split; [exact Hw' |].
    unfold tree_of.
    destruct (node_color (chain_has_node (CPair cl cr2))
                (Node KLeft pp' ss)).
    + cbn. exact I.
    + destruct cl as [|[lb ln] lrest|? ?]; cbn; exact I.
    + destruct cr2 as [|[rb rn] rrest|? ?]; cbn; exact I.
    + cbn. exact I.
Qed.

(* ========================================================================== *)
(* pop_raw on a pair: pop the left component; keep, or re-crown collapse.     *)
(* ========================================================================== *)

(** One-step unfolding (so the recursive call can be rewritten by its
    propositional value without cbn-unfolding it into the let-match body). *)
Lemma pop_raw_pair_eq :
  forall A (l r : cchain A),
    pop_raw (CPair l r)
    = match pop_raw l with
      | Some (x, l') =>
          match l' with
          | CEmpty => Some (x, r)
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty =>
              if length lp <? 5
              then
                match r with
                | CSingle pr rr =>
                    match root_and_child pr rr with
                    | (Node _ p2 s2, d2) =>
                        Some (x, tree_of (Node KOnly (lp ++ ls ++ p2) s2) d2)
                    end
                | _ => None
                end
              else Some (x, CPair l' r)
          | _ => Some (x, CPair l' r)
          end
      | None => None
      end.
Proof. reflexivity. Qed.

Lemma pop_raw_pair_total :
  forall A (k : nat) (l r : cchain A),
    is_single l = true -> is_single r = true ->
    chain_wf KLeft l -> chain_wf KRight r ->
    chain_ends_green l -> chain_ends_green r ->
    chain_leveled k l -> chain_leveled k r ->
    exists x c',
      pop_raw (CPair l r) = Some (x, c') /\
      stored_wf x /\ stored_leveled k x /\
      chain_wf KOnly c' /\
      chain_leveled k c' /\
      cchain_seq (CPair l r) = stored_seq x ++ cchain_seq c'.
Proof.
  intros A k l r Hsl Hsr Hl Hr Hgl Hgr Hll Hlr.
  destruct l as [|pl rl|? ?]; cbn [is_single] in Hsl; try discriminate.
  destruct (pop_raw_left_total Hl Hgl Hll)
    as [x [l' [Hpop [Hxw [Hxl [Hll' [Hseql Hdisj]]]]]]].
  rewrite (cchain_seq_pair (CSingle pl rl) r).
  rewrite pop_raw_pair_eq, Hpop.
  destruct Hdisj as
    [[lp [ls [-> [Hlpw [Hlsw [Hlpl [Hlsl [Hls2 [Hlp4 Hseqcl]]]]]]]]]
     | [Hwfl' Hguard]].
  - (* childless left remainder *)
    destruct (length lp <? 5) eqn:Hlp.
    + (* collapse: re-crown over the peeled right root *)
      destruct r as [|pr rr|? ?]; cbn [is_single] in Hsr; try discriminate.
      destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
      cbn [fst snd].
      pose proof (root_and_child_facts Hr) as Hf2.
      rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
      destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 _]]]].
      cbn [node_kind] in Hk2. subst k2.
      cbn [node_sizes] in Hsz2. destruct Hsz2 as [Hp22 Hs25].
      cbn [cnode_wf] in Hnw2. destruct Hnw2 as [Hp2w Hs2w].
      pose proof (root_and_child_leveled Hlr) as Hlf2.
      rewrite Hrc2 in Hlf2. cbn [fst snd] in Hlf2.
      destruct Hlf2 as [Hn2l Hd2l].
      cbn [cnode_leveled] in Hn2l. destruct Hn2l as [Hp2l Hs2l].
      pose proof (root_not_red Hr Hgr) as Hnr2.
      rewrite Hrc2 in Hnr2. cbn [fst snd] in Hnr2.
      pose proof (root_child_facts Hr Hgr) as Hccf2.
      rewrite Hrc2 in Hccf2. cbn [fst snd] in Hccf2.
      assert (Hnpw : buf_stored_all_wf (lp ++ ls ++ p2)).
      { apply buf_all_wf_app; [exact Hlpw |].
        apply buf_all_wf_app; [exact Hlsw | exact Hp2w]. }
      assert (Hnpl : buf_all_leveled k (lp ++ ls ++ p2)).
      { apply buf_all_leveled_app; [exact Hlpl |].
        apply buf_all_leveled_app; [exact Hlsl | exact Hp2l]. }
      assert (Hlen8 : length (lp ++ ls ++ p2) = 8)
        by (rewrite !length_app; apply Nat.ltb_lt in Hlp; lia).
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      destruct d2 as [|d2p d2r|d2l d2rr].
      * (* childless right root *)
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [lia | exact Hs25]
             | split; [exact Hnpw | exact Hs2w]
             | exact I
             | exact I].
        -- apply tree_of_leveled;
             [split; [exact Hnpl | exact Hs2l] | exact I].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseql, Hseqcl.
           rewrite (root_and_child_seq pr rr), Hrc2. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
      * (* rooted right root: single child *)
        assert (Hhc : chain_has_node (CSingle d2p d2r) = true)
          by reflexivity.
        assert (Hnewc : node_color (chain_has_node (CSingle d2p d2r))
                  (Node KOnly (lp ++ ls ++ p2) s2) = gyor_of (length s2)).
        { rewrite Hhc, node_color_measure. cbn [node_measure].
          apply gyor_of_min_big. lia. }
        cbn [chain_has_node] in Hnr2, Hccf2.
        rewrite node_color_measure in Hnr2, Hccf2.
        cbn [node_measure] in Hnr2, Hccf2.
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [lia | exact Hs25]
             | split; [exact Hnpw | exact Hs2w]
             | exact Hcw2
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of (length s2)) eqn:Hg;
               [exact I | exact I
               | destruct Hccf2 as [_ Hpk]; exact Hpk
               | exfalso; apply Hnr2; reflexivity]].
        -- apply tree_of_leveled;
             [split; [exact Hnpl | exact Hs2l] | exact Hd2l].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseql, Hseqcl.
           rewrite (root_and_child_seq pr rr), Hrc2. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
      * (* rooted right root: pair child *)
        assert (Hhc : chain_has_node (CPair d2l d2rr) = true)
          by reflexivity.
        assert (Hnewc : node_color (chain_has_node (CPair d2l d2rr))
                  (Node KOnly (lp ++ ls ++ p2) s2) = gyor_of (length s2)).
        { rewrite Hhc, node_color_measure. cbn [node_measure].
          apply gyor_of_min_big. lia. }
        cbn [chain_has_node] in Hnr2, Hccf2.
        rewrite node_color_measure in Hnr2, Hccf2.
        cbn [node_measure] in Hnr2, Hccf2.
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [lia | exact Hs25]
             | split; [exact Hnpw | exact Hs2w]
             | exact Hcw2
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of (length s2)) eqn:Hg;
               [exact I | exact I
               | destruct Hccf2 as [_ Hpk]; exact Hpk
               | exfalso; apply Hnr2; reflexivity]].
        -- apply tree_of_leveled;
             [split; [exact Hnpl | exact Hs2l] | exact Hd2l].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseql, Hseqcl.
           rewrite (root_and_child_seq pr rr), Hrc2. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
    + (* keep: the childless left single stays legal *)
      apply Nat.ltb_ge in Hlp.
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      split; [| split].
      * cbn [chain_wf is_single].
        split; [reflexivity |]. split; [exact Hsr |].
        split; [| exact Hr].
        split; [exact I |].
        split; [reflexivity |].
        split.
        { cbn [chain_has_node node_sizes].
          split; [exact Hlp | exact Hls2]. }
        split; [split; [exact Hlpw | exact Hlsw] |].
        split; [left; reflexivity | exact I].
      * cbn [chain_leveled].
        split; [exact Hll' | exact Hlr].
      * rewrite Hseql.
        rewrite (cchain_seq_pair
          (CSingle (Pkt BHole (Node KLeft lp ls)) CEmpty) r).
        seq_normalize.
  - (* with-child left remainder: keep the pair *)
    destruct l' as [|[bd0 n0] rest0|? ?];
      [exfalso; exact Hguard | | exfalso; exact Hguard].
    destruct n0 as [kn0 pn0 sn0].
    destruct bd0; destruct rest0;
      try (exfalso; exact Hguard);
      (eexists; eexists;
       split; [reflexivity |];
       split; [exact Hxw |]; split; [exact Hxl |];
       split;
         [cbn [chain_wf is_single];
          split; [reflexivity |]; split; [exact Hsr |];
          split; [exact Hwfl' | exact Hr] |];
       split;
         [cbn [chain_leveled]; split; [exact Hll' | exact Hlr] |];
       rewrite Hseql;
       match goal with
       | |- _ = _ ++ cchain_seq (CPair ?a ?b) =>
           rewrite (cchain_seq_pair a b)
       end;
       seq_normalize).
Qed.

(* ========================================================================== *)
(* Eject mirrors.  node_eject takes the LAST suffix element via rev, so the   *)
(* buffer bookkeeping goes through rev-append inversions.                      *)
(* ========================================================================== *)

Lemma rev_cons_inv :
  forall (X : Type) (s s' : list X) (x : X),
    rev s = x :: s' -> s = rev s' ++ [x].
Proof.
  intros X s s' x H.
  rewrite <- (rev_involutive s), H. cbn [rev]. reflexivity.
Qed.

Lemma rev_nil_inv :
  forall (X : Type) (s : list X), rev s = [] -> s = [].
Proof.
  intros X [|a s] H; [reflexivity |].
  apply (f_equal (@length X)) in H.
  cbn [rev] in H. rewrite length_app in H. cbn in H. lia.
Qed.

Lemma eject_rebundle_total :
  forall A (k : nat) (kd : kind) (pp ss' : buffer (stored A))
         (x : stored A) (child : cchain A),
    (kd = KOnly \/ kd = KRight) ->
    node_sizes true (Node kd pp (ss' ++ [x])) ->
    node_color (chain_has_node child) (Node kd pp (ss' ++ [x])) <> CR ->
    buf_stored_all_wf pp -> buf_stored_all_wf ss' ->
    buf_all_leveled k pp -> buf_all_leveled k ss' ->
    chain_wf KOnly child -> child <> CEmpty ->
    chain_leveled (S k) child ->
    child_color_facts
      (node_color (chain_has_node child) (Node kd pp (ss' ++ [x]))) child ->
    chain_wf kd (tree_of (Node kd pp ss') child) /\
    chain_leveled k (tree_of (Node kd pp ss') child) /\
    cchain_seq (tree_of (Node kd pp ss') child)
    = buf_stored_seq pp ++ cchain_seq child ++ buf_stored_seq ss'.
Proof.
  intros A k kd pp ss' x child Hkd Hsz Hnr Hpw Hsw Hpl Hsl Hcw Hne Hcl
    Hccf.
  assert (Hhc : chain_has_node child = true)
    by (destruct child; [congruence | reflexivity | reflexivity]).
  rewrite Hhc in Hnr, Hccf.
  rewrite node_color_measure in Hnr, Hccf.
  assert (Hm6 : 6 <= node_measure (Node kd pp (ss' ++ [x]))).
  { destruct (gyor_of (node_measure (Node kd pp (ss' ++ [x])))) eqn:Hold.
    - assert (H8 : 8 <= node_measure (Node kd pp (ss' ++ [x])))
        by exact (gyor_of_inv Hold). lia.
    - assert (H7 : node_measure (Node kd pp (ss' ++ [x])) = 7)
        by exact (gyor_of_inv Hold). lia.
    - assert (H6 : node_measure (Node kd pp (ss' ++ [x])) = 6)
        by exact (gyor_of_inv Hold). lia.
    - exfalso. apply Hnr. reflexivity. }
  assert (Hsz' : node_sizes true (Node kd pp ss')).
  { destruct Hkd as [-> | ->]; cbn [node_sizes] in Hsz |- *.
    - destruct Hsz as [[H1 H2] | [Hcontra _]]; [| discriminate].
      left. cbn [node_measure] in Hm6.
      rewrite length_app in Hm6, H2. cbn [length] in Hm6, H2.
      split; lia.
    - destruct Hsz as [H1 H2]. split; [exact H1 |].
      cbn [node_measure] in Hm6.
      rewrite length_app in Hm6. cbn [length] in Hm6. lia. }
  assert (Hrcf' : root_color_facts (Node kd pp ss') child).
  { unfold root_color_facts. rewrite Hhc, node_color_measure.
    destruct (gyor_of (node_measure (Node kd pp ss'))) eqn:Hnew.
    - exact I.
    - exact I.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct child as [|? ?|l r2]; [congruence | exact I |].
      destruct (gyor_of (node_measure (Node kd pp (ss' ++ [x])))) eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure] in Hold, Hnew;
          rewrite !length_app in Hold; cbn [length] in Hold; lia.
      + cbn [child_color_facts cont_green] in Hccf. exact Hccf.
      + cbn [child_color_facts cont_green] in Hccf.
        destruct Hccf as [_ Hpk]. exact Hpk.
      + exfalso. apply Hnr. reflexivity.
    - apply gyor_of_inv in Hnew. cbn [node_measure] in Hnew.
      destruct (gyor_of (node_measure (Node kd pp (ss' ++ [x])))) eqn:Hold.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure] in Hold, Hnew;
          rewrite !length_app in Hold; cbn [length] in Hold; lia.
      + apply gyor_of_inv in Hold. cbn [node_measure] in Hold.
        exfalso. destruct Hkd as [-> | ->];
          cbn [node_measure] in Hold, Hnew;
          rewrite !length_app in Hold; cbn [length] in Hold; lia.
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

Lemma eject_raw_only_total :
  forall A (k : nat) (p : cpacket A) (rest : cchain A),
    chain_wf KOnly (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    chain_leveled k (CSingle p rest) ->
    exists c' x,
      eject_raw (CSingle p rest) = Some (c', x) /\
      stored_wf x /\ stored_leveled k x /\
      chain_wf KOnly c' /\
      chain_leveled k c' /\
      cchain_seq (CSingle p rest) = cchain_seq c' ++ stored_seq x.
Proof.
  intros A k p r Hwf Hg Hl.
  cbn [eject_raw].
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
  cbn [node_eject].
  destruct (rev ss) as [|x ss''] eqn:Hrs.
  - (* empty suffix: childless one-sided, eject the prefix's last *)
    apply rev_nil_inv in Hrs. subst ss.
    destruct child as [|cp cr|cl cr2].
    + cbn [node_sizes chain_has_node] in Hsz.
      assert (Hpp1 : 1 <= length pp).
      { destruct Hsz as [[H1 H2] | [_ [[Hpe H1] | [_ H1]]]];
          [cbn in H2; lia | cbn in H1; lia | exact H1]. }
      destruct (rev pp) as [|y pp''] eqn:Hrp.
      { apply rev_nil_inv in Hrp. subst pp. cbn in Hpp1. lia. }
      pose proof (rev_cons_inv Hrp) as Hb.
      assert (Hppw' : buf_stored_all_wf (rev pp'' ++ [y]))
        by (rewrite <- Hb; exact Hppw).
      apply buf_all_wf_app_inv in Hppw'.
      destruct Hppw' as [Hpp''w Hyw']. cbn in Hyw'.
      destruct Hyw' as [Hyw _].
      assert (Hppl' : buf_all_leveled k (rev pp'' ++ [y]))
        by (rewrite <- Hb; exact Hppl).
      apply buf_all_leveled_app_inv in Hppl'.
      destruct Hppl' as [Hpp''l Hyl']. cbn in Hyl'.
      destruct Hyl' as [Hyl _].
      destruct (@rebuild_childless_facts A k (Node KOnly (rev pp'') [])
                  ltac:(reflexivity)
                  ltac:(split; [exact Hpp''w | exact I])
                  ltac:(split; [exact Hpp''l | exact I]))
        as [Hw' [Hg' [Hl' Hs']]].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hyw |]. split; [exact Hyl |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs', Hb.
      rewrite cnode_seq_eq. seq_normalize.
    + cbn [node_sizes] in Hsz.
      destruct Hsz as [[H1 H2] | [Hcontra _]];
        [cbn in H2; lia | discriminate].
    + cbn [node_sizes] in Hsz.
      destruct Hsz as [[H1 H2] | [Hcontra _]];
        [cbn in H2; lia | discriminate].
  - (* nonempty suffix: eject its last *)
    pose proof (rev_cons_inv Hrs) as Hb.
    assert (Hssw' : buf_stored_all_wf (rev ss'' ++ [x]))
      by (rewrite <- Hb; exact Hssw).
    apply buf_all_wf_app_inv in Hssw'.
    destruct Hssw' as [Hss''w Hxw']. cbn in Hxw'.
    destruct Hxw' as [Hxw _].
    assert (Hssl' : buf_all_leveled k (rev ss'' ++ [x]))
      by (rewrite <- Hb; exact Hssl).
    apply buf_all_leveled_app_inv in Hssl'.
    destruct Hssl' as [Hss''l Hxl']. cbn in Hxl'.
    destruct Hxl' as [Hxl _].
    rewrite Hb in Hsz, Hnr, Hccf, Hseq0.
    destruct child as [|cp cr|cl cr2].
    + (* childless *)
      destruct (@rebuild_childless_facts A k (Node KOnly pp (rev ss''))
                  ltac:(reflexivity)
                  ltac:(split; [exact Hppw | exact Hss''w])
                  ltac:(split; [exact Hppl | exact Hss''l]))
        as [Hw' [Hg' [Hl' Hs']]].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs'.
      rewrite cnode_seq_eq. seq_normalize.
    + (* with child: single *)
      destruct (@eject_rebundle_total A k KOnly pp (rev ss'') x
                  (CSingle cp cr)
                  ltac:(left; reflexivity) Hsz Hnr Hppw Hss''w Hppl Hss''l
                  Hcw ltac:(discriminate) Hchl Hccf)
        as [Hw' [Hl' Hs']].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs'. seq_normalize.
    + (* with child: pair *)
      destruct (@eject_rebundle_total A k KOnly pp (rev ss'') x
                  (CPair cl cr2)
                  ltac:(left; reflexivity) Hsz Hnr Hppw Hss''w Hppl Hss''l
                  Hcw ltac:(discriminate) Hchl Hccf)
        as [Hw' [Hl' Hs']].
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      split; [exact Hw' |]. split; [exact Hl' |].
      rewrite Hseq0, Hs'. seq_normalize.
Qed.

Lemma eject_raw_right_total :
  forall A (k : nat) (p : cpacket A) (rest : cchain A),
    chain_wf KRight (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    chain_leveled k (CSingle p rest) ->
    exists c' x,
      eject_raw (CSingle p rest) = Some (c', x) /\
      stored_wf x /\ stored_leveled k x /\
      chain_leveled k c' /\
      cchain_seq (CSingle p rest) = cchain_seq c' ++ stored_seq x /\
      ((exists rp rs,
          c' = CSingle (Pkt BHole (Node KRight rp rs)) CEmpty /\
          buf_stored_all_wf rp /\ buf_stored_all_wf rs /\
          buf_all_leveled k rp /\ buf_all_leveled k rs /\
          length rp = 2 /\ 4 <= length rs /\
          cchain_seq c' = buf_stored_seq rp ++ buf_stored_seq rs)
       \/ (chain_wf KRight c' /\
           match c' with
           | CSingle (Pkt BHole _) CEmpty => False
           | CSingle _ _ => True
           | _ => False
           end)).
Proof.
  intros A k p r Hwf Hg Hl.
  cbn [eject_raw].
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
  cbn [node_sizes] in Hsz. destruct Hsz as [Hp22 Hs5].
  cbn [node_eject].
  destruct (rev ss) as [|x ss''] eqn:Hrs.
  { apply rev_nil_inv in Hrs. subst ss. cbn in Hs5. lia. }
  pose proof (rev_cons_inv Hrs) as Hb.
  assert (Hlenss : length ss = length ss'' + 1).
  { rewrite Hb, length_app. cbn [length]. rewrite length_rev. lia. }
  assert (Hssw' : buf_stored_all_wf (rev ss'' ++ [x]))
    by (rewrite <- Hb; exact Hssw).
  apply buf_all_wf_app_inv in Hssw'.
  destruct Hssw' as [Hss''w Hxw']. cbn in Hxw'.
  destruct Hxw' as [Hxw _].
  assert (Hssl' : buf_all_leveled k (rev ss'' ++ [x]))
    by (rewrite <- Hb; exact Hssl).
  apply buf_all_leveled_app_inv in Hssl'.
  destruct Hssl' as [Hss''l Hxl']. cbn in Hxl'.
  destruct Hxl' as [Hxl _].
  rewrite Hb in Hnr, Hccf, Hseq0.
  destruct child as [|cp cr|cl cr2].
  - (* childless: rebuild keeps the KRight node — report the shape *)
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Hxw |]. split; [exact Hxl |].
    assert (Hrb : rebuild_childless (Node KRight pp (rev ss''))
                  = CSingle (Pkt BHole (Node KRight pp (rev ss''))) CEmpty).
    { unfold rebuild_childless.
      destruct pp as [|? ?]; [cbn [length] in Hp22; lia |].
      destruct (rev ss'') as [|? ?]; reflexivity. }
    rewrite Hrb.
    split.
    { cbn [chain_leveled cbody_leveled body_depth].
      rewrite Nat.add_0_r.
      split; [exact I |].
      split; [| exact I].
      cbn [cnode_leveled]. split; [exact Hppl | exact Hss''l]. }
    split.
    { rewrite Hseq0.
      cbn [cchain_seq cpacket_seq cbody_seq].
      rewrite cnode_seq_eq. seq_normalize. }
    left. exists pp, (rev ss'').
    split; [reflexivity |].
    split; [exact Hppw |]. split; [exact Hss''w |].
    split; [exact Hppl |]. split; [exact Hss''l |].
    split; [exact Hp22 |].
    split; [rewrite length_rev; lia |].
    cbn [cchain_seq cpacket_seq cbody_seq].
    rewrite cnode_seq_eq. seq_normalize.
  - (* with child: single *)
    destruct (@eject_rebundle_total A k KRight pp (rev ss'') x
                (CSingle cp cr)
                ltac:(right; reflexivity)
                ltac:(cbn [node_sizes]; split;
                      [exact Hp22
                      | rewrite length_app; cbn [length];
                        rewrite Hb, length_app in Hs5;
                        cbn [length] in Hs5; lia])
                Hnr Hppw Hss''w Hppl Hss''l Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Hxw |]. split; [exact Hxl |].
    split; [exact Hl' |].
    split; [rewrite Hseq0, Hs'; seq_normalize |].
    right. split; [exact Hw' |].
    unfold tree_of.
    destruct (node_color (chain_has_node (CSingle cp cr))
                (Node KRight pp (rev ss'')));
      [| destruct cp as [cb cn] | destruct cp as [cb cn] |];
      cbn; exact I.
  - (* with child: pair *)
    destruct (@eject_rebundle_total A k KRight pp (rev ss'') x
                (CPair cl cr2)
                ltac:(right; reflexivity)
                ltac:(cbn [node_sizes]; split;
                      [exact Hp22
                      | rewrite length_app; cbn [length];
                        rewrite Hb, length_app in Hs5;
                        cbn [length] in Hs5; lia])
                Hnr Hppw Hss''w Hppl Hss''l Hcw
                ltac:(discriminate) Hchl Hccf)
      as [Hw' [Hl' Hs']].
    eexists. eexists.
    split; [reflexivity |].
    split; [exact Hxw |]. split; [exact Hxl |].
    split; [exact Hl' |].
    split; [rewrite Hseq0, Hs'; seq_normalize |].
    right. split; [exact Hw' |].
    unfold tree_of.
    destruct (node_color (chain_has_node (CPair cl cr2))
                (Node KRight pp (rev ss''))).
    + cbn. exact I.
    + destruct cl as [|[lb ln] lrest|? ?]; cbn; exact I.
    + destruct cr2 as [|[rb rn] rrest|? ?]; cbn; exact I.
    + cbn. exact I.
Qed.

Lemma eject_raw_pair_eq :
  forall A (l r : cchain A),
    eject_raw (CPair l r)
    = match eject_raw r with
      | Some (r', x) =>
          match r' with
          | CEmpty => Some (l, x)
          | CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if length rs <? 5
              then
                match l with
                | CSingle pl rl =>
                    match root_and_child pl rl with
                    | (Node _ p1 s1, d1) =>
                        Some (tree_of (Node KOnly p1 (s1 ++ rp ++ rs)) d1, x)
                    end
                | _ => None
                end
              else Some (CPair l r', x)
          | _ => Some (CPair l r', x)
          end
      | None => None
      end.
Proof. reflexivity. Qed.

Lemma eject_raw_pair_total :
  forall A (k : nat) (l r : cchain A),
    is_single l = true -> is_single r = true ->
    chain_wf KLeft l -> chain_wf KRight r ->
    chain_ends_green l -> chain_ends_green r ->
    chain_leveled k l -> chain_leveled k r ->
    exists c' x,
      eject_raw (CPair l r) = Some (c', x) /\
      stored_wf x /\ stored_leveled k x /\
      chain_wf KOnly c' /\
      chain_leveled k c' /\
      cchain_seq (CPair l r) = cchain_seq c' ++ stored_seq x.
Proof.
  intros A k l r Hsl Hsr Hl Hr Hgl Hgr Hll Hlr.
  destruct r as [|pr rr|? ?]; cbn [is_single] in Hsr; try discriminate.
  destruct (eject_raw_right_total Hr Hgr Hlr)
    as [r' [x [Hpop [Hxw [Hxl [Hlr' [Hseqr Hdisj]]]]]]].
  rewrite (cchain_seq_pair l (CSingle pr rr)).
  rewrite eject_raw_pair_eq, Hpop.
  destruct Hdisj as
    [[rp [rs [-> [Hrpw [Hrsw [Hrpl [Hrsl [Hrp2 [Hrs4 Hseqcr]]]]]]]]]
     | [Hwfr' Hguard]].
  - (* childless right remainder *)
    destruct (length rs <? 5) eqn:Hrs5.
    + (* collapse: re-crown over the peeled left root *)
      destruct l as [|pl rl|? ?]; cbn [is_single] in Hsl; try discriminate.
      destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
      cbn [fst snd].
      pose proof (root_and_child_facts Hl) as Hf1.
      rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
      destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 _]]]].
      cbn [node_kind] in Hk1. subst k1.
      cbn [node_sizes] in Hsz1. destruct Hsz1 as [Hp15 Hs12].
      cbn [cnode_wf] in Hnw1. destruct Hnw1 as [Hp1w Hs1w].
      pose proof (root_and_child_leveled Hll) as Hlf1.
      rewrite Hrc1 in Hlf1. cbn [fst snd] in Hlf1.
      destruct Hlf1 as [Hn1l Hd1l].
      cbn [cnode_leveled] in Hn1l. destruct Hn1l as [Hp1l Hs1l].
      pose proof (root_not_red Hl Hgl) as Hnr1.
      rewrite Hrc1 in Hnr1. cbn [fst snd] in Hnr1.
      pose proof (root_child_facts Hl Hgl) as Hccf1.
      rewrite Hrc1 in Hccf1. cbn [fst snd] in Hccf1.
      assert (Hnsw : buf_stored_all_wf (s1 ++ rp ++ rs)).
      { apply buf_all_wf_app; [exact Hs1w |].
        apply buf_all_wf_app; [exact Hrpw | exact Hrsw]. }
      assert (Hnsl : buf_all_leveled k (s1 ++ rp ++ rs)).
      { apply buf_all_leveled_app; [exact Hs1l |].
        apply buf_all_leveled_app; [exact Hrpl | exact Hrsl]. }
      assert (Hlen8 : length (s1 ++ rp ++ rs) = 8)
        by (rewrite !length_app; apply Nat.ltb_lt in Hrs5; lia).
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      destruct d1 as [|d1p d1r|d1l d1rr].
      * (* childless left root *)
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [exact Hp15 | lia]
             | split; [exact Hp1w | exact Hnsw]
             | exact I
             | exact I].
        -- apply tree_of_leveled;
             [split; [exact Hp1l | exact Hnsl] | exact I].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseqr, Hseqcr.
           rewrite (root_and_child_seq pl rl), Hrc1. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
      * (* rooted left root: single child *)
        assert (Hnewc : node_color (chain_has_node (CSingle d1p d1r))
                  (Node KOnly p1 (s1 ++ rp ++ rs)) = gyor_of (length p1)).
        { cbn [chain_has_node]. rewrite node_color_measure.
          cbn [node_measure].
          apply gyor_of_min_big_r. lia. }
        cbn [chain_has_node] in Hnr1, Hccf1.
        rewrite node_color_measure in Hnr1, Hccf1.
        cbn [node_measure] in Hnr1, Hccf1.
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [exact Hp15 | lia]
             | split; [exact Hp1w | exact Hnsw]
             | exact Hcw1
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of (length p1)) eqn:Hg;
               [exact I | exact I
               | destruct Hccf1 as [_ Hpk]; exact Hpk
               | exfalso; apply Hnr1; reflexivity]].
        -- apply tree_of_leveled;
             [split; [exact Hp1l | exact Hnsl] | exact Hd1l].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseqr, Hseqcr.
           rewrite (root_and_child_seq pl rl), Hrc1. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
      * (* rooted left root: pair child *)
        assert (Hnewc : node_color (chain_has_node (CPair d1l d1rr))
                  (Node KOnly p1 (s1 ++ rp ++ rs)) = gyor_of (length p1)).
        { cbn [chain_has_node]. rewrite node_color_measure.
          cbn [node_measure].
          apply gyor_of_min_big_r. lia. }
        cbn [chain_has_node] in Hnr1, Hccf1.
        rewrite node_color_measure in Hnr1, Hccf1.
        cbn [node_measure] in Hnr1, Hccf1.
        split; [| split].
        -- apply tree_of_wf;
             [reflexivity
             | cbn [chain_has_node node_sizes]; left;
               split; [exact Hp15 | lia]
             | split; [exact Hp1w | exact Hnsw]
             | exact Hcw1
             | unfold root_color_facts; rewrite Hnewc;
               destruct (gyor_of (length p1)) eqn:Hg;
               [exact I | exact I
               | destruct Hccf1 as [_ Hpk]; exact Hpk
               | exfalso; apply Hnr1; reflexivity]].
        -- apply tree_of_leveled;
             [split; [exact Hp1l | exact Hnsl] | exact Hd1l].
        -- rewrite tree_of_seq, cnode_seq_eq.
           rewrite Hseqr, Hseqcr.
           rewrite (root_and_child_seq pl rl), Hrc1. cbn [fst snd].
           rewrite cnode_seq_eq. seq_normalize.
    + (* keep *)
      apply Nat.ltb_ge in Hrs5.
      eexists. eexists.
      split; [reflexivity |].
      split; [exact Hxw |]. split; [exact Hxl |].
      split; [| split].
      * cbn [chain_wf is_single].
        split; [exact Hsl |]. split; [reflexivity |].
        split; [exact Hl |].
        split; [exact I |].
        split; [reflexivity |].
        split.
        { cbn [chain_has_node node_sizes].
          split; [exact Hrp2 | exact Hrs5]. }
        split; [split; [exact Hrpw | exact Hrsw] |].
        split; [left; reflexivity | exact I].
      * cbn [chain_leveled].
        split; [exact Hll | exact Hlr'].
      * rewrite Hseqr.
        rewrite (cchain_seq_pair l
          (CSingle (Pkt BHole (Node KRight rp rs)) CEmpty)).
        seq_normalize.
  - (* with-child right remainder: keep the pair *)
    destruct r' as [|[bd0 n0] rest0|? ?];
      [exfalso; exact Hguard | | exfalso; exact Hguard].
    destruct n0 as [kn0 pn0 sn0].
    destruct bd0; destruct rest0;
      try (exfalso; exact Hguard);
      (eexists; eexists;
       split; [reflexivity |];
       split; [exact Hxw |]; split; [exact Hxl |];
       split;
         [cbn [chain_wf is_single];
          split; [exact Hsl |]; split; [reflexivity |];
          split; [exact Hl | exact Hwfr'] |];
       split;
         [cbn [chain_leveled]; split; [exact Hll | exact Hlr'] |];
       rewrite Hseqr;
       match goal with
       | |- _ = cchain_seq (CPair ?a ?b) ++ _ =>
           rewrite (cchain_seq_pair a b)
       end;
       seq_normalize).
Qed.
