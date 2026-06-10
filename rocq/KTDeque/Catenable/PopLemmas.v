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
