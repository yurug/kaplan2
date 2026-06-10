(** * KTDeque.Catenable.ConcatLemmas — concat totality + J + sequence.

    KT99 §6.2 Lemma 6.2, assembled per case.  The empty/degenerate/small
    cases are proven; the two big-prefix cases and the two Case-1 triple
    builders are precise [Admitted] sub-obligations (the keystone's single
    concat admit, split smaller per methodology rule 6). *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Case 4: both degenerate.                                                    *)
(* ========================================================================== *)

Lemma single_node_seq :
  forall A (p s : buffer (stored A)),
    cchain_seq (CSingle (Pkt BHole (Node KOnly p s)) CEmpty)
    = buf_stored_seq p ++ buf_stored_seq s.
Proof. reflexivity. Qed.

Lemma concat_case4 :
  forall A (p s : buffer (stored A)),
    1 <= length p -> 1 <= length s ->
    buf_stored_all_wf p -> buf_stored_all_wf s ->
    exists f,
      (if (length p <? 8) || (length s <? 8)
       then Some (CSingle (Pkt BHole (Node KOnly (p ++ s) [])) CEmpty)
       else Some (CSingle (Pkt BHole (Node KOnly p s)) CEmpty))
      = Some (f : cchain A) /\
      chain_wf KOnly f /\ chain_ends_green f /\
      cchain_seq f = buf_stored_seq p ++ buf_stored_seq s.
Proof.
  intros A p s Hp Hs Hpw Hsw.
  destruct ((length p <? 8) || (length s <? 8)) eqn:Hsmall.
  - eexists. split; [reflexivity|].
    split.
    + split; [exact I|]. split; [reflexivity|].
      split.
      * right. split; [reflexivity|]. right.
        split; [reflexivity | rewrite length_app; lia].
      * split.
        { split; [apply buf_all_stored_wf_app; assumption | exact I]. }
        split; [left; reflexivity | exact I].
    + split; [reflexivity|].
      rewrite single_node_seq, buf_stored_seq_app.
      cbn [buf_stored_seq]. rewrite !app_nil_r. reflexivity.
  - apply Bool.orb_false_elim in Hsmall. destruct Hsmall as [Hp8 Hs8].
    apply Nat.ltb_ge in Hp8. apply Nat.ltb_ge in Hs8.
    eexists. split; [reflexivity|].
    split.
    + split; [exact I|]. split; [reflexivity|].
      split.
      * left. split; lia.
      * split; [split; assumption | split; [left; reflexivity | exact I]].
    + split; [reflexivity|].
      rewrite single_node_seq. reflexivity.
Qed.


(* ========================================================================== *)
(* Buffer decomposition toolkit (for the Case-1 builders).                     *)
(* ========================================================================== *)

Lemma buf_pop2_inv :
  forall (X : Type) (b : buffer X) (x y : X) (r : buffer X),
    buf_pop2 b = Some (x, y, r) -> b = x :: y :: r.
Proof.
  intros X b x y r H.
  destruct b as [|a [|a' b']]; cbn in H; try discriminate.
  injection H as <- <- <-. reflexivity.
Qed.

Lemma buf_pop2_total :
  forall (X : Type) (b : buffer X),
    2 <= length b -> exists x y r, buf_pop2 b = Some (x, y, r).
Proof.
  intros X [|a [|a' b']] H; cbn in H; try lia.
  repeat eexists.
Qed.

Lemma buf_eject2_inv :
  forall (X : Type) (b : buffer X) (i : buffer X) (y z : X),
    buf_eject2 b = Some (i, y, z) -> b = i ++ [y; z].
Proof.
  intros X b i y z H.
  unfold buf_eject2 in H.
  destruct (rev b) as [|z0 [|y0 r]] eqn:Hr; try discriminate.
  injection H as <- <- <-.
  rewrite <- (rev_involutive b), Hr.
  cbn [rev]. rewrite <- app_assoc. reflexivity.
Qed.

Lemma buf_eject2_total :
  forall (X : Type) (b : buffer X),
    2 <= length b -> exists i y z, buf_eject2 b = Some (i, y, z).
Proof.
  intros X b H.
  unfold buf_eject2.
  destruct (rev b) as [|z0 [|y0 r]] eqn:Hr.
  - apply (f_equal (@length X)) in Hr. rewrite length_rev in Hr. cbn in Hr. lia.
  - apply (f_equal (@length X)) in Hr. rewrite length_rev in Hr. cbn in Hr. lia.
  - repeat eexists.
Qed.

Lemma buf_eject3_inv :
  forall (X : Type) (b : buffer X) (i : buffer X) (x y z : X),
    buf_eject3 b = Some (i, x, y, z) -> b = i ++ [x; y; z].
Proof.
  intros X b i x y z H.
  unfold buf_eject3 in H.
  destruct (rev b) as [|c [|bb [|a r]]] eqn:Hr; try discriminate.
  injection H as <- <- <- <-.
  rewrite <- (rev_involutive b), Hr.
  cbn [rev]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma buf_eject3_total :
  forall (X : Type) (b : buffer X),
    3 <= length b -> exists i x y z, buf_eject3 b = Some (i, x, y, z).
Proof.
  intros X b H.
  unfold buf_eject3.
  destruct (rev b) as [|c [|bb [|a r]]] eqn:Hr;
    try (apply (f_equal (@length X)) in Hr; rewrite length_rev in Hr;
         cbn in Hr; lia).
  repeat eexists.
Qed.

Lemma buf_all_wf_app_inv :
  forall A (a b : buffer (stored A)),
    buf_stored_all_wf (a ++ b) ->
    buf_stored_all_wf a /\ buf_stored_all_wf b.
Proof.
  intros A a b H. induction a as [|x r IH]; cbn in *.
  - split; [exact I | exact H].
  - destruct H as [Hx Hr]. destruct (IH Hr) as [Ha Hb].
    repeat split; assumption.
Qed.

Lemma buf_all_wf_app :
  forall A (a b : buffer (stored A)),
    buf_stored_all_wf a -> buf_stored_all_wf b ->
    buf_stored_all_wf (a ++ b).
Proof. intros A a b. apply buf_all_stored_wf_app. Qed.

Lemma buf_stored_seq_cons :
  forall A (x : stored A) (r : buffer (stored A)),
    buf_stored_seq (x :: r) = stored_seq x ++ buf_stored_seq r.
Proof. reflexivity. Qed.

Lemma buf_stored_seq_nil :
  forall A, buf_stored_seq (@nil (stored A)) = [].
Proof. reflexivity. Qed.

(** Normalize a sequence goal: split all buffer apps/conses, reduce empties,
    right-associate. *)
Ltac seq_normalize :=
  repeat first
    [ rewrite buf_stored_seq_app
    | rewrite buf_stored_seq_cons
    | rewrite buf_stored_seq_nil ];
  cbn [cchain_seq stored_seq];
  rewrite <- ?app_assoc, ?app_nil_r, ?app_nil_l;
  try reflexivity.

(** Length of the eject2 remainder. *)
Lemma buf_eject2_length :
  forall (X : Type) (b i : buffer X) (y z : X),
    buf_eject2 b = Some (i, y, z) -> length b = length i + 2.
Proof.
  intros X b i y z H. apply buf_eject2_inv in H. subst b.
  rewrite length_app. cbn. lia.
Qed.

(* ========================================================================== *)
(* The per-shape colour-facts bundle a root's child supplies (keyed on the     *)
(* root's colour) — what the Case-1 builders need for the inner inject/push   *)
(* and the rebuilt node's tree_of dispatch.                                    *)
(* ========================================================================== *)

Definition child_color_facts {A : Type} (g : gyor) (d1 : cchain A) : Prop :=
  match g with
  | CG => True
  | CY => cont_green CY d1
  | CO => cont_green CO d1 /\
          match d1 with CPair l _ => chain_ends_green l | _ => True end
  | CR => False
  end.

(** Any green-ended single tree supplies the bundle at its root's colour. *)
Lemma root_child_facts :
  forall A (k : kind) (p : cpacket A) (rest : cchain A),
    chain_wf k (CSingle p rest) ->
    chain_ends_green (CSingle p rest) ->
    child_color_facts
      (node_color (chain_has_node (snd (root_and_child p rest)))
         (fst (root_and_child p rest)))
      (snd (root_and_child p rest)).
Proof.
  intros A k [b n] rest Hwf Hgreen.
  destruct b as [|hn b'|hn b' rc|hn lc b'];
    cbn [chain_wf cbody_wf body_out_kind is_single] in Hwf;
    cbn [chain_ends_green] in Hgreen;
    cbn [root_and_child fst snd].
  - (* BHole: terminal root, green by ends_green *)
    unfold child_color_facts.
    destruct rest as [|rp rrest|rl rr]; cbn [chain_has_node] in Hgreen |- *.
    + rewrite node_color_no_child. exact I.
    + rewrite Hgreen. exact I.
    + rewrite Hgreen. exact I.
  - (* BSingle head: CY or CO; child is the single path chain *)
    destruct Hwf as [[_ [_ [_ [Hcol _]]]] _].
    unfold child_color_facts. cbn [chain_has_node].
    destruct Hcol as [Hy | Ho]; [rewrite Hy | rewrite Ho].
    + exact Hgreen.
    + split; [exact Hgreen | exact I].
  - (* BPairY head: CY; cont = the left (path) side, green by ends_green *)
    destruct Hwf as [[_ [_ [_ [Hcol _]]]] _].
    unfold child_color_facts. cbn [chain_has_node].
    rewrite Hcol. exact Hgreen.
  - (* BPairO head: CO; cont = the right (path) side; parked left green *)
    destruct Hwf as [[_ [_ [_ [Hcol [_ [_ [Hlg _]]]]]]] _].
    unfold child_color_facts. cbn [chain_has_node].
    rewrite Hcol. split; [exact Hgreen | exact Hlg].
Qed.

(* ========================================================================== *)
(* Case 1c/1d: the only-triple LEFT builder.                                   *)
(* ========================================================================== *)

(** The singleton chain [push_chain (SSmall b) CEmpty] is well-formed and
    carries [b]'s sequence, given the stored floor. *)
Lemma small_singleton_wf :
  forall A (b : buffer (stored A)),
    3 <= length b -> buf_stored_all_wf b ->
    chain_wf KOnly (push_chain (SSmall b) CEmpty) /\
    chain_ends_green (push_chain (SSmall b) CEmpty) /\
    cchain_seq (push_chain (SSmall b) CEmpty) = buf_stored_seq b.
Proof.
  intros A b H3 Hw.
  cbn [push_chain].
  split; [| split].
  - split; [exact I|]. split; [reflexivity|].
    split.
    + right. split; [reflexivity|]. right.
      split; [reflexivity | cbn; lia].
    + split.
      * cbn. repeat split; [exact H3 | exact Hw].
      * split; [left; reflexivity | exact I].
  - reflexivity.
  - cbn. rewrite !app_nil_r. reflexivity.
Qed.

Lemma make_left_only_total :
  forall A (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A)),
    5 <= length p1 -> 5 <= length s1 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    chain_wf KOnly d1 ->
    (d1 <> CEmpty ->
       child_color_facts (gyor_of (Nat.min (length p1) (length s1))) d1) ->
    exists t,
      make_left_only p1 d1 s1 = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\ chain_ends_green t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1.
Proof.
  intros A p1 d1 s1 Hp5 Hs5 Hpw Hsw Hd1 Hbundle.
  unfold make_left_only.
  destruct d1 as [|d1p d1rest|d1l d1r].
  - (* 1d: childless *)
    destruct (length s1 <=? 8) eqn:H8.
    + (* small: move all but the last two across *)
      destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
        as [s1' [y [z He2]]].
      rewrite He2.
      pose proof (buf_eject2_inv He2) as Hs1eq.
      pose proof (buf_eject2_length He2) as Hlen.
      subst s1.
      destruct (buf_all_wf_app_inv Hsw) as [Hs1'w Hyzw].
      cbn in Hyzw. destruct Hyzw as [Hyw [Hzw _]].
      eexists. split; [reflexivity|].
      split; [apply tree_of_is_single|].
      assert (Hnode : node_color (chain_has_node (@CEmpty A))
                        (Node KLeft (p1 ++ s1') [y; z]) = CG)
        by (cbn [chain_has_node]; apply node_color_no_child).
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn; rewrite length_app; split; [lia | reflexivity]
          | split;
            [apply buf_all_wf_app; assumption
            | cbn; repeat split; assumption]
          | exact I
          | unfold root_color_facts; rewrite Hnode; exact I].
      * apply tree_of_ends_green; [exact I |].
        rewrite Hnode. exact I.
      * rewrite tree_of_seq, cnode_seq_eq. seq_normalize.
    + (* big: keep a stored middle *)
      apply Nat.leb_gt in H8.
      destruct s1 as [|a [|b [|c srest]]]; cbn in H8; try lia.
      assert (Hsr : 2 <= length srest) by (cbn in Hs5, H8; lia).
      destruct (@buf_eject2_total (stored A) srest Hsr)
        as [smid [y [z He2]]].
      rewrite He2.
      pose proof (buf_eject2_inv He2) as Hsreq.
      pose proof (buf_eject2_length He2) as Hlen.
      subst srest.
      cbn [buf_stored_all_wf] in Hsw.
      destruct Hsw as [Haw [Hbw [Hcw Hrw]]].
      destruct (buf_all_wf_app_inv Hrw) as [Hmidw Hyzw].
      cbn in Hyzw. destruct Hyzw as [Hyw [Hzw _]].
      assert (Hmid3 : 3 <= length smid) by (cbn in H8; lia).
      destruct (small_singleton_wf Hmid3 Hmidw) as [Hcwf [Hcg Hcseq]].
      eexists. split; [reflexivity|].
      split; [apply tree_of_is_single|].
      assert (Hnode :
          node_color
            (chain_has_node (push_chain (SSmall smid) (@CEmpty A)))
            (Node KLeft (p1 ++ [a; b; c]) [y; z]) = CG).
      { cbn [push_chain chain_has_node].
        rewrite node_color_measure. unfold gyor_of.
        cbn [node_measure]. rewrite length_app.
        destruct (8 <=? length p1 + length [a; b; c]) eqn:HH;
          [reflexivity | apply Nat.leb_gt in HH; cbn in HH; lia]. }
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; rewrite length_app;
            split; [cbn; lia | reflexivity]
          | split;
            [apply buf_all_wf_app;
              [assumption | cbn; repeat split; assumption]
            | cbn; repeat split; assumption]
          | exact Hcwf
          | unfold root_color_facts; rewrite Hnode; exact I].
      * apply tree_of_ends_green; [exact Hcwf |].
        rewrite Hnode. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hcseq. seq_normalize.
  - (* 1c, single child *)
    specialize (Hbundle ltac:(discriminate)).
    destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
      as [s1' [y [z He2]]].
    rewrite He2.
    pose proof (buf_eject2_inv He2) as Hs1eq.
    pose proof (buf_eject2_length He2) as Hlen.
    subst s1.
    destruct (buf_all_wf_app_inv Hsw) as [Hs1'w Hyzw].
    cbn in Hyzw. destruct Hyzw as [Hyw [Hzw _]].
    assert (Hsm : stored_wf (SSmall s1'))
      by (cbn; split; [lia | exact Hs1'w]).
    (* The bundle colour cannot be red, and on a single child it gives the
       child's greenness whenever it is CY or CO. *)
    assert (Hgd1 :
        gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))) = CG \/
        chain_ends_green (CSingle d1p d1rest)).
    { unfold child_color_facts in Hbundle.
      destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
        [left; reflexivity | right; exact Hbundle
        | right; exact (proj1 Hbundle) | contradiction]. }
    pose proof (@inject_chain_preserves_wf A (SSmall s1')
                  (CSingle d1p d1rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hsm Hd1) as Hwf'.
    eexists. split; [reflexivity|].
    split; [apply tree_of_is_single|].
    assert (Hseqd1' :
        cchain_seq (inject_chain (CSingle d1p d1rest) (SSmall s1'))
        = cchain_seq (CSingle d1p d1rest) ++ buf_stored_seq s1').
    { rewrite (inject_chain_seq (SSmall s1') Hd1). reflexivity. }
    (* colour of the new node *)
    destruct (node_color
                (chain_has_node
                   (inject_chain (CSingle d1p d1rest) (SSmall s1')))
                (Node KLeft p1 [y; z])) eqn:Hnew.
    + (* CG *)
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CY: the child must have been green-ended (single-child bundle) *)
      destruct Hgd1 as [HgCG | Hge].
      { (* bundle CG would force the new node green too *)
        exfalso.
        assert (Hm : gyor_rank (gyor_of (Nat.min (length p1)
                       (length (s1' ++ [y; z]))))
                     <= gyor_rank (gyor_of (length p1)))
          by (apply gyor_of_mono; lia).
        rewrite HgCG in Hm. cbn in Hm.
        revert Hnew.
        destruct (inject_chain (CSingle d1p d1rest) (SSmall s1'));
          cbn [chain_has_node];
          [ intros Hnew; rewrite node_color_no_child in Hnew; discriminate
          | rewrite node_color_measure; cbn [node_measure];
            intros Hnew; rewrite Hnew in Hm; cbn in Hm; lia
          | rewrite node_color_measure; cbn [node_measure];
            intros Hnew; rewrite Hnew in Hm; cbn in Hm; lia ]. }
      destruct (@inject_chain_preserves A (SSmall s1')
                  (CSingle d1p d1rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hsm Hd1 Hge)
        as [_ Hge'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew.
        unfold cont_green.
        destruct (inject_chain (CSingle d1p d1rest) (SSmall s1')) eqn:Hi;
          [exact I | exact Hge' |].
        (* inject of a CSingle is single *)
        exfalso. cbn [inject_chain] in Hi.
        pose proof (pkt_update_is_single
                      (fun n => node_inject n (SSmall s1')) d1p d1rest) as Hs.
        rewrite Hi in Hs. cbn in Hs. discriminate.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CO: same single-child bundle story *)
      destruct Hgd1 as [HgCG | Hge].
      { exfalso.
        assert (Hm : gyor_rank (gyor_of (Nat.min (length p1)
                       (length (s1' ++ [y; z]))))
                     <= gyor_rank (gyor_of (length p1)))
          by (apply gyor_of_mono; lia).
        rewrite HgCG in Hm. cbn in Hm.
        revert Hnew.
        destruct (inject_chain (CSingle d1p d1rest) (SSmall s1'));
          cbn [chain_has_node];
          [ intros Hnew; rewrite node_color_no_child in Hnew; discriminate
          | rewrite node_color_measure; cbn [node_measure];
            intros Hnew; rewrite Hnew in Hm; cbn in Hm; lia
          | rewrite node_color_measure; cbn [node_measure];
            intros Hnew; rewrite Hnew in Hm; cbn in Hm; lia ]. }
      destruct (@inject_chain_preserves A (SSmall s1')
                  (CSingle d1p d1rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hsm Hd1 Hge)
        as [_ Hge'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf' |].
        unfold root_color_facts. rewrite Hnew.
        destruct (inject_chain (CSingle d1p d1rest) (SSmall s1')) eqn:Hi;
          [exact I | exact I |].
        exfalso. cbn [inject_chain] in Hi.
        pose proof (pkt_update_is_single
                      (fun n => node_inject n (SSmall s1')) d1p d1rest) as Hs.
        rewrite Hi in Hs. cbn in Hs. discriminate.
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew.
        unfold cont_green.
        destruct (inject_chain (CSingle d1p d1rest) (SSmall s1')) eqn:Hi;
          [exact I | exact Hge' |].
        exfalso. cbn [inject_chain] in Hi.
        pose proof (pkt_update_is_single
                      (fun n => node_inject n (SSmall s1')) d1p d1rest) as Hs.
        rewrite Hi in Hs. cbn in Hs. discriminate.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CR: impossible — the new rank dominates the non-red bundle rank *)
      exfalso.
      assert (Hg0 : gyor_of (Nat.min (length p1) (length (s1' ++ [y; z])))
                    <> CR).
      { unfold child_color_facts in Hbundle.
        destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
          congruence. }
      assert (Hm : gyor_rank (gyor_of (Nat.min (length p1)
                     (length (s1' ++ [y; z]))))
                   <= gyor_rank (gyor_of (length p1)))
        by (apply gyor_of_mono; lia).
      revert Hnew.
      destruct (inject_chain (CSingle d1p d1rest) (SSmall s1'));
        cbn [chain_has_node].
      * intros Hnew. rewrite node_color_no_child in Hnew. discriminate.
      * rewrite node_color_measure; cbn [node_measure].
        intros Hnew. rewrite Hnew in Hm. cbn in Hm.
        destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
          cbn in Hm; congruence || lia.
      * rewrite node_color_measure; cbn [node_measure].
        intros Hnew. rewrite Hnew in Hm. cbn in Hm.
        destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
          cbn in Hm; congruence || lia.
  - (* 1c, pair child *)
    specialize (Hbundle ltac:(discriminate)).
    destruct (@buf_eject2_total (stored A) s1 ltac:(lia))
      as [s1' [y [z He2]]].
    rewrite He2.
    pose proof (buf_eject2_inv He2) as Hs1eq.
    pose proof (buf_eject2_length He2) as Hlen.
    subst s1.
    destruct (buf_all_wf_app_inv Hsw) as [Hs1'w Hyzw].
    cbn in Hyzw. destruct Hyzw as [Hyw [Hzw _]].
    assert (Hsm : stored_wf (SSmall s1'))
      by (cbn; split; [lia | exact Hs1'w]).
    pose proof Hd1 as Hd1'. cbn [chain_wf] in Hd1'.
    destruct Hd1' as [Hls [Hrs [Hl Hr]]].
    pose proof (@inject_chain_preserves_wf A (SSmall s1')
                  (CPair d1l d1r) KOnly
                  ltac:(congruence) ltac:(discriminate) Hsm Hd1) as Hwf'.
    assert (Hseqd1' :
        cchain_seq (inject_chain (CPair d1l d1r) (SSmall s1'))
        = cchain_seq (CPair d1l d1r) ++ buf_stored_seq s1').
    { rewrite (inject_chain_seq (SSmall s1') Hd1). reflexivity. }
    cbn [inject_chain] in Hwf', Hseqd1' |- *.
    eexists. split; [reflexivity|].
    split; [apply tree_of_is_single|].
    destruct (node_color
                (chain_has_node
                   (CPair d1l (inject_chain d1r (SSmall s1'))))
                (Node KLeft p1 [y; z])) eqn:Hnew.
    + (* CG *)
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CY: the continuation is the (unchanged) left side *)
      assert (HgL : chain_ends_green d1l).
      { unfold child_color_facts in Hbundle.
        destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))))
          eqn:Hg0.
        - exfalso.
          assert (Hm : 3 <= gyor_rank (gyor_of (length p1))).
          { pose proof (@gyor_of_mono
                          (Nat.min (length p1) (length (s1' ++ [y; z])))
                          (length p1) ltac:(lia)) as Hm.
            rewrite Hg0 in Hm. cbn in Hm. exact Hm. }
          revert Hnew. cbn [chain_has_node].
          rewrite node_color_measure; cbn [node_measure].
          intros Hnew. rewrite Hnew in Hm. cbn in Hm. lia.
        - cbn [cont_green] in Hbundle. exact Hbundle.
        - destruct Hbundle as [_ Hpl]. exact Hpl.
        - contradiction.
      }
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnew; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew. cbn [cont_green]. exact HgL.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CO: bundle must be CO — gives parked-left green and right-side green *)
      assert (HgCO : gyor_of (Nat.min (length p1) (length (s1' ++ [y; z])))
                     = CO \/
                     gyor_of (Nat.min (length p1) (length (s1' ++ [y; z])))
                     = CY).
      { destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))))
          eqn:Hg0.
        - exfalso.
          assert (Hm : 3 <= gyor_rank (gyor_of (length p1))).
          { pose proof (@gyor_of_mono
                          (Nat.min (length p1) (length (s1' ++ [y; z])))
                          (length p1) ltac:(lia)) as Hm.
            rewrite Hg0 in Hm. cbn in Hm. exact Hm. }
          revert Hnew. cbn [chain_has_node].
          rewrite node_color_measure; cbn [node_measure].
          intros Hnew. rewrite Hnew in Hm. cbn in Hm. lia.
        - right; reflexivity.
        - left; reflexivity.
        - contradiction. }
      (* In the CY-bundle case the new node cannot be CO (rank would drop). *)
      destruct HgCO as [HgCO | HgCY].
      2: { exfalso.
           assert (Hm : 2 <= gyor_rank (gyor_of (length p1))).
           { pose proof (@gyor_of_mono
                           (Nat.min (length p1) (length (s1' ++ [y; z])))
                           (length p1) ltac:(lia)) as Hm.
             rewrite HgCY in Hm. cbn in Hm. exact Hm. }
           revert Hnew. cbn [chain_has_node].
           rewrite node_color_measure; cbn [node_measure].
           intros Hnew. rewrite Hnew in Hm. cbn in Hm. lia. }
      unfold child_color_facts in Hbundle. rewrite HgCO in Hbundle.
      destruct Hbundle as [HgR HgL].
      cbn [cont_green] in HgR.
      (* strong inject on the right component for its greenness *)
      assert (Hrne : d1r <> CEmpty)
        by (destruct d1r; cbn in Hrs; congruence).
      destruct (@inject_chain_preserves A (SSmall s1') d1r KRight
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hrne; exact Heq)
                  Hsm Hr HgR) as [_ HgR'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnew; exact HgL].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnew. cbn [cont_green]. exact HgR'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseqd1'. seq_normalize.
    + (* CR impossible *)
      exfalso.
      assert (Hg0 : gyor_of (Nat.min (length p1) (length (s1' ++ [y; z])))
                    <> CR).
      { unfold child_color_facts in Hbundle.
        destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
          congruence. }
      assert (Hm : gyor_rank (gyor_of (Nat.min (length p1)
                     (length (s1' ++ [y; z]))))
                   <= gyor_rank (gyor_of (length p1)))
        by (apply gyor_of_mono; lia).
      revert Hnew. cbn [chain_has_node].
      rewrite node_color_measure; cbn [node_measure].
      intros Hnew. rewrite Hnew in Hm. cbn in Hm.
      destruct (gyor_of (Nat.min (length p1) (length (s1' ++ [y; z]))));
        cbn in Hm; congruence || lia.
Qed.

(* ========================================================================== *)
(* Case 1a core: rebuild a LEFT node over an injected stored cell.             *)
(* The bundle is keyed at gyor_of |p1| — exactly the new node's colour.        *)
(* ========================================================================== *)

Lemma gyor_of_min_big :
  forall a b, 9 <= a -> gyor_of (Nat.min a b) = gyor_of b.
Proof.
  intros a b Ha. unfold gyor_of.
  destruct (8 <=? b) eqn:Hb.
  - apply Nat.leb_le in Hb.
    assert (H8 : (8 <=? Nat.min a b) = true)
      by (apply Nat.leb_le; apply Nat.min_glb; lia).
    rewrite H8. reflexivity.
  - pose proof Hb as Hb0. apply Nat.leb_gt in Hb0.
    rewrite (Nat.min_r a b) by lia. rewrite Hb. reflexivity.
Qed.

Lemma left_rebuild_total :
  forall A (p1 : buffer (stored A)) (y z : stored A) (cell : stored A)
         (d1 : cchain A),
    5 <= length p1 -> buf_stored_all_wf p1 ->
    stored_wf y -> stored_wf z -> stored_wf cell ->
    chain_wf KOnly d1 -> d1 <> CEmpty ->
    child_color_facts (gyor_of (length p1)) d1 ->
    chain_wf KLeft (tree_of (Node KLeft p1 [y; z]) (inject_chain d1 cell)) /\
    chain_ends_green
      (tree_of (Node KLeft p1 [y; z]) (inject_chain d1 cell)) /\
    cchain_seq (tree_of (Node KLeft p1 [y; z]) (inject_chain d1 cell))
    = buf_stored_seq p1 ++ cchain_seq d1 ++ stored_seq cell
      ++ stored_seq y ++ stored_seq z.
Proof.
  intros A p1 y z cell d1 Hp5 Hpw Hyw Hzw Hcw Hd1 Hne Hbundle.
  assert (Hwf' : chain_wf KOnly (inject_chain d1 cell)).
  { apply (@inject_chain_preserves_wf A cell d1 KOnly);
      [congruence
      | intros Heq; exfalso; apply Hne; exact Heq
      | exact Hcw | exact Hd1]. }
  assert (Hseq' : cchain_seq (inject_chain d1 cell)
                  = cchain_seq d1 ++ stored_seq cell)
    by (rewrite (inject_chain_seq cell Hd1); reflexivity).
  destruct d1 as [|d1p d1rest|d1l d1r]; [congruence | |].
  - (* single child *)
    cbn [inject_chain] in Hwf', Hseq' |- *.
    assert (Hsing : is_single
              (pkt_update (fun n => node_inject n cell) d1p d1rest) = true)
      by apply pkt_update_is_single.
    destruct (pkt_update (fun n => node_inject n cell) d1p d1rest)
      as [|ip irest|? ?] eqn:Hpu; cbn in Hsing; try congruence.
    assert (Hnewc : node_color (chain_has_node (CSingle ip irest))
                      (Node KLeft p1 [y; z]) = gyor_of (length p1))
      by (cbn [chain_has_node]; rewrite node_color_measure; reflexivity).
    destruct (gyor_of (length p1)) eqn:Hg.
    + (* CG *)
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CY: bundle gives ends_green d1; use the strong inject *)
      cbn [cont_green] in Hbundle.
      destruct (@inject_chain_preserves A cell (CSingle d1p d1rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hcw Hd1 Hbundle)
        as [_ Hge'].
      cbn [inject_chain] in Hge'. rewrite Hpu in Hge'.
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hge'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CO: single child — bundle's cont gives the greenness *)
      cbn [cont_green] in Hbundle. destruct Hbundle as [Hge HparkT].
      destruct (@inject_chain_preserves A cell (CSingle d1p d1rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hcw Hd1 Hge)
        as [_ Hge'].
      cbn [inject_chain] in Hge'. rewrite Hpu in Hge'.
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hge'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + contradiction.
  - (* pair child: the cell goes right; the left continuation is untouched *)
    cbn [inject_chain] in Hwf', Hseq' |- *.
    pose proof Hd1 as Hd1'. cbn [chain_wf] in Hd1'.
    destruct Hd1' as [Hls [Hrs [Hl Hr]]].
    assert (Hnewc : node_color
                      (chain_has_node (CPair d1l (inject_chain d1r cell)))
                      (Node KLeft p1 [y; z]) = gyor_of (length p1))
      by (cbn [chain_has_node]; rewrite node_color_measure; reflexivity).
    destruct (gyor_of (length p1)) eqn:Hg.
    + split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CY: continuation is the unchanged left side *)
      cbn [cont_green] in Hbundle.
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hbundle.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CO: parked-left green + strong inject on the right component *)
      cbn [cont_green] in Hbundle. destruct Hbundle as [HgR HgL].
      assert (Hrne : d1r <> CEmpty)
        by (destruct d1r; cbn in Hrs; congruence).
      destruct (@inject_chain_preserves A cell d1r KRight
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hrne; exact Heq)
                  Hcw Hr HgR) as [_ HgR'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [lia | reflexivity]
          | split; [exact Hpw | cbn; repeat split; assumption]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact HgL].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact HgR'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + contradiction.
Qed.

(* ========================================================================== *)
(* Bridges and the two-sided-root fact (for the Case-1 dispatch).              *)
(* ========================================================================== *)

Lemma cchain_seq_pair :
  forall A (l r : cchain A),
    cchain_seq (CPair l r) = cchain_seq l ++ cchain_seq r.
Proof. reflexivity. Qed.

Lemma stored_seq_SBig :
  forall A (p : buffer (stored A)) (c : cchain A) (q : buffer (stored A)),
    stored_seq (SBig p c q)
    = buf_stored_seq p ++ cchain_seq c ++ buf_stored_seq q.
Proof. reflexivity. Qed.

(** A nondegenerate single tree has a two-sided root: the one-sided escape
    in [node_sizes] needs a childless root, and a childless root sits in a
    [BHole]/[CEmpty] packet — exactly the [degenerate_buf] shape. *)
Lemma root_two_sided :
  forall A (p : cpacket A) (r : cchain A) (k0 : kind)
         (pp ss : buffer (stored A)) (child : cchain A),
    root_and_child p r = (Node k0 pp ss, child) ->
    chain_wf KOnly (CSingle p r) ->
    degenerate_buf (CSingle p r) = None ->
    5 <= length pp /\ 5 <= length ss.
Proof.
  intros A p r k0 pp ss child Hrc Hwf Hdeg.
  pose proof (root_and_child_facts Hwf) as [Hk [Hsz _]].
  rewrite Hrc in Hk, Hsz. cbn [fst snd] in Hk, Hsz.
  cbn [node_kind] in Hk. subst k0.
  cbn [node_sizes] in Hsz.
  destruct Hsz as [[Hp Hs] | [Hnc Hone]]; [split; assumption | exfalso].
  destruct child as [|? ?|? ?]; cbn [chain_has_node] in Hnc;
    try discriminate.
  destruct p as [b n].
  destruct b as [|m b'|m b' rc|m lc b']; cbn [root_and_child] in Hrc.
  - injection Hrc as Hn Hr. subst n r.
    destruct Hone as [[Hpe _] | [Hse _]].
    + subst pp. cbn in Hdeg. discriminate.
    + subst ss. destruct pp as [|? ?]; cbn in Hdeg; discriminate.
  - injection Hrc as Hm Hc. discriminate Hc.
  - injection Hrc as Hm Hc. discriminate Hc.
  - injection Hrc as Hm Hc. discriminate Hc.
Qed.

(** Case 1a's computational core, shape-generic in the nonempty left child:
    eject two from the right suffix, park the middle as one [SBig] stored
    cell injected into the left child, rebuild a LEFT root over it. *)
Lemma make_left_pair_core :
  forall A (p1 s1 p2 s2 : buffer (stored A)) (d1 d2 : cchain A),
    5 <= length p1 -> length s1 = 2 ->
    length p2 = 2 -> 5 <= length s2 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    buf_stored_all_wf p2 -> buf_stored_all_wf s2 ->
    chain_wf KOnly d1 -> d1 <> CEmpty -> chain_wf KOnly d2 ->
    child_color_facts (gyor_of (length p1)) d1 ->
    exists t,
      match buf_eject2 s2 with
      | Some (s2', y, z) =>
          Some (tree_of (Node KLeft p1 [y; z])
                  (inject_chain d1 (SBig (s1 ++ p2) d2 s2')))
      | None => None
      end = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\ chain_ends_green t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1
        ++ buf_stored_seq p2 ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A p1 s1 p2 s2 d1 d2 Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
    Hd1 Hne Hd2 Hbundle.
  destruct (@buf_eject2_total (stored A) s2 ltac:(lia)) as [s2' [y [z He]]].
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
  destruct (left_rebuild_total Hp1 Hp1w Hyw Hzw Hcellw Hd1 Hne Hbundle)
    as [Hwt [Hgt Hseqt]].
  exists (tree_of (Node KLeft p1 [y; z])
            (inject_chain d1 (SBig (s1 ++ p2) d2 s2'))).
  split; [reflexivity |].
  split; [apply tree_of_is_single |].
  split; [exact Hwt |]. split; [exact Hgt |].
  rewrite Hseqt, Hb, stored_seq_SBig. seq_normalize.
Qed.

(* ========================================================================== *)
(* Right-side mirror toolkit.                                                  *)
(* ========================================================================== *)

(** A redder bundle key is stronger: CO's facts (cont on the right plus a
    parked-green left) imply CY's (green preferred/left path), and CR's
    [False] implies anything.  This converts a min-keyed bundle to a
    one-sided key. *)
Lemma child_color_facts_mono :
  forall A (g g' : gyor) (d : cchain A),
    gyor_rank g <= gyor_rank g' ->
    child_color_facts g d -> child_color_facts g' d.
Proof.
  intros A g g' d Hle Hf.
  destruct g.
  - destruct g'; cbn [gyor_rank] in Hle; try lia. exact I.
  - destruct g'; cbn [gyor_rank] in Hle; try lia.
    + exact I.
    + exact Hf.
  - destruct g'; cbn [gyor_rank] in Hle; try lia.
    + exact I.
    + cbn [child_color_facts] in Hf |- *.
      destruct Hf as [Hco Hpk].
      destruct d as [|? ?|l r]; cbn [cont_green] in Hco |- *.
      * exact I.
      * exact Hco.
      * exact Hpk.
    + exact Hf.
  - destruct g'; cbn [child_color_facts] in Hf; contradiction.
Qed.

Lemma gyor_of_big : forall m, 8 <= m -> gyor_of m = CG.
Proof.
  intros m H. unfold gyor_of.
  assert (Hb : (8 <=? m) = true) by (apply Nat.leb_le; lia).
  rewrite Hb. reflexivity.
Qed.

Lemma gyor_of_min_big_r :
  forall a b, 9 <= b -> gyor_of (Nat.min a b) = gyor_of a.
Proof.
  intros a b Hb. rewrite Nat.min_comm. apply gyor_of_min_big. exact Hb.
Qed.

Lemma stored_seq_SSmall :
  forall A (b : buffer (stored A)),
    stored_seq (SSmall b) = buf_stored_seq b.
Proof. reflexivity. Qed.

(** Mirror of [left_rebuild_total]: rebuild a RIGHT node over a pushed
    stored cell.  [push_chain] descends into the LEFT pair component — the
    yellow-preferred side — so CY needs the strong push under the bundle's
    green left path, and CO uses its parked clause for the strong push and
    its cont clause (the untouched right) for the top path. *)
Lemma right_rebuild_total :
  forall A (s2 : buffer (stored A)) (x y : stored A) (cell : stored A)
         (d2 : cchain A),
    5 <= length s2 -> buf_stored_all_wf s2 ->
    stored_wf x -> stored_wf y -> stored_wf cell ->
    chain_wf KOnly d2 -> d2 <> CEmpty ->
    child_color_facts (gyor_of (length s2)) d2 ->
    chain_wf KRight
      (tree_of (Node KRight [x; y] s2) (push_chain cell d2)) /\
    chain_ends_green
      (tree_of (Node KRight [x; y] s2) (push_chain cell d2)) /\
    cchain_seq (tree_of (Node KRight [x; y] s2) (push_chain cell d2))
    = stored_seq x ++ stored_seq y ++ stored_seq cell
      ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A s2 x y cell d2 Hs5 Hsw Hxw Hyw Hcw Hd2 Hne Hbundle.
  assert (Hwf' : chain_wf KOnly (push_chain cell d2)).
  { apply (@push_chain_preserves_wf A cell d2 KOnly);
      [congruence
      | intros Heq; exfalso; apply Hne; exact Heq
      | exact Hcw | exact Hd2]. }
  assert (Hseq' : cchain_seq (push_chain cell d2)
                  = stored_seq cell ++ cchain_seq d2)
    by (rewrite (push_chain_seq cell Hd2); reflexivity).
  destruct d2 as [|d2p d2rest|d2l d2r]; [congruence | |].
  - (* single child *)
    cbn [push_chain] in Hwf', Hseq' |- *.
    assert (Hsing : is_single
              (pkt_update (node_push cell) d2p d2rest) = true)
      by apply pkt_update_is_single.
    destruct (pkt_update (node_push cell) d2p d2rest)
      as [|ip irest|? ?] eqn:Hpu; cbn in Hsing; try congruence.
    assert (Hnewc : node_color (chain_has_node (CSingle ip irest))
                      (Node KRight [x; y] s2) = gyor_of (length s2))
      by (cbn [chain_has_node]; rewrite node_color_measure; reflexivity).
    destruct (gyor_of (length s2)) eqn:Hg.
    + (* CG *)
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CY: strong push under bundle's ends_green *)
      cbn [cont_green] in Hbundle.
      destruct (@push_chain_preserves A cell (CSingle d2p d2rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hcw Hd2 Hbundle)
        as [_ Hge'].
      cbn [push_chain] in Hge'. rewrite Hpu in Hge'.
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hge'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CO single *)
      cbn [cont_green] in Hbundle. destruct Hbundle as [Hge HparkT].
      destruct (@push_chain_preserves A cell (CSingle d2p d2rest) KOnly
                  ltac:(congruence) ltac:(discriminate) Hcw Hd2 Hge)
        as [_ Hge'].
      cbn [push_chain] in Hge'. rewrite Hpu in Hge'.
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hge'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + contradiction.
  - (* pair child: the cell goes LEFT — the preferred side *)
    cbn [push_chain] in Hwf', Hseq' |- *.
    pose proof Hd2 as Hd2'. cbn [chain_wf] in Hd2'.
    destruct Hd2' as [Hls [Hrs [Hl Hr]]].
    assert (Hlne : d2l <> CEmpty)
      by (destruct d2l; cbn in Hls; congruence).
    assert (Hnewc : node_color
                      (chain_has_node (CPair (push_chain cell d2l) d2r))
                      (Node KRight [x; y] s2) = gyor_of (length s2))
      by (cbn [chain_has_node]; rewrite node_color_measure; reflexivity).
    destruct (gyor_of (length s2)) eqn:Hg.
    + split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CY: the continuation IS the pushed left side — strong push *)
      cbn [cont_green] in Hbundle.
      destruct (@push_chain_preserves A cell d2l KLeft
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hlne; exact Heq)
                  Hcw Hl Hbundle) as [_ Hgl'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact Hgl'.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + (* CO: cont = untouched right; parked left stays green via strong push *)
      cbn [cont_green] in Hbundle. destruct Hbundle as [HgR HgL].
      destruct (@push_chain_preserves A cell d2l KLeft
                  ltac:(congruence)
                  ltac:(intros Heq; exfalso; apply Hlne; exact Heq)
                  Hcw Hl HgL) as [_ Hgl'].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [node_sizes]; split; [reflexivity | lia]
          | split; [cbn; repeat split; assumption | exact Hsw]
          | exact Hwf'
          | unfold root_color_facts; rewrite Hnewc; exact Hgl'].
      * apply tree_of_ends_green; [exact Hwf' |].
        rewrite Hnewc. cbn [cont_green]. exact HgR.
      * rewrite tree_of_seq, cnode_seq_eq, Hseq'. seq_normalize.
    + contradiction.
Qed.

(** Mirror of [make_left_only_total]: the Case 1c/1d RIGHT builder.  The
    1c branch delegates to [right_rebuild_total], converting the min-keyed
    bundle to the suffix key via [child_color_facts_mono]. *)
Lemma make_right_only_total :
  forall A (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A)),
    5 <= length p1 -> 5 <= length s1 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    chain_wf KOnly d1 ->
    (d1 <> CEmpty ->
       child_color_facts (gyor_of (Nat.min (length p1) (length s1))) d1) ->
    exists t,
      make_right_only p1 d1 s1 = Some t /\
      is_single t = true /\
      chain_wf KRight t /\ chain_ends_green t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1.
Proof.
  intros A p1 d1 s1 Hp5 Hs5 Hpw Hsw Hd1 Hbk.
  unfold make_right_only.
  destruct d1 as [|d1p d1r|d1l d1rr].
  - (* 1d: childless *)
    destruct (length p1 <=? 8) eqn:H8.
    + (* <= 8: pop two, everything else joins the suffix *)
      destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
        as [x [y [p1' He]]].
      rewrite He.
      pose proof (buf_pop2_inv He) as Hb.
      rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
      exists (tree_of (Node KRight [x; y] (p1' ++ s1)) CEmpty).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [chain_has_node node_sizes];
            split; [reflexivity | rewrite length_app; lia]
          | split; [cbn; repeat split; assumption
                   | exact (buf_all_wf_app Hp1'w Hsw)]
          | exact I
          | exact I].
      * apply tree_of_ends_green; [exact I | exact I].
      * rewrite tree_of_seq, cnode_seq_eq, Hb. seq_normalize.
    + (* > 8: pop two, eject three, park the SSmall remainder *)
      destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
        as [x [y [p1' He]]].
      rewrite He.
      pose proof (buf_pop2_inv He) as Hb.
      assert (Hlen1 : length p1 = S (S (length p1')))
        by (rewrite Hb; reflexivity).
      apply Nat.leb_gt in H8.
      destruct (@buf_eject3_total (stored A) p1' ltac:(lia))
        as [pmid [a [b [c He3]]]].
      rewrite He3.
      pose proof (buf_eject3_inv He3) as Hb3.
      rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
      assert (Hp1'w' : buf_stored_all_wf (pmid ++ [a; b; c]))
        by (rewrite <- Hb3; exact Hp1'w).
      apply buf_all_wf_app_inv in Hp1'w'.
      destruct Hp1'w' as [Hmw Habc].
      cbn in Habc. destruct Habc as [Haw [Hbw [Hcw _]]].
      assert (Hmlen : 3 <= length pmid).
      { assert (Hl3 : length p1' = length pmid + 3)
          by (rewrite Hb3, length_app; cbn; lia). lia. }
      destruct (small_singleton_wf Hmlen Hmw) as [Hcwf [Hcg Hcseq]].
      assert (Hsufw : buf_stored_all_wf ([a; b; c] ++ s1)).
      { apply buf_all_wf_app; [cbn; repeat split; assumption | exact Hsw]. }
      assert (Hnewc : node_color
                (chain_has_node (push_chain (SSmall pmid) (@CEmpty A)))
                (Node KRight [x; y] ([a; b; c] ++ s1)) = CG).
      { cbn [push_chain chain_has_node].
        rewrite node_color_measure. cbn [node_measure].
        apply gyor_of_big. rewrite length_app. cbn [length]. lia. }
      exists (tree_of (Node KRight [x; y] ([a; b; c] ++ s1))
                (push_chain (SSmall pmid) CEmpty)).
      split; [reflexivity |].
      split; [apply tree_of_is_single |].
      split; [| split].
      * apply tree_of_wf;
          [reflexivity
          | cbn [push_chain chain_has_node node_sizes];
            split; [reflexivity | rewrite length_app; cbn [length]; lia]
          | split; [cbn; repeat split; assumption | exact Hsufw]
          | exact Hcwf
          | unfold root_color_facts; rewrite Hnewc; exact I].
      * apply tree_of_ends_green; [exact Hcwf |].
        rewrite Hnewc. exact I.
      * rewrite tree_of_seq, cnode_seq_eq, Hcseq, Hb, Hb3. seq_normalize.
  - (* 1c, single child *)
    destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
      as [x [y [p1' He]]].
    rewrite He.
    pose proof (buf_pop2_inv He) as Hb.
    assert (Hlen1 : length p1 = S (S (length p1')))
      by (rewrite Hb; reflexivity).
    rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
    assert (Hcellw : stored_wf (SSmall p1')).
    { cbn [stored_wf]. split; [lia | exact Hp1'w]. }
    assert (Hbk2 : child_color_facts (gyor_of (length s1))
                     (CSingle d1p d1r)).
    { apply (@child_color_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_r
        | exact (Hbk ltac:(discriminate))]. }
    destruct (right_rebuild_total Hs5 Hsw Hxw Hyw Hcellw Hd1
                ltac:(discriminate) Hbk2)
      as [Hwt [Hgt Hseqt]].
    exists (tree_of (Node KRight [x; y] s1)
              (push_chain (SSmall p1') (CSingle d1p d1r))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |]. split; [exact Hgt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
  - (* 1c, pair child: same script *)
    destruct (@buf_pop2_total (stored A) p1 ltac:(lia))
      as [x [y [p1' He]]].
    rewrite He.
    pose proof (buf_pop2_inv He) as Hb.
    assert (Hlen1 : length p1 = S (S (length p1')))
      by (rewrite Hb; reflexivity).
    rewrite Hb in Hpw. cbn in Hpw. destruct Hpw as [Hxw [Hyw Hp1'w]].
    assert (Hcellw : stored_wf (SSmall p1')).
    { cbn [stored_wf]. split; [lia | exact Hp1'w]. }
    assert (Hbk2 : child_color_facts (gyor_of (length s1))
                     (CPair d1l d1rr)).
    { apply (@child_color_facts_mono A
               (gyor_of (Nat.min (length p1) (length s1))));
        [apply gyor_of_mono; apply Nat.le_min_r
        | exact (Hbk ltac:(discriminate))]. }
    destruct (right_rebuild_total Hs5 Hsw Hxw Hyw Hcellw Hd1
                ltac:(discriminate) Hbk2)
      as [Hwt [Hgt Hseqt]].
    exists (tree_of (Node KRight [x; y] s1)
              (push_chain (SSmall p1') (CPair d1l d1rr))).
    split; [reflexivity |].
    split; [apply tree_of_is_single |].
    split; [exact Hwt |]. split; [exact Hgt |].
    rewrite Hseqt, stored_seq_SSmall, Hb. seq_normalize.
Qed.

(** Mirror of [make_left_pair_core]: Case 1a's RIGHT core — pop two from
    the left prefix, park the middle (left child included) as one [SBig]
    cell pushed into the right child, rebuild a RIGHT root over it.  The
    bundle is keyed at gyor_of |s2| — exactly the new root's colour. *)
Lemma make_right_pair_core :
  forall A (p1 s1 p2 s2 : buffer (stored A)) (d1 d2 : cchain A),
    5 <= length p1 -> length s1 = 2 ->
    length p2 = 2 -> 5 <= length s2 ->
    buf_stored_all_wf p1 -> buf_stored_all_wf s1 ->
    buf_stored_all_wf p2 -> buf_stored_all_wf s2 ->
    chain_wf KOnly d1 -> chain_wf KOnly d2 -> d2 <> CEmpty ->
    child_color_facts (gyor_of (length s2)) d2 ->
    exists t,
      match buf_pop2 p1 with
      | Some (x, y, p1') =>
          Some (tree_of (Node KRight [x; y] s2)
                  (push_chain (SBig p1' d1 (s1 ++ p2)) d2))
      | None => None
      end = Some t /\
      is_single t = true /\
      chain_wf KRight t /\ chain_ends_green t /\
      cchain_seq t
      = buf_stored_seq p1 ++ cchain_seq d1 ++ buf_stored_seq s1
        ++ buf_stored_seq p2 ++ cchain_seq d2 ++ buf_stored_seq s2.
Proof.
  intros A p1 s1 p2 s2 d1 d2 Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
    Hd1 Hd2 Hne Hbundle.
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
  destruct (right_rebuild_total Hs2 Hs2w Hxw Hyw Hcellw Hd2 Hne Hbundle)
    as [Hwt [Hgt Hseqt]].
  exists (tree_of (Node KRight [x; y] s2)
            (push_chain (SBig p1' d1 (s1 ++ p2)) d2)).
  split; [reflexivity |].
  split; [apply tree_of_is_single |].
  split; [exact Hwt |]. split; [exact Hgt |].
  rewrite Hseqt, Hb, stored_seq_SBig. seq_normalize.
Qed.

(* ========================================================================== *)
(* Cases 2/3, big side (>=8): Admitted sub-obligations.                        *)
(* ========================================================================== *)

Lemma concat_small_left_big :
  forall A (p3 : buffer (stored A)) (e : cchain A),
    8 <= length p3 -> buf_stored_all_wf p3 ->
    chain_wf KOnly e -> chain_ends_green e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists f,
      concat_small_left p3 e = Some f /\
      chain_wf KOnly f /\ chain_ends_green f /\
      cchain_seq f = buf_stored_seq p3 ++ cchain_seq e.
Proof. Admitted.

Lemma concat_small_right_big :
  forall A (d : cchain A) (s3 : buffer (stored A)),
    8 <= length s3 -> buf_stored_all_wf s3 ->
    chain_wf KOnly d -> chain_ends_green d ->
    d <> CEmpty -> degenerate_buf d = None ->
    exists f,
      concat_small_right d s3 = Some f /\
      chain_wf KOnly f /\ chain_ends_green f /\
      cchain_seq f = cchain_seq d ++ buf_stored_seq s3.
Proof. Admitted.

Lemma concat_small_left_total :
  forall A (p3 : buffer (stored A)) (e : cchain A),
    1 <= length p3 -> buf_stored_all_wf p3 ->
    chain_wf KOnly e -> chain_ends_green e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists f,
      concat_small_left p3 e = Some f /\
      chain_wf KOnly f /\ chain_ends_green f /\
      cchain_seq f = buf_stored_seq p3 ++ cchain_seq e.
Proof.
  intros A p3 e Hp Hpw Hwf Hg Hne Hdeg.
  unfold concat_small_left.
  destruct (length p3 <? 8) eqn:H8.
  - destruct (@fold_push_preserves A p3 e Hpw Hwf Hg) as [Hwf' [Hg' Hseq']].
    eexists. split; [reflexivity|]. repeat split; assumption.
  - apply Nat.ltb_ge in H8.
    pose proof (@concat_small_left_big A p3 e H8 Hpw Hwf Hg Hne Hdeg)
      as [f [Hf Hrest]].
    unfold concat_small_left in Hf.
    apply Nat.ltb_ge in H8. rewrite H8 in Hf.
    exists f. split; [exact Hf | exact Hrest].
Qed.

Lemma concat_small_right_total :
  forall A (d : cchain A) (s3 : buffer (stored A)),
    1 <= length s3 -> buf_stored_all_wf s3 ->
    chain_wf KOnly d -> chain_ends_green d ->
    d <> CEmpty -> degenerate_buf d = None ->
    exists f,
      concat_small_right d s3 = Some f /\
      chain_wf KOnly f /\ chain_ends_green f /\
      cchain_seq f = cchain_seq d ++ buf_stored_seq s3.
Proof.
  intros A d s3 Hs Hsw Hwf Hg Hne Hdeg.
  unfold concat_small_right.
  destruct (length s3 <? 8) eqn:H8.
  - destruct (@fold_inject_preserves A s3 d Hsw Hwf Hg) as [Hwf' [Hg' Hseq']].
    eexists. split; [reflexivity|]. repeat split; assumption.
  - apply Nat.ltb_ge in H8.
    pose proof (@concat_small_right_big A d s3 H8 Hsw Hwf Hg Hne Hdeg)
      as [f [Hf Hrest]].
    unfold concat_small_right in Hf.
    apply Nat.ltb_ge in H8. rewrite H8 in Hf.
    exists f. split; [exact Hf | exact Hrest].
Qed.

(* ========================================================================== *)
(* Case 1: the triple builders — Admitted sub-obligations.                     *)
(* ========================================================================== *)

Lemma make_left_total :
  forall A (d : cchain A),
    chain_wf KOnly d -> chain_ends_green d ->
    d <> CEmpty -> degenerate_buf d = None ->
    exists t,
      make_left d = Some t /\
      is_single t = true /\
      chain_wf KLeft t /\ chain_ends_green t /\
      cchain_seq t = cchain_seq d.
Proof.
  intros A d Hwf Hg Hne Hdeg.
  destruct d as [|p r|dl dr]; [congruence | |].
  - (* CSingle: Cases 1c/1d — delegate to make_left_only *)
    cbn [make_left].
    destruct (root_and_child p r) as [[k0 pp ss] child] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hfacts.
    rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
    destruct Hfacts as [Hk [_ [Hnw [Hcw _]]]].
    cbn [node_kind] in Hk. subst k0.
    destruct (root_two_sided Hrc Hwf Hdeg) as [Hp5 Hs5].
    cbn [cnode_wf] in Hnw. destruct Hnw as [Hpw Hsw].
    pose proof (root_child_facts Hwf Hg) as Hbundle.
    rewrite Hrc in Hbundle. cbn [fst snd] in Hbundle.
    assert (Hbk : child <> CEmpty ->
        child_color_facts
          (gyor_of (Nat.min (length pp) (length ss))) child).
    { intros Hcne.
      destruct child as [|? ?|? ?]; [congruence | |];
        cbn [chain_has_node] in Hbundle;
        rewrite node_color_measure in Hbundle;
        cbn [node_measure] in Hbundle; exact Hbundle. }
    destruct (make_left_only_total Hp5 Hs5 Hpw Hsw Hcw Hbk)
      as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
    exists t.
    split; [exact Hmk |]. split; [exact Hsing |].
    split; [exact Hwt |]. split; [exact Hgt |].
    rewrite Hseq.
    rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity.
  - (* CPair: Cases 1a/1b *)
    cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    cbn [make_left].
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 _]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 _]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [Hp1 Hs1]. destruct Hsz2 as [Hp2 Hs2].
    cbn [cnode_wf] in Hnw1, Hnw2.
    destruct Hnw1 as [Hp1w Hs1w]. destruct Hnw2 as [Hp2w Hs2w].
    pose proof (root_child_facts Hl Hgl) as Hb1.
    rewrite Hrc1 in Hb1. cbn [fst snd] in Hb1.
    pose proof (root_child_facts Hr Hgr) as Hb2.
    rewrite Hrc2 in Hb2. cbn [fst snd] in Hb2.
    destruct d1 as [|d1p d1r|d1l d1rr].
    + (* 1b: collapse the childless left tree into one only-triple *)
      assert (Hp5 : 5 <= length (p1 ++ s1 ++ p2))
        by (rewrite !length_app; lia).
      assert (Hpw : buf_stored_all_wf (p1 ++ s1 ++ p2)).
      { apply buf_all_wf_app; [exact Hp1w |].
        apply buf_all_wf_app; [exact Hs1w | exact Hp2w]. }
      assert (Hbk : d2 <> CEmpty ->
          child_color_facts
            (gyor_of (Nat.min (length (p1 ++ s1 ++ p2)) (length s2))) d2).
      { intros Hcne.
        rewrite gyor_of_min_big by (rewrite !length_app; lia).
        destruct d2 as [|? ?|? ?]; [congruence | |];
          cbn [chain_has_node] in Hb2;
          rewrite node_color_measure in Hb2;
          cbn [node_measure] in Hb2; exact Hb2. }
      destruct (make_left_only_total Hp5 Hs2 Hpw Hs2w Hcw2 Hbk)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + (* 1a, single left child: new LEFT root colour = old left-root colour *)
      cbn [chain_has_node] in Hb1.
      rewrite node_color_measure in Hb1. cbn [node_measure] in Hb1.
      destruct (make_left_pair_core Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
                  Hcw1 ltac:(discriminate) Hcw2 Hb1)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + (* 1a, pair left child: same script — the core is shape-generic *)
      cbn [chain_has_node] in Hb1.
      rewrite node_color_measure in Hb1. cbn [node_measure] in Hb1.
      destruct (make_left_pair_core Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
                  Hcw1 ltac:(discriminate) Hcw2 Hb1)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
Qed.

Lemma make_right_total :
  forall A (e : cchain A),
    chain_wf KOnly e -> chain_ends_green e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists u,
      make_right e = Some u /\
      is_single u = true /\
      chain_wf KRight u /\ chain_ends_green u /\
      cchain_seq u = cchain_seq e.
Proof.
  intros A e Hwf Hg Hne Hdeg.
  destruct e as [|p r|dl dr]; [congruence | |].
  - (* CSingle: Cases 1c/1d — delegate to make_right_only *)
    cbn [make_right].
    destruct (root_and_child p r) as [[k0 pp ss] child] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hfacts.
    rewrite Hrc in Hfacts. cbn [fst snd] in Hfacts.
    destruct Hfacts as [Hk [_ [Hnw [Hcw _]]]].
    cbn [node_kind] in Hk. subst k0.
    destruct (root_two_sided Hrc Hwf Hdeg) as [Hp5 Hs5].
    cbn [cnode_wf] in Hnw. destruct Hnw as [Hpw Hsw].
    pose proof (root_child_facts Hwf Hg) as Hbundle.
    rewrite Hrc in Hbundle. cbn [fst snd] in Hbundle.
    assert (Hbk : child <> CEmpty ->
        child_color_facts
          (gyor_of (Nat.min (length pp) (length ss))) child).
    { intros Hcne.
      destruct child as [|? ?|? ?]; [congruence | |];
        cbn [chain_has_node] in Hbundle;
        rewrite node_color_measure in Hbundle;
        cbn [node_measure] in Hbundle; exact Hbundle. }
    destruct (make_right_only_total Hp5 Hs5 Hpw Hsw Hcw Hbk)
      as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
    exists t.
    split; [exact Hmk |]. split; [exact Hsing |].
    split; [exact Hwt |]. split; [exact Hgt |].
    rewrite Hseq.
    rewrite (root_and_child_seq p r), Hrc. cbn [fst snd].
    rewrite cnode_seq_eq. reflexivity.
  - (* CPair: Cases 1a/1b *)
    cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    cbn [chain_ends_green] in Hg. destruct Hg as [Hgl Hgr].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    cbn [make_right].
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [Hnw1 [Hcw1 _]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [Hnw2 [Hcw2 _]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [Hp1 Hs1]. destruct Hsz2 as [Hp2 Hs2].
    cbn [cnode_wf] in Hnw1, Hnw2.
    destruct Hnw1 as [Hp1w Hs1w]. destruct Hnw2 as [Hp2w Hs2w].
    pose proof (root_child_facts Hl Hgl) as Hb1.
    rewrite Hrc1 in Hb1. cbn [fst snd] in Hb1.
    pose proof (root_child_facts Hr Hgr) as Hb2.
    rewrite Hrc2 in Hb2. cbn [fst snd] in Hb2.
    destruct d2 as [|d2p d2r|d2l d2rr].
    + (* 1b: collapse the childless right tree into one only-triple *)
      assert (Hs5 : 5 <= length (s1 ++ p2 ++ s2))
        by (rewrite !length_app; lia).
      assert (Hsw : buf_stored_all_wf (s1 ++ p2 ++ s2)).
      { apply buf_all_wf_app; [exact Hs1w |].
        apply buf_all_wf_app; [exact Hp2w | exact Hs2w]. }
      assert (Hbk : d1 <> CEmpty ->
          child_color_facts
            (gyor_of (Nat.min (length p1) (length (s1 ++ p2 ++ s2)))) d1).
      { intros Hcne.
        rewrite gyor_of_min_big_r by (rewrite !length_app; lia).
        destruct d1 as [|? ?|? ?]; [congruence | |];
          cbn [chain_has_node] in Hb1;
          rewrite node_color_measure in Hb1;
          cbn [node_measure] in Hb1; exact Hb1. }
      destruct (make_right_only_total Hp1 Hs5 Hp1w Hsw Hcw1 Hbk)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + (* 1a, single right child: new RIGHT root colour = old right-root *)
      cbn [chain_has_node] in Hb2.
      rewrite node_color_measure in Hb2. cbn [node_measure] in Hb2.
      destruct (make_right_pair_core Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
                  Hcw1 Hcw2 ltac:(discriminate) Hb2)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
    + (* 1a, pair right child: same script — the core is shape-generic *)
      cbn [chain_has_node] in Hb2.
      rewrite node_color_measure in Hb2. cbn [node_measure] in Hb2.
      destruct (make_right_pair_core Hp1 Hs1 Hp2 Hs2 Hp1w Hs1w Hp2w Hs2w
                  Hcw1 Hcw2 ltac:(discriminate) Hb2)
        as [t [Hmk [Hsing [Hwt [Hgt Hseq]]]]].
      exists t.
      split; [exact Hmk |]. split; [exact Hsing |].
      split; [exact Hwt |]. split; [exact Hgt |].
      rewrite Hseq.
      rewrite (cchain_seq_pair (CSingle pl rl) (CSingle pr rr)).
      rewrite (root_and_child_seq pl rl), Hrc1,
        (root_and_child_seq pr rr), Hrc2.
      cbn [fst snd]. rewrite !cnode_seq_eq. seq_normalize.
Qed.

(* ========================================================================== *)
(* The concat obligation, assembled.                                           *)
(* ========================================================================== *)

Lemma cad_concat_core_total :
  forall A (d e : cchain A),
    chain_wf KOnly d -> chain_ends_green d ->
    chain_wf KOnly e -> chain_ends_green e ->
    d <> CEmpty -> e <> CEmpty ->
    exists f,
      (match degenerate_buf d, degenerate_buf e with
       | Some p, Some s =>
           if (length p <? 8) || (length s <? 8)
           then Some (CSingle (Pkt BHole (Node KOnly (p ++ s) [])) CEmpty)
           else Some (CSingle (Pkt BHole (Node KOnly p s)) CEmpty)
       | Some p, None => concat_small_left p e
       | None, Some s => concat_small_right d s
       | None, None =>
           match make_left d, make_right e with
           | Some t, Some u => Some (CPair t u)
           | _, _ => None
           end
       end) = Some f /\
      (chain_wf KOnly f /\ chain_ends_green f) /\
      cchain_seq f = cchain_seq d ++ cchain_seq e.
Proof.
  intros A d e Hwfd Hgd Hwfe Hge Hdne Hene.
  destruct (degenerate_buf d) as [pb|] eqn:Hdd;
    destruct (degenerate_buf e) as [eb|] eqn:Hde.
  - (* Case 4 *)
    pose proof (degenerate_buf_facts Hwfd Hdd) as [Hp1 [Hpw Hpseq]].
    pose proof (degenerate_buf_facts Hwfe Hde) as [Hs1 [Hsw Hsseq]].
    destruct (concat_case4 Hp1 Hs1 Hpw Hsw) as [f [Hf [Hwf' [Hg' Hseq']]]].
    exists f. rewrite Hf. repeat split; try assumption.
    rewrite Hseq', Hpseq, Hsseq. reflexivity.
  - (* Case 2 *)
    pose proof (degenerate_buf_facts Hwfd Hdd) as [Hp1 [Hpw Hpseq]].
    destruct (concat_small_left_total Hp1 Hpw Hwfe Hge Hene Hde)
      as [f [Hf [Hwf' [Hg' Hseq']]]].
    exists f. rewrite Hf. repeat split; try assumption.
    rewrite Hseq', Hpseq. reflexivity.
  - (* Case 3 *)
    pose proof (degenerate_buf_facts Hwfe Hde) as [Hs1 [Hsw Hsseq]].
    destruct (concat_small_right_total Hs1 Hsw Hwfd Hgd Hdne Hdd)
      as [f [Hf [Hwf' [Hg' Hseq']]]].
    exists f. rewrite Hf. repeat split; try assumption.
    rewrite Hseq', Hsseq. reflexivity.
  - (* Case 1 *)
    destruct (make_left_total Hwfd Hgd Hdne Hdd)
      as [t [Ht [Hts [Htwf [Htg Htseq]]]]].
    destruct (make_right_total Hwfe Hge Hene Hde)
      as [u [Hu [Hus [Huwf [Hug Huseq]]]]].
    exists (CPair t u). rewrite Ht, Hu.
    repeat split; try assumption.
    cbn [cchain_seq]. rewrite Htseq, Huseq. reflexivity.
Qed.

Lemma cad_concat_total :
  forall A (d e : cadeque A),
    J d -> J e ->
    exists f,
      cad_concat d e = Some f /\
      J f /\
      cad_to_list f = cad_to_list d ++ cad_to_list e.
Proof.
  intros A d e [Hwfd Hgd] [Hwfe Hge].
  unfold cad_concat, J, cad_to_list.
  destruct d as [|dp drest|dl dr].
  { exists e. split; [reflexivity|].
    split; [split; [exact Hwfe | exact Hge]|]. reflexivity. }
  - destruct e as [|ep erest|el er].
    { eexists. split; [reflexivity|].
      split; [split; [exact Hwfd | exact Hgd]|].
      cbn [cchain_seq]. rewrite app_nil_r. reflexivity. }
    + exact (cad_concat_core_total Hwfd Hgd Hwfe Hge
               ltac:(discriminate) ltac:(discriminate)).
    + exact (cad_concat_core_total Hwfd Hgd Hwfe Hge
               ltac:(discriminate) ltac:(discriminate)).
  - destruct e as [|ep erest|el er].
    { eexists. split; [reflexivity|].
      split; [split; [exact Hwfd | exact Hgd]|].
      cbn [cchain_seq]. rewrite app_nil_r. reflexivity. }
    + exact (cad_concat_core_total Hwfd Hgd Hwfe Hge
               ltac:(discriminate) ltac:(discriminate)).
    + exact (cad_concat_core_total Hwfd Hgd Hwfe Hge
               ltac:(discriminate) ltac:(discriminate)).
Qed.
