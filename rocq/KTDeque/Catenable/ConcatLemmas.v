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
Proof. Admitted.

Lemma make_right_total :
  forall A (e : cchain A),
    chain_wf KOnly e -> chain_ends_green e ->
    e <> CEmpty -> degenerate_buf e = None ->
    exists u,
      make_right e = Some u /\
      is_single u = true /\
      chain_wf KRight u /\ chain_ends_green u /\
      cchain_seq u = cchain_seq e.
Proof. Admitted.

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
