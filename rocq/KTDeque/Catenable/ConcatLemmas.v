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
