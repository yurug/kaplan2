(** * KTDeque.Catenable.Cost — the cost half of the catenable keystone.

    Buffer-primitive counters mirroring the (now frozen) op code in Ops.v,
    per the design memo Decision 4.  The unit of cost is ONE buffer
    primitive on the underlying noncatenable deque (the proven kt4 deque,
    [deque_wc_o1]): a single-element push/pop/inject/eject, or one pointer
    surgery (root peel / tree_of rebundle / whole-buffer handoff).

    Splices [a ++ b] charge the length of the side the implementation
    MOVES, which at every call site is the bounded one:
    - fold pushes are guarded by [<? 8];
    - the Case-1 builders move ejected/popped pieces of bounded size
      ([|s1| = 2], [|p2| = 2], eject2/eject3 outputs of guarded buffers);
    - the repairs move the DEFICIENT side (red measure 5, or both sides
      [<= 7] by the repair_packet 8-tests) into the drained cell's buffer.

    [node_eject]'s [rev] is a model artifact: the implementation buffer is
    a deque with O(1) back access, so it charges 1.

    Headline: [cat_wc_o1] — every operation costs at most an explicit
    constant on regular ([J]) inputs. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops SeqLemmas WfLemmas
  ConcatLemmas PopLemmas SRLemmas RepairLemmas.

Set Implicit Arguments.

(* ========================================================================== *)
(* Chain-level primitive counters.                                             *)
(* ========================================================================== *)

(** push/inject: peel (1), node update (1), rebundle (1); a pair descends
    into one component first. *)
Fixpoint push_chain_cost {A : Type} (c : cchain A) : nat :=
  match c with
  | CEmpty => 1
  | CSingle _ _ => 3
  | CPair l _ => 1 + push_chain_cost l
  end.

Fixpoint inject_chain_cost {A : Type} (c : cchain A) : nat :=
  match c with
  | CEmpty => 1
  | CSingle _ _ => 3
  | CPair _ r => 1 + inject_chain_cost r
  end.

Lemma push_chain_cost_bound :
  forall A (k : kind) (c : cchain A),
    chain_wf k c -> push_chain_cost c <= 4.
Proof.
  intros A k c Hwf.
  destruct c as [|? ?|l r]; cbn [push_chain_cost]; [lia | lia |].
  cbn [chain_wf] in Hwf. destruct Hwf as [Hls _].
  destruct l as [|? ?|? ?]; cbn [is_single] in Hls; try discriminate.
  cbn [push_chain_cost]. lia.
Qed.

Lemma inject_chain_cost_bound :
  forall A (k : kind) (c : cchain A),
    chain_wf k c -> inject_chain_cost c <= 4.
Proof.
  intros A k c Hwf.
  destruct c as [|? ?|l r]; cbn [inject_chain_cost]; [lia | lia |].
  cbn [chain_wf] in Hwf. destruct Hwf as [_ [Hrs _]].
  destruct r as [|? ?|? ?]; cbn [is_single] in Hrs; try discriminate.
  cbn [inject_chain_cost]. lia.
Qed.

(** Folds: one chain push/inject per element. *)
Definition fold_push_cost {A : Type}
    (b : buffer (stored A)) (c : cchain A) : nat :=
  4 * length b.

Definition fold_inject_cost {A : Type}
    (b : buffer (stored A)) (c : cchain A) : nat :=
  4 * length b.

(* ========================================================================== *)
(* Push / inject (the public ops are one chain operation).                     *)
(* ========================================================================== *)

Definition cad_push_cost {A : Type} (x : A) (d : cadeque A) : nat :=
  push_chain_cost d.

Definition cad_inject_cost {A : Type} (d : cadeque A) (x : A) : nat :=
  inject_chain_cost d.

Lemma cad_push_cost_bound :
  forall A (x : A) (d : cadeque A), J d -> cad_push_cost x d <= 4.
Proof.
  intros A x d [Hwf _]. exact (push_chain_cost_bound Hwf).
Qed.

Lemma cad_inject_cost_bound :
  forall A (d : cadeque A) (x : A), J d -> cad_inject_cost d x <= 4.
Proof.
  intros A d x [Hwf _]. exact (inject_chain_cost_bound Hwf).
Qed.

(* ========================================================================== *)
(* Concat costs.  Counters DOMINATE the per-branch work (a branch may be      *)
(* charged its worst sibling), which is sound for upper bounds.                *)
(* ========================================================================== *)

Definition make_left_only_cost {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : nat :=
  match d1 with
  | CEmpty =>
      if length s1 <=? 8
      then 3 + length s1          (* eject2 + move s1' + rebundle *)
      else 8                      (* eject2 + move [a;b;c] + park + rebundle *)
  | _ => 3 + inject_chain_cost d1 (* eject2 + park + inject + rebundle *)
  end.

Definition make_right_only_cost {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : nat :=
  match d1 with
  | CEmpty =>
      if length p1 <=? 8
      then 3 + length p1
      else 8
  | _ => 3 + push_chain_cost d1
  end.

Lemma make_left_only_cost_bound :
  forall A (p1 : buffer (stored A)) (d1 : cchain A)
         (s1 : buffer (stored A)),
    chain_wf KOnly d1 ->
    make_left_only_cost p1 d1 s1 <= 11.
Proof.
  intros A p1 d1 s1 Hwf.
  unfold make_left_only_cost.
  destruct d1 as [|? ?|? ?].
  - destruct (length s1 <=? 8) eqn:H8; [apply Nat.leb_le in H8 |]; lia.
  - pose proof (inject_chain_cost_bound Hwf). lia.
  - pose proof (inject_chain_cost_bound Hwf). lia.
Qed.

Lemma make_right_only_cost_bound :
  forall A (p1 : buffer (stored A)) (d1 : cchain A)
         (s1 : buffer (stored A)),
    chain_wf KOnly d1 ->
    make_right_only_cost p1 d1 s1 <= 11.
Proof.
  intros A p1 d1 s1 Hwf.
  unfold make_right_only_cost.
  destruct d1 as [|? ?|? ?].
  - destruct (length p1 <=? 8) eqn:H8; [apply Nat.leb_le in H8 |]; lia.
  - pose proof (push_chain_cost_bound Hwf). lia.
  - pose proof (push_chain_cost_bound Hwf). lia.
Qed.

Definition make_left_cost {A : Type} (d : cchain A) : nat :=
  match d with
  | CEmpty => 0
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => 1 + make_left_only_cost p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d1 with
          | CEmpty =>
              2 + length s1 + length p2 + make_left_only_cost (p1 ++ s1 ++ p2) d2 s2
          | _ =>
              2 + length s1 + length p2 + 3 + inject_chain_cost d1
          end
      end
  | CPair _ _ => 0
  end.

Definition make_right_cost {A : Type} (e : cchain A) : nat :=
  match e with
  | CEmpty => 0
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => 1 + make_right_only_cost p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d2 with
          | CEmpty =>
              2 + length s1 + length p2 + make_right_only_cost p1 d1 (s1 ++ p2 ++ s2)
          | _ =>
              2 + length s1 + length p2 + 3 + push_chain_cost d2
          end
      end
  | CPair _ _ => 0
  end.

Lemma make_left_cost_bound :
  forall A (d : cchain A),
    chain_wf KOnly d ->
    make_left_cost d <= 20.
Proof.
  intros A d Hwf.
  destruct d as [|p r|dl dr]; cbn [make_left_cost]; [lia | |].
  - destruct (root_and_child p r) as [[k0 p1 s1] d1] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    pose proof (make_left_only_cost_bound p1 s1 Hcw). lia.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [_ [Hcw1 _]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [_ [Hcw2 _]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [_ Hs1]. destruct Hsz2 as [Hp2 _].
    destruct d1 as [|? ?|? ?].
    + pose proof (make_left_only_cost_bound (p1 ++ s1 ++ p2) s2 Hcw2).
      lia.
    + pose proof (inject_chain_cost_bound Hcw1). lia.
    + pose proof (inject_chain_cost_bound Hcw1). lia.
Qed.

Lemma make_right_cost_bound :
  forall A (e : cchain A),
    chain_wf KOnly e ->
    make_right_cost e <= 20.
Proof.
  intros A e Hwf.
  destruct e as [|p r|dl dr]; cbn [make_right_cost]; [lia | |].
  - destruct (root_and_child p r) as [[k0 p1 s1] d1] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    pose proof (make_right_only_cost_bound p1 s1 Hcw). lia.
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [Hrs [Hl Hr]]].
    destruct dl as [|pl rl|? ?]; cbn [is_single] in Hls; try discriminate.
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs; try discriminate.
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1] eqn:Hrc1.
    destruct (root_and_child pr rr) as [[k2 p2 s2] d2] eqn:Hrc2.
    pose proof (root_and_child_facts Hl) as Hf1.
    rewrite Hrc1 in Hf1. cbn [fst snd] in Hf1.
    destruct Hf1 as [Hk1 [Hsz1 [_ [Hcw1 _]]]].
    pose proof (root_and_child_facts Hr) as Hf2.
    rewrite Hrc2 in Hf2. cbn [fst snd] in Hf2.
    destruct Hf2 as [Hk2 [Hsz2 [_ [Hcw2 _]]]].
    cbn [node_kind] in Hk1, Hk2. subst k1 k2.
    cbn [node_sizes] in Hsz1, Hsz2.
    destruct Hsz1 as [_ Hs1]. destruct Hsz2 as [Hp2 _].
    destruct d2 as [|? ?|? ?].
    + pose proof (make_right_only_cost_bound p1 (s1 ++ p2 ++ s2) Hcw1).
      lia.
    + pose proof (push_chain_cost_bound Hcw2). lia.
    + pose proof (push_chain_cost_bound Hcw2). lia.
Qed.

Definition concat_small_left_cost {A : Type}
    (p3 : buffer (stored A)) (e : cchain A) : nat :=
  if length p3 <? 8
  then 4 * length p3
  else
    match e with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p2 s2, d2) =>
            match d2 with
            | CEmpty => 1 + 5            (* peel + eject2 + move + rebundle *)
            | _ => 1 + 2 + push_chain_cost d2
            end
        end
    | CPair (CSingle pl rl) rt =>
        match root_and_child pl rl with
        | (Node _ p2 s2, d2) => 1 + 2 + push_chain_cost d2
        end
    | _ => 0
    end.

Definition concat_small_right_cost {A : Type}
    (d : cchain A) (s3 : buffer (stored A)) : nat :=
  if length s3 <? 8
  then 4 * length s3
  else
    match d with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p1 s1, d1) =>
            match d1 with
            | CEmpty => 1 + 5
            | _ => 1 + 2 + inject_chain_cost d1
            end
        end
    | CPair lt (CSingle pr rr) =>
        match root_and_child pr rr with
        | (Node _ p1 s1, d1) => 1 + 2 + inject_chain_cost d1
        end
    | _ => 0
    end.

Lemma concat_small_left_cost_bound :
  forall A (p3 : buffer (stored A)) (e : cchain A),
    chain_wf KOnly e ->
    concat_small_left_cost p3 e <= 28.
Proof.
  intros A p3 e Hwf.
  unfold concat_small_left_cost.
  destruct (length p3 <? 8) eqn:H8.
  { apply Nat.ltb_lt in H8. lia. }
  destruct e as [|p r|el er]; [lia | |].
  - destruct (root_and_child p r) as [[k0 p2 s2] d2] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    destruct d2 as [|? ?|? ?];
      [lia | pose proof (push_chain_cost_bound Hcw); lia
       | pose proof (push_chain_cost_bound Hcw); lia].
  - cbn [chain_wf] in Hwf. destruct Hwf as [Hls [_ [Hl _]]].
    destruct el as [|pl rl|? ?]; cbn [is_single] in Hls;
      try discriminate.
    destruct (root_and_child pl rl) as [[k1 p2 s2] d2] eqn:Hrc.
    pose proof (root_and_child_facts Hl) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    pose proof (push_chain_cost_bound Hcw). lia.
Qed.

Lemma concat_small_right_cost_bound :
  forall A (d : cchain A) (s3 : buffer (stored A)),
    chain_wf KOnly d ->
    concat_small_right_cost d s3 <= 28.
Proof.
  intros A d s3 Hwf.
  unfold concat_small_right_cost.
  destruct (length s3 <? 8) eqn:H8.
  { apply Nat.ltb_lt in H8. lia. }
  destruct d as [|p r|dl dr]; [lia | |].
  - destruct (root_and_child p r) as [[k0 p1 s1] d1] eqn:Hrc.
    pose proof (root_and_child_facts Hwf) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    destruct d1 as [|? ?|? ?];
      [lia | pose proof (inject_chain_cost_bound Hcw); lia
       | pose proof (inject_chain_cost_bound Hcw); lia].
  - cbn [chain_wf] in Hwf. destruct Hwf as [_ [Hrs [_ Hr]]].
    destruct dr as [|pr rr|? ?]; cbn [is_single] in Hrs;
      try discriminate.
    destruct (root_and_child pr rr) as [[k2 p1 s1] d1] eqn:Hrc.
    pose proof (root_and_child_facts Hr) as Hf.
    rewrite Hrc in Hf. cbn [fst snd] in Hf.
    destruct Hf as [_ [_ [_ [Hcw _]]]].
    pose proof (inject_chain_cost_bound Hcw). lia.
Qed.

Definition cad_concat_cost {A : Type} (d e : cadeque A) : nat :=
  match d, e with
  | CEmpty, _ => 0
  | _, CEmpty => 0
  | _, _ =>
      2 +
      match degenerate_buf d, degenerate_buf e with
      | Some p, Some s =>
          if (length p <? 8) || (length s <? 8)
          then 1 + Nat.min (length p) (length s)
          else 1
      | Some p, None => concat_small_left_cost p e
      | None, Some s => concat_small_right_cost d s
      | None, None => 1 + make_left_cost d + make_right_cost e
      end
  end.

Lemma cad_concat_cost_bound :
  forall A (d e : cadeque A),
    chain_wf KOnly d -> chain_wf KOnly e ->
    cad_concat_cost d e <= 43.
Proof.
  intros A d e Hwfd Hwfe.
  assert (Hcore :
    2 + match degenerate_buf d, degenerate_buf e with
        | Some p, Some s =>
            if (length p <? 8) || (length s <? 8)
            then 1 + Nat.min (length p) (length s)
            else 1
        | Some p, None => concat_small_left_cost p e
        | None, Some s => concat_small_right_cost d s
        | None, None => 1 + make_left_cost d + make_right_cost e
        end <= 43).
  { destruct (degenerate_buf d) as [p|] eqn:Hdd;
      destruct (degenerate_buf e) as [s|] eqn:Hde.
    - (* case 4: the merge moves the smaller side, < 8 by the guard *)
      destruct ((length p <? 8) || (length s <? 8)) eqn:Hsm; [| lia].
      apply Bool.orb_true_iff in Hsm.
      destruct Hsm as [H|H]; apply Nat.ltb_lt in H; lia.
    - pose proof (concat_small_left_cost_bound p Hwfe). lia.
    - pose proof (concat_small_right_cost_bound s Hwfd). lia.
    - pose proof (make_left_cost_bound Hwfd).
      pose proof (make_right_cost_bound Hwfe). lia. }
  unfold cad_concat_cost.
  destruct d as [|? ?|? ?]; [lia | |];
    (destruct e as [|? ?|? ?]; [lia | exact Hcore | exact Hcore]).
Qed.
