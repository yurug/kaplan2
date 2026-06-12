(** * KTDeque.Catenable.OpsFast — the §6 ops against buffer primitives.

    A 1:1 mirror of Ops.v in which every buffer access goes through the
    named primitives of BufPrims.v (no list constructor, literal, match,
    [length], [++], [rev] or fold touches a buffer directly).  Each
    mirrored function comes with an [_eq] lemma proving it EQUAL to the
    frozen original — the lemmas are the machine-checked diff of the
    port, and they transfer the keystone + cost theorems to the fast
    family for free (FastKeystone.v).

    Extraction (Extract/ExtractionFast.v) remaps [buffer] and the
    primitives to the production buffer (the proven §4 deque plus an
    O(1) size field), turning every [bsize] colour test into an int
    compare and every end access into a WC O(1) deque op. *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims.

Set Implicit Arguments.

(* ========================================================================== *)
(* Colour, rebundling, push / inject.                                          *)
(* ========================================================================== *)

Definition node_color_f {A : Type} (has_child : bool) (n : cnode A) : gyor :=
  if negb has_child then CG
  else
    match n with
    | Node k p s =>
        let m :=
          match k with
          | KLeft => bsize p
          | KRight => bsize s
          | KOnly => Nat.min (bsize p) (bsize s)
          end
        in
        if 8 <=? m then CG
        else if m =? 7 then CY
        else if m =? 6 then CO
        else CR
    end.

Lemma node_color_f_eq : forall A hc (n : cnode A),
    node_color_f hc n = node_color hc n.
Proof. reflexivity. Qed.

Definition tree_of_f {A : Type} (n : cnode A) (child : cchain A) : cchain A :=
  match node_color_f (chain_has_node child) n with
  | CG | CR => CSingle (Pkt BHole n) child
  | CY =>
      match child with
      | CSingle (Pkt rb rn) rrest => CSingle (Pkt (BSingle n rb) rn) rrest
      | CPair (CSingle (Pkt lb ln) lrest) r =>
          CSingle (Pkt (BPairY n lb r) ln) lrest
      | _ => CSingle (Pkt BHole n) child
      end
  | CO =>
      match child with
      | CSingle (Pkt rb rn) rrest => CSingle (Pkt (BSingle n rb) rn) rrest
      | CPair l (CSingle (Pkt rb rn) rrest) =>
          CSingle (Pkt (BPairO n l rb) rn) rrest
      | _ => CSingle (Pkt BHole n) child
      end
  end.

Lemma tree_of_f_eq : forall A (n : cnode A) child,
    tree_of_f n child = tree_of n child.
Proof. reflexivity. Qed.

Definition pkt_update_f {A : Type}
    (upd : cnode A -> cnode A) (p : cpacket A) (rest : cchain A) : cchain A :=
  let '(n, child) := root_and_child p rest in
  tree_of_f (upd n) child.

Lemma pkt_update_f_ext : forall A (updf upd : cnode A -> cnode A) p rest,
    (forall n, updf n = upd n) ->
    pkt_update_f updf p rest = pkt_update upd p rest.
Proof.
  intros A updf upd p rest Hu.
  unfold pkt_update_f, pkt_update.
  destruct (root_and_child p rest) as [n child].
  rewrite Hu, tree_of_f_eq. reflexivity.
Qed.

Definition node_push_f {A : Type} (s : stored A) (n : cnode A) : cnode A :=
  match n with
  | Node k p suf =>
      if bis_empty p
      then Node k p (bpush s suf)
      else Node k (bpush s p) suf
  end.

Lemma node_push_f_eq : forall A (s : stored A) n,
    node_push_f s n = node_push s n.
Proof.
  intros A s [k p suf]. destruct p; reflexivity.
Qed.

Definition node_inject_f {A : Type} (n : cnode A) (s : stored A) : cnode A :=
  match n with
  | Node k p suf =>
      if bis_empty suf
      then Node k (binject p s) suf
      else Node k p (binject suf s)
  end.

Lemma node_inject_f_eq : forall A (n : cnode A) s,
    node_inject_f n s = node_inject n s.
Proof.
  intros A [k p suf] s. destruct suf; reflexivity.
Qed.

Fixpoint push_chain_f {A : Type} (s : stored A) (c : cchain A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly (b1 s) bempty)) CEmpty
  | CSingle p rest => pkt_update_f (node_push_f s) p rest
  | CPair l r => CPair (push_chain_f s l) r
  end.

Lemma push_chain_f_eq : forall A (s : stored A) c,
    push_chain_f s c = push_chain s c.
Proof.
  intros A s c. revert s.
  induction c as [| p rest _ | l IHl r _]; intros s; cbn.
  - reflexivity.
  - apply pkt_update_f_ext. intros n. apply node_push_f_eq.
  - rewrite IHl. reflexivity.
Qed.

Fixpoint inject_chain_f {A : Type} (c : cchain A) (s : stored A) : cchain A :=
  match c with
  | CEmpty => CSingle (Pkt BHole (Node KOnly bempty (b1 s))) CEmpty
  | CSingle p rest => pkt_update_f (fun n => node_inject_f n s) p rest
  | CPair l r => CPair l (inject_chain_f r s)
  end.

Lemma inject_chain_f_eq : forall A (c : cchain A) (s : stored A),
    inject_chain_f c s = inject_chain c s.
Proof.
  intros A c. induction c as [| p rest _ | l _ r IHr]; intros s; cbn.
  - reflexivity.
  - apply pkt_update_f_ext. intros n. apply node_inject_f_eq.
  - rewrite IHr. reflexivity.
Qed.

Definition cad_push_f {A : Type} (x : A) (d : cadeque A) : cadeque A :=
  push_chain_f (SGround x) d.

Lemma cad_push_f_eq : forall A (x : A) d, cad_push_f x d = cad_push x d.
Proof. intros. apply push_chain_f_eq. Qed.

Definition cad_inject_f {A : Type} (d : cadeque A) (x : A) : cadeque A :=
  inject_chain_f d (SGround x).

Lemma cad_inject_f_eq : forall A (d : cadeque A) x,
    cad_inject_f d x = cad_inject d x.
Proof. intros. apply inject_chain_f_eq. Qed.

(* ========================================================================== *)
(* Concat.                                                                     *)
(* ========================================================================== *)

(** The bounded multi-transfers are primitives outright; Ops.v's local
    definitions have the same bodies. *)
Lemma bpop2_eq : forall X (b : buffer X), bpop2 b = buf_pop2 b.
Proof. reflexivity. Qed.

Lemma beject2_eq : forall X (b : buffer X), beject2 b = buf_eject2 b.
Proof. reflexivity. Qed.

Lemma beject3_eq : forall X (b : buffer X), beject3 b = buf_eject3 b.
Proof. reflexivity. Qed.

Definition degenerate_buf_f {A : Type} (d : cchain A)
    : option (buffer (stored A)) :=
  match d with
  | CSingle (Pkt BHole (Node KOnly p s)) CEmpty =>
      if bis_empty p then Some s
      else if bis_empty s then Some p
      else None
  | _ => None
  end.

Lemma degenerate_buf_f_eq : forall A (d : cchain A),
    degenerate_buf_f d = degenerate_buf d.
Proof.
  intros A d.
  destruct d as [| [b n] rest |]; try reflexivity.
  destruct b; try reflexivity.
  destruct n as [k p s]; destruct k; try reflexivity.
  destruct rest; try reflexivity.
  destruct p; destruct s; reflexivity.
Qed.

Definition make_left_only_f {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : option (cchain A) :=
  match d1 with
  | CEmpty =>
      if bsize s1 <=? 8 then
        match beject2 s1 with
        | Some (s1', y, z) =>
            Some (tree_of_f (Node KLeft (bapp p1 s1') (b2 y z)) CEmpty)
        | None => None
        end
      else
        match bpop s1 with
        | Some (a, t1) =>
            match bpop t1 with
            | Some (b, t2) =>
                match bpop t2 with
                | Some (c, srest) =>
                    match beject2 srest with
                    | Some (smid, y, z) =>
                        Some (tree_of_f (Node KLeft (bapp p1 (b3 a b c))
                                           (b2 y z))
                                (push_chain_f (SSmall smid) CEmpty))
                    | None => None
                    end
                | None => None
                end
            | None => None
            end
        | None => None
        end
  | _ =>
      match beject2 s1 with
      | Some (s1', y, z) =>
          Some (tree_of_f (Node KLeft p1 (b2 y z))
                  (inject_chain_f d1 (SSmall s1')))
      | None => None
      end
  end.

Lemma make_left_only_f_eq : forall A p1 (d1 : cchain A) s1,
    make_left_only_f p1 d1 s1 = make_left_only p1 d1 s1.
Proof.
  intros A p1 d1 s1.
  unfold make_left_only_f, make_left_only.
  destruct d1 as [| p rest | l r].
  - change (bsize s1) with (length s1).
    destruct (length s1 <=? 8).
    + rewrite beject2_eq.
      destruct (buf_eject2 s1) as [[[s1' y] z]|]; [|reflexivity].
      rewrite tree_of_f_eq. reflexivity.
    + destruct s1 as [| a [| b [| c srest]]]; reflexivity.
  - rewrite beject2_eq.
    destruct (buf_eject2 s1) as [[[s1' y] z]|]; [|reflexivity].
    rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
  - rewrite beject2_eq.
    destruct (buf_eject2 s1) as [[[s1' y] z]|]; [|reflexivity].
    rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
Qed.

Definition make_left_f {A : Type} (d : cchain A) : option (cchain A) :=
  match d with
  | CEmpty => None
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => make_left_only_f p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d1 with
          | CEmpty =>
              make_left_only_f (bapp p1 (bapp s1 p2)) d2 s2
          | _ =>
              match beject2 s2 with
              | Some (s2', y, z) =>
                  Some (tree_of_f (Node KLeft p1 (b2 y z))
                          (inject_chain_f d1 (SBig (bapp s1 p2) d2 s2')))
              | None => None
              end
          end
      end
  | CPair _ _ => None
  end.

Lemma make_left_f_eq : forall A (d : cchain A), make_left_f d = make_left d.
Proof.
  intros A d.
  unfold make_left_f, make_left.
  destruct d as [| p r | l rr]; try reflexivity.
  - destruct (root_and_child p r) as [[k1 p1 s1] d1].
    apply make_left_only_f_eq.
  - destruct l as [| pl rl |]; try reflexivity.
    destruct rr as [| pr rr2 |]; try reflexivity.
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1].
    destruct (root_and_child pr rr2) as [[k2 p2 s2] d2].
    destruct d1 as [| pp rrest | ll rrr].
    + apply make_left_only_f_eq.
    + rewrite beject2_eq.
      destruct (buf_eject2 s2) as [[[s2' y] z]|]; [|reflexivity].
      rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
    + rewrite beject2_eq.
      destruct (buf_eject2 s2) as [[[s2' y] z]|]; [|reflexivity].
      rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
Qed.

Definition make_right_only_f {A : Type}
    (p1 : buffer (stored A)) (d1 : cchain A) (s1 : buffer (stored A))
    : option (cchain A) :=
  match d1 with
  | CEmpty =>
      if bsize p1 <=? 8 then
        match bpop2 p1 with
        | Some (x, y, p1') =>
            Some (tree_of_f (Node KRight (b2 x y) (bapp p1' s1)) CEmpty)
        | None => None
        end
      else
        match bpop2 p1 with
        | Some (x, y, p1') =>
            match beject3 p1' with
            | Some (pmid, a, b, c) =>
                Some (tree_of_f (Node KRight (b2 x y) (bapp (b3 a b c) s1))
                        (push_chain_f (SSmall pmid) CEmpty))
            | None => None
            end
        | None => None
        end
  | _ =>
      match bpop2 p1 with
      | Some (x, y, p1') =>
          Some (tree_of_f (Node KRight (b2 x y) s1)
                  (push_chain_f (SSmall p1') d1))
      | None => None
      end
  end.

Lemma make_right_only_f_eq : forall A p1 (d1 : cchain A) s1,
    make_right_only_f p1 d1 s1 = make_right_only p1 d1 s1.
Proof.
  intros A p1 d1 s1.
  unfold make_right_only_f, make_right_only.
  destruct d1 as [| p rest | l r].
  - change (bsize p1) with (length p1).
    destruct (length p1 <=? 8).
    + rewrite bpop2_eq.
      destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
      rewrite tree_of_f_eq. reflexivity.
    + rewrite bpop2_eq.
      destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
      rewrite beject3_eq.
      destruct (buf_eject3 p1') as [[[[pmid a] b] c]|]; [|reflexivity].
      rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
  - rewrite bpop2_eq.
    destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
    rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
  - rewrite bpop2_eq.
    destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
    rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
Qed.

Definition make_right_f {A : Type} (e : cchain A) : option (cchain A) :=
  match e with
  | CEmpty => None
  | CSingle p r =>
      match root_and_child p r with
      | (Node _ p1 s1, d1) => make_right_only_f p1 d1 s1
      end
  | CPair (CSingle pl rl) (CSingle pr rr) =>
      match root_and_child pl rl, root_and_child pr rr with
      | (Node _ p1 s1, d1), (Node _ p2 s2, d2) =>
          match d2 with
          | CEmpty =>
              make_right_only_f p1 d1 (bapp s1 (bapp p2 s2))
          | _ =>
              match bpop2 p1 with
              | Some (x, y, p1') =>
                  Some (tree_of_f (Node KRight (b2 x y) s2)
                          (push_chain_f (SBig p1' d1 (bapp s1 p2)) d2))
              | None => None
              end
          end
      end
  | CPair _ _ => None
  end.

Lemma make_right_f_eq : forall A (e : cchain A), make_right_f e = make_right e.
Proof.
  intros A e.
  unfold make_right_f, make_right.
  destruct e as [| p r | l rr]; try reflexivity.
  - destruct (root_and_child p r) as [[k1 p1 s1] d1].
    apply make_right_only_f_eq.
  - destruct l as [| pl rl |]; try reflexivity.
    destruct rr as [| pr rr2 |]; try reflexivity.
    destruct (root_and_child pl rl) as [[k1 p1 s1] d1].
    destruct (root_and_child pr rr2) as [[k2 p2 s2] d2].
    destruct d2 as [| pp rrest | ll rrr].
    + apply make_right_only_f_eq.
    + rewrite bpop2_eq.
      destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
      rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
    + rewrite bpop2_eq.
      destruct (buf_pop2 p1) as [[[x y] p1']|]; [|reflexivity].
      rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
Qed.

Lemma bfold_right_push_eq : forall A (e : cchain A) (b : buffer (stored A)),
    bfold_right push_chain_f e b = fold_right push_chain e b.
Proof.
  intros A e b. unfold bfold_right.
  induction b as [| x b IH]; cbn [fold_right]; [reflexivity|].
  rewrite IH, push_chain_f_eq. reflexivity.
Qed.

Lemma bfold_left_inject_eq : forall A (b : buffer (stored A)) (d : cchain A),
    bfold_left inject_chain_f b d = fold_left inject_chain b d.
Proof.
  intros A b. unfold bfold_left.
  induction b as [| x b IH]; intros d; cbn [fold_left]; [reflexivity|].
  rewrite inject_chain_f_eq. apply IH.
Qed.

Definition concat_small_left_f {A : Type}
    (p3 : buffer (stored A)) (e : cchain A) : option (cchain A) :=
  if bsize p3 <? 8 then Some (bfold_right push_chain_f e p3)
  else
    match e with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p2 s2, d2) =>
            match d2 with
            | CEmpty =>
                match beject2 p2 with
                | Some (p2', y, z) =>
                    Some (tree_of_f (Node KOnly p3 (bpush y (bpush z s2)))
                            (push_chain_f (SSmall p2') CEmpty))
                | None => None
                end
            | _ =>
                Some (tree_of_f (Node KOnly p3 s2)
                        (push_chain_f (SSmall p2) d2))
            end
        end
    | CPair (CSingle pl rl) rt =>
        match root_and_child pl rl with
        | (Node _ p2 s2, d2) =>
            Some (CPair (tree_of_f (Node KLeft p3 s2)
                           (push_chain_f (SSmall p2) d2)) rt)
        end
    | _ => None
    end.

Lemma concat_small_left_f_eq : forall A p3 (e : cchain A),
    concat_small_left_f p3 e = concat_small_left p3 e.
Proof.
  intros A p3 e.
  unfold concat_small_left_f, concat_small_left.
  change (bsize p3) with (length p3).
  destruct (length p3 <? 8).
  - rewrite bfold_right_push_eq. reflexivity.
  - destruct e as [| p r | l rt]; try reflexivity.
    + destruct (root_and_child p r) as [[k2 p2 s2] d2].
      destruct d2 as [| pp rrest | ll rrr].
      * rewrite beject2_eq.
        destruct (buf_eject2 p2) as [[[p2' y] z]|]; [|reflexivity].
        rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
      * rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
      * rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
    + destruct l as [| pl rl |]; try reflexivity.
      destruct (root_and_child pl rl) as [[k2 p2 s2] d2].
      rewrite tree_of_f_eq, push_chain_f_eq. reflexivity.
Qed.

Definition concat_small_right_f {A : Type}
    (d : cchain A) (s3 : buffer (stored A)) : option (cchain A) :=
  if bsize s3 <? 8 then Some (bfold_left inject_chain_f s3 d)
  else
    match d with
    | CSingle p r =>
        match root_and_child p r with
        | (Node _ p1 s1, d1) =>
            match d1 with
            | CEmpty =>
                match bpop2 s1 with
                | Some (x, y, s1') =>
                    Some (tree_of_f
                            (Node KOnly (binject (binject p1 x) y) s3)
                            (push_chain_f (SSmall s1') CEmpty))
                | None => None
                end
            | _ =>
                Some (tree_of_f (Node KOnly p1 s3)
                        (inject_chain_f d1 (SSmall s1)))
            end
        end
    | CPair lt (CSingle pr rr) =>
        match root_and_child pr rr with
        | (Node _ p1 s1, d1) =>
            Some (CPair lt (tree_of_f (Node KRight p1 s3)
                              (inject_chain_f d1 (SSmall s1))))
        end
    | _ => None
    end.

Lemma binject2_app : forall X (p : buffer X) x y,
    binject (binject p x) y = p ++ [x; y].
Proof.
  intros X p x y. unfold binject. rewrite <- app_assoc. reflexivity.
Qed.

Lemma concat_small_right_f_eq : forall A (d : cchain A) s3,
    concat_small_right_f d s3 = concat_small_right d s3.
Proof.
  intros A d s3.
  unfold concat_small_right_f, concat_small_right.
  change (bsize s3) with (length s3).
  destruct (length s3 <? 8).
  - rewrite bfold_left_inject_eq. reflexivity.
  - destruct d as [| p r | lt rt]; try reflexivity.
    + destruct (root_and_child p r) as [[k1 p1 s1] d1].
      destruct d1 as [| pp rrest | ll rrr].
      * rewrite bpop2_eq.
        destruct (buf_pop2 s1) as [[[x y] s1']|]; [|reflexivity].
        rewrite tree_of_f_eq, push_chain_f_eq, binject2_app. reflexivity.
      * rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
      * rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
    + destruct rt as [| pr rr |]; try reflexivity.
      destruct (root_and_child pr rr) as [[k1 p1 s1] d1].
      rewrite tree_of_f_eq, inject_chain_f_eq. reflexivity.
Qed.

Definition cad_concat_f {A : Type} (d e : cadeque A) : option (cadeque A) :=
  match d, e with
  | CEmpty, _ => Some e
  | _, CEmpty => Some d
  | _, _ =>
      match degenerate_buf_f d, degenerate_buf_f e with
      | Some p, Some s =>
          if (bsize p <? 8) || (bsize s <? 8)
          then Some (CSingle (Pkt BHole (Node KOnly (bapp p s) bempty))
                       CEmpty)
          else Some (CSingle (Pkt BHole (Node KOnly p s)) CEmpty)
      | Some p, None => concat_small_left_f p e
      | None, Some s => concat_small_right_f d s
      | None, None =>
          match make_left_f d, make_right_f e with
          | Some t, Some u => Some (CPair t u)
          | _, _ => None
          end
      end
  end.

Lemma cad_concat_f_eq : forall A (d e : cadeque A),
    cad_concat_f d e = cad_concat d e.
Proof.
  intros A d e.
  unfold cad_concat_f, cad_concat.
  destruct d as [| pd rd | ld rrd]; [reflexivity| |];
    (destruct e as [| pe re | le rre]; [reflexivity| |]);
    rewrite !degenerate_buf_f_eq;
    repeat match goal with
           | |- context [match degenerate_buf ?x with _ => _ end] =>
               destruct (degenerate_buf x)
           end;
    try reflexivity;
    try apply concat_small_left_f_eq;
    try apply concat_small_right_f_eq;
    rewrite make_left_f_eq, make_right_f_eq; reflexivity.
Qed.

(* ========================================================================== *)
(* Pop / eject with repair.                                                    *)
(* ========================================================================== *)

Definition node_pop_f {A : Type} (n : cnode A) : option (stored A * cnode A) :=
  match n with
  | Node k p s =>
      match bpop p with
      | Some (x, p') => Some (x, Node k p' s)
      | None =>
          match bpop s with
          | Some (x, s') => Some (x, Node k p s')
          | None => None
          end
      end
  end.

Lemma node_pop_f_eq : forall A (n : cnode A), node_pop_f n = node_pop n.
Proof.
  intros A [k p s]. destruct p; [destruct s|]; reflexivity.
Qed.

Definition node_eject_f {A : Type} (n : cnode A)
    : option (cnode A * stored A) :=
  match n with
  | Node k p s =>
      match beject s with
      | Some (s', x) => Some (Node k p s', x)
      | None =>
          match beject p with
          | Some (p', x) => Some (Node k p' bempty, x)
          | None => None
          end
      end
  end.

Lemma node_eject_f_eq : forall A (n : cnode A), node_eject_f n = node_eject n.
Proof.
  intros A [k p s].
  unfold node_eject_f, node_eject, beject.
  destruct (rev s) as [| x s']; [destruct (rev p)|]; reflexivity.
Qed.

Definition rebuild_childless_f {A : Type} (n : cnode A) : cchain A :=
  match n with
  | Node k p s =>
      if bis_empty p && bis_empty s then CEmpty
      else
        match k with
        | KOnly =>
            if bis_empty p || bis_empty s
            then CSingle (Pkt BHole n) CEmpty
            else if (bsize p <? 5) || (bsize s <? 5)
                 then CSingle (Pkt BHole (Node KOnly (bapp p s) bempty))
                        CEmpty
                 else CSingle (Pkt BHole n) CEmpty
        | _ => CSingle (Pkt BHole n) CEmpty
        end
  end.

Lemma rebuild_childless_f_eq : forall A (n : cnode A),
    rebuild_childless_f n = rebuild_childless n.
Proof.
  intros A [k p s]. destruct k; destruct p; destruct s; reflexivity.
Qed.

Fixpoint pop_raw_f {A : Type} (c : cchain A)
    : option (stored A * cchain A) :=
  match c with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_pop_f n with
      | Some (x, n') =>
          match child with
          | CEmpty => Some (x, rebuild_childless_f n')
          | _ => Some (x, tree_of_f n' child)
          end
      | None => None
      end
  | CPair l r =>
      match pop_raw_f l with
      | Some (x, l') =>
          match l' with
          | CEmpty => Some (x, r)
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty =>
              if bsize lp <? 5
              then
                match r with
                | CSingle pr rr =>
                    match root_and_child pr rr with
                    | (Node _ p2 s2, d2) =>
                        Some (x, tree_of_f
                                   (Node KOnly (bapp lp (bapp ls p2)) s2) d2)
                    end
                | _ => None
                end
              else Some (x, CPair l' r)
          | _ => Some (x, CPair l' r)
          end
      | None => None
      end
  end.

Lemma pop_raw_f_eq : forall A (c : cchain A), pop_raw_f c = pop_raw c.
Proof.
  intros A c.
  induction c as [| p rest _ | l IHl r _]; cbn [pop_raw_f pop_raw].
  - reflexivity.
  - destruct (root_and_child p rest) as [n child].
    rewrite node_pop_f_eq.
    destruct (node_pop n) as [[x n']|]; [|reflexivity].
    destruct child; [rewrite rebuild_childless_f_eq | rewrite tree_of_f_eq..];
      reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Fixpoint eject_raw_f {A : Type} (c : cchain A)
    : option (cchain A * stored A) :=
  match c with
  | CEmpty => None
  | CSingle p rest =>
      let '(n, child) := root_and_child p rest in
      match node_eject_f n with
      | Some (n', x) =>
          match child with
          | CEmpty => Some (rebuild_childless_f n', x)
          | _ => Some (tree_of_f n' child, x)
          end
      | None => None
      end
  | CPair l r =>
      match eject_raw_f r with
      | Some (r', x) =>
          match r' with
          | CEmpty => Some (l, x)
          | CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if bsize rs <? 5
              then
                match l with
                | CSingle pl rl =>
                    match root_and_child pl rl with
                    | (Node _ p1 s1, d1) =>
                        Some (tree_of_f
                                (Node KOnly p1 (bapp s1 (bapp rp rs))) d1, x)
                    end
                | _ => None
                end
              else Some (CPair l r', x)
          | _ => Some (CPair l r', x)
          end
      | None => None
      end
  end.

Lemma eject_raw_f_eq : forall A (c : cchain A), eject_raw_f c = eject_raw c.
Proof.
  intros A c.
  induction c as [| p rest _ | l _ r IHr]; cbn [eject_raw_f eject_raw].
  - reflexivity.
  - destruct (root_and_child p rest) as [n child].
    rewrite node_eject_f_eq.
    destruct (node_eject n) as [[n' x]|]; [|reflexivity].
    destruct child; [rewrite rebuild_childless_f_eq | rewrite tree_of_f_eq..];
      reflexivity.
  - rewrite IHr. reflexivity.
Qed.

Definition repair_front_f {A : Type} (k : kind) (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match pop_raw_f rest with
  | Some (SBig p2 d2 s2, d1') =>
      match cad_concat_f d2 (push_chain_f (SSmall s2) d1') with
      | Some d3 => Some (CSingle (Pkt body (Node k (bapp p1 p2) s1)) d3)
      | None => None
      end
  | Some (SSmall b, d1') =>
      Some (CSingle (Pkt body (Node k (bapp p1 b) s1)) d1')
  | _ => None
  end.

Lemma repair_front_f_eq : forall A k (body : cbody A) p1 s1 rest,
    repair_front_f k body p1 s1 rest = repair_front k body p1 s1 rest.
Proof.
  intros A k body p1 s1 rest.
  unfold repair_front_f, repair_front.
  rewrite pop_raw_f_eq.
  destruct (pop_raw rest) as [[x d1']|]; [|reflexivity].
  destruct x as [a | b | p2 d2 s2]; try reflexivity.
  rewrite push_chain_f_eq, cad_concat_f_eq.
  destruct (cad_concat d2 (push_chain (SSmall s2) d1')); reflexivity.
Qed.

Definition repair_back_f {A : Type} (k : kind) (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match eject_raw_f rest with
  | Some (d1', SBig p2 d2 s2) =>
      match cad_concat_f (inject_chain_f d1' (SSmall p2)) d2 with
      | Some d3 => Some (CSingle (Pkt body (Node k p1 (bapp s2 s1))) d3)
      | None => None
      end
  | Some (d1', SSmall b) =>
      Some (CSingle (Pkt body (Node k p1 (bapp b s1))) d1')
  | _ => None
  end.

Lemma repair_back_f_eq : forall A k (body : cbody A) p1 s1 rest,
    repair_back_f k body p1 s1 rest = repair_back k body p1 s1 rest.
Proof.
  intros A k body p1 s1 rest.
  unfold repair_back_f, repair_back.
  rewrite eject_raw_f_eq.
  destruct (eject_raw rest) as [[d1' x]|]; [|reflexivity].
  destruct x as [a | b | p2 d2 s2]; try reflexivity.
  rewrite inject_chain_f_eq, cad_concat_f_eq.
  destruct (cad_concat (inject_chain d1' (SSmall p2)) d2); reflexivity.
Qed.

Definition drain_both_f {A : Type} (rest : cchain A)
    : option (stored A * option (stored A) * cchain A) :=
  match rest with
  | CEmpty => None
  | CSingle p r =>
      let '(n, dd) := root_and_child p r in
      match node_pop_f n with
      | Some (cellF, n1) =>
          match node_eject_f n1 with
          | Some (n2, cellB) =>
              match dd with
              | CEmpty => Some (cellF, Some cellB, rebuild_childless_f n2)
              | _ => Some (cellF, Some cellB, tree_of_f n2 dd)
              end
          | None =>
              match dd with
              | CEmpty => Some (cellF, None, CEmpty)
              | _ => None
              end
          end
      | None => None
      end
  | CPair l r =>
      match pop_raw_f l, eject_raw_f r with
      | Some (cellF, l'), Some (r', cellB) =>
          match l', r' with
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty,
            CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if (bsize lp <? 5) || (bsize rs <? 5)
              then Some (cellF, Some cellB,
                     CSingle (Pkt BHole
                       (Node KOnly (bapp lp ls) (bapp rp rs))) CEmpty)
              else Some (cellF, Some cellB, CPair l' r')
          | CSingle (Pkt BHole (Node _ lp ls)) CEmpty, CSingle pr' rr' =>
              if bsize lp <? 5
              then
                match root_and_child pr' rr' with
                | (Node _ p2 s2, d2) =>
                    Some (cellF, Some cellB,
                      tree_of_f (Node KOnly (bapp lp (bapp ls p2)) s2) d2)
                end
              else Some (cellF, Some cellB, CPair l' r')
          | CSingle pl' rl', CSingle (Pkt BHole (Node _ rp rs)) CEmpty =>
              if bsize rs <? 5
              then
                match root_and_child pl' rl' with
                | (Node _ p2 s2, d2) =>
                    Some (cellF, Some cellB,
                      tree_of_f (Node KOnly p2 (bapp s2 (bapp rp rs))) d2)
                end
              else Some (cellF, Some cellB, CPair l' r')
          | _, _ => Some (cellF, Some cellB, CPair l' r')
          end
      | _, _ => None
      end
  end.

Lemma drain_both_f_eq : forall A (rest : cchain A),
    drain_both_f rest = drain_both rest.
Proof.
  intros A rest.
  unfold drain_both_f, drain_both.
  destruct rest as [| p r | l r]; [reflexivity| |].
  - destruct (root_and_child p r) as [n dd].
    rewrite node_pop_f_eq.
    destruct (node_pop n) as [[cellF n1]|]; [|reflexivity].
    rewrite node_eject_f_eq.
    destruct (node_eject n1) as [[n2 cellB]|].
    + destruct dd; try reflexivity.
      rewrite rebuild_childless_f_eq. reflexivity.
    + destruct dd; reflexivity.
  - rewrite pop_raw_f_eq, eject_raw_f_eq. reflexivity.
Qed.

Definition repair_both_f {A : Type} (body : cbody A)
    (p1 s1 : buffer (stored A)) (rest : cchain A) : option (cchain A) :=
  match drain_both_f rest with
  | Some (cellF, None, _) =>
      match cellF with
      | SBig p2 d2 s2 =>
          Some (CSingle (Pkt body (Node KOnly (bapp p1 p2) (bapp s2 s1))) d2)
      | SSmall b =>
          Some (CSingle (Pkt body (Node KOnly (bapp p1 b) s1)) CEmpty)
      | SGround _ => None
      end
  | Some (cellF, Some cellB, mid) =>
      let front :=
        match cellF with
        | SBig p2 d2 s2 =>
            match cad_concat_f d2 (push_chain_f (SSmall s2) mid) with
            | Some d4 => Some (p2, d4)
            | None => None
            end
        | SSmall b => Some (b, mid)
        | SGround _ => None
        end
      in
      match front with
      | Some (pf, d4) =>
          match cellB with
          | SBig p3 d3 s3 =>
              match cad_concat_f (inject_chain_f d4 (SSmall p3)) d3 with
              | Some d5 =>
                  Some (CSingle
                    (Pkt body (Node KOnly (bapp p1 pf) (bapp s3 s1))) d5)
              | None => None
              end
          | SSmall b =>
              Some (CSingle
                (Pkt body (Node KOnly (bapp p1 pf) (bapp b s1))) d4)
          | SGround _ => None
          end
      | None => None
      end
  | None => None
  end.

Lemma repair_both_f_eq : forall A (body : cbody A) p1 s1 rest,
    repair_both_f body p1 s1 rest = repair_both body p1 s1 rest.
Proof.
  intros A body p1 s1 rest.
  unfold repair_both_f, repair_both.
  rewrite drain_both_f_eq.
  destruct (drain_both rest) as [[[cellF [cellB|]] mid]|]; [|reflexivity..].
  destruct cellF as [a | b | p2 d2 s2]; try reflexivity.
  - (* SSmall front *)
    destruct cellB as [a3 | b3 | p3 d3 s3]; try reflexivity.
    rewrite inject_chain_f_eq, cad_concat_f_eq.
    destruct (cad_concat (inject_chain mid (SSmall p3)) d3); reflexivity.
  - (* SBig front *)
    rewrite push_chain_f_eq, cad_concat_f_eq.
    destruct (cad_concat d2 (push_chain (SSmall s2) mid)) as [d4|];
      [|reflexivity].
    destruct cellB as [a3 | b3 | p3 d3 s3]; try reflexivity.
    rewrite inject_chain_f_eq, cad_concat_f_eq.
    destruct (cad_concat (inject_chain d4 (SSmall p3)) d3); reflexivity.
Qed.

Definition repair_packet_f {A : Type}
    (p : cpacket A) (rest : cchain A) : option (cchain A) :=
  match p with
  | Pkt body n =>
      match node_color_f (chain_has_node rest) n with
      | CR =>
          match n with
          | Node KLeft p1 s1 => repair_front_f KLeft body p1 s1 rest
          | Node KRight p1 s1 => repair_back_f KRight body p1 s1 rest
          | Node KOnly p1 s1 =>
              if 8 <=? bsize s1 then repair_front_f KOnly body p1 s1 rest
              else if 8 <=? bsize p1 then repair_back_f KOnly body p1 s1 rest
              else repair_both_f body p1 s1 rest
          end
      | _ => Some (CSingle p rest)
      end
  end.

Lemma repair_packet_f_eq : forall A (p : cpacket A) rest,
    repair_packet_f p rest = repair_packet p rest.
Proof.
  intros A [body n] rest.
  unfold repair_packet_f, repair_packet.
  rewrite node_color_f_eq.
  destruct (node_color (chain_has_node rest) n); try reflexivity.
  destruct n as [k p1 s1]; destruct k.
  - change (bsize s1) with (length s1).
    change (bsize p1) with (length p1).
    destruct (8 <=? length s1); [apply repair_front_f_eq|].
    destruct (8 <=? length p1); [apply repair_back_f_eq|].
    apply repair_both_f_eq.
  - apply repair_front_f_eq.
  - apply repair_back_f_eq.
Qed.

Definition repair_pop_side_f {A : Type} (c : cchain A) : option (cchain A) :=
  match c with
  | CEmpty => Some CEmpty
  | CSingle p rest => repair_packet_f p rest
  | CPair (CSingle pl rl) r =>
      match repair_packet_f pl rl with
      | Some l' => Some (CPair l' r)
      | None => None
      end
  | CPair _ _ => None
  end.

Lemma repair_pop_side_f_eq : forall A (c : cchain A),
    repair_pop_side_f c = repair_pop_side c.
Proof.
  intros A c.
  unfold repair_pop_side_f, repair_pop_side.
  destruct c as [| p rest | l r]; try apply repair_packet_f_eq; [reflexivity|].
  destruct l as [| pl rl |]; try reflexivity.
  rewrite repair_packet_f_eq.
  destruct (repair_packet pl rl); reflexivity.
Qed.

Definition repair_eject_side_f {A : Type} (c : cchain A) : option (cchain A) :=
  match c with
  | CEmpty => Some CEmpty
  | CSingle p rest => repair_packet_f p rest
  | CPair l (CSingle pr rr) =>
      match repair_packet_f pr rr with
      | Some r' => Some (CPair l r')
      | None => None
      end
  | CPair _ _ => None
  end.

Lemma repair_eject_side_f_eq : forall A (c : cchain A),
    repair_eject_side_f c = repair_eject_side c.
Proof.
  intros A c.
  unfold repair_eject_side_f, repair_eject_side.
  destruct c as [| p rest | l r]; try apply repair_packet_f_eq; [reflexivity|].
  destruct r as [| pr rr |]; try reflexivity.
  rewrite repair_packet_f_eq.
  destruct (repair_packet pr rr); reflexivity.
Qed.

Definition cad_pop_f {A : Type} (d : cadeque A) : option (A * cadeque A) :=
  match pop_raw_f d with
  | Some (SGround x, d') =>
      match repair_pop_side_f d' with
      | Some d'' => Some (x, d'')
      | None => None
      end
  | _ => None
  end.

Lemma cad_pop_f_eq : forall A (d : cadeque A), cad_pop_f d = cad_pop d.
Proof.
  intros A d.
  unfold cad_pop_f, cad_pop.
  rewrite pop_raw_f_eq.
  destruct (pop_raw d) as [[x d']|]; [|reflexivity].
  destruct x; try reflexivity.
  rewrite repair_pop_side_f_eq.
  destruct (repair_pop_side d'); reflexivity.
Qed.

Definition cad_eject_f {A : Type} (d : cadeque A) : option (cadeque A * A) :=
  match eject_raw_f d with
  | Some (d', SGround x) =>
      match repair_eject_side_f d' with
      | Some d'' => Some (d'', x)
      | None => None
      end
  | _ => None
  end.

Lemma cad_eject_f_eq : forall A (d : cadeque A), cad_eject_f d = cad_eject d.
Proof.
  intros A d.
  unfold cad_eject_f, cad_eject.
  rewrite eject_raw_f_eq.
  destruct (eject_raw d) as [[d' x]|]; [|reflexivity].
  destruct x; try reflexivity.
  rewrite repair_eject_side_f_eq.
  destruct (repair_eject_side d'); reflexivity.
Qed.
