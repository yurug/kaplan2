(** * KTDeque.Catenable.FlatOps — the §6 ops on the fused spine.

    Mirrors of the production operation family (OpsFast.v / OpsFused.v)
    over the fused representation of FlatChain.v.  Each mirror [op_x]
    comes with a commutation lemma

        fc_er (op_x args) = op_f/op_v2 (erased args)

    — the machine-checked diff of the representation change.  The
    lemmas compose with the [_f_eq]/[_v2_eq] chains of OpsFast/OpsFused,
    so the keystone transfers to the fused family (FlatKeystone.v).

    Construction discipline: every site that built
    [CSingle (Pkt b n) rest] goes through the smart constructor
    [fsingle], so hole-bodied packets stay in the one-block [FFlat]
    form on every path; matching sites split the [FFlat]/[FSingle]
    arms (both erase to [CSingle (Pkt _ _) _]). *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast
  OpsFused FlatChain.

Set Implicit Arguments.

(* ========================================================================== *)
(* Colour, rebundling, push / inject.                                          *)
(* ========================================================================== *)

Definition node_color_x {A : Type} (has_child : bool) (n : fnode A) : gyor :=
  if negb has_child then CG
  else
    match n with
    | FNode k p s =>
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

Lemma node_color_x_er : forall A hc (n : fnode A),
    node_color_f hc (fn_er n) = node_color_x hc n.
Proof.
  intros A hc [k p s].
  unfold node_color_f, node_color_x.
  rewrite fn_er_node.
  destruct hc; [|reflexivity].
  rewrite !map_bsize. reflexivity.
Qed.

Definition tree_of_x {A : Type} (n : fnode A) (child : fchain A) : fchain A :=
  match node_color_x (fchain_has_node child) n with
  | CG | CR => fsingle FHole n child
  | CY =>
      match child with
      | FFlat k2 p2 s2 rrest =>
          FSingle (FBSingle n FHole) (FNode k2 p2 s2) rrest
      | FSingle rb rn rrest => FSingle (FBSingle n rb) rn rrest
      | FPair (FFlat k2 p2 s2 lrest) r =>
          FSingle (FBPairY n FHole r) (FNode k2 p2 s2) lrest
      | FPair (FSingle lb ln lrest) r => FSingle (FBPairY n lb r) ln lrest
      | _ => fsingle FHole n child
      end
  | CO =>
      match child with
      | FFlat k2 p2 s2 rrest =>
          FSingle (FBSingle n FHole) (FNode k2 p2 s2) rrest
      | FSingle rb rn rrest => FSingle (FBSingle n rb) rn rrest
      | FPair l (FFlat k2 p2 s2 rrest) =>
          FSingle (FBPairO n l FHole) (FNode k2 p2 s2) rrest
      | FPair l (FSingle rb rn rrest) => FSingle (FBPairO n l rb) rn rrest
      | _ => fsingle FHole n child
      end
  end.

Lemma tree_of_x_er : forall A (n : fnode A) child,
    fc_er (tree_of_x n child) = tree_of_f (fn_er n) (fc_er child).
Proof.
  intros A n child.
  unfold tree_of_x, tree_of_f.
  rewrite fchain_has_node_er, node_color_x_er.
  destruct (node_color_x (fchain_has_node child) n);
    try (rewrite fc_er_fsingle; reflexivity).
  - (* CY *)
    destruct child as [| k2 p2 s2 rrest | rb rn rrest | l r];
      try (rewrite ?fc_er_fsingle; reflexivity).
    destruct l as [| k2 p2 s2 lrest | lb ln lrest |];
      rewrite ?fc_er_fsingle; reflexivity.
  - (* CO *)
    destruct child as [| k2 p2 s2 rrest | rb rn rrest | l r];
      try (rewrite ?fc_er_fsingle; reflexivity).
    destruct r as [| k2 p2 s2 rrest | rb rn rrest |];
      rewrite ?fc_er_fsingle; reflexivity.
Qed.

(** Decompose a (destructured) packet cell into (root node, child). *)
Definition root_and_child_x {A : Type}
    (b : fbody A) (n : fnode A) (rest : fchain A) : fnode A * fchain A :=
  match b with
  | FHole => (n, rest)
  | FBSingle hn b' => (hn, fsingle b' n rest)
  | FBPairY hn b' rc => (hn, FPair (fsingle b' n rest) rc)
  | FBPairO hn lc b' => (hn, FPair lc (fsingle b' n rest))
  end.

Lemma root_and_child_x_er : forall A (b : fbody A) n rest,
    root_and_child (Pkt (fb_er b) (fn_er n)) (fc_er rest)
    = (fn_er (fst (root_and_child_x b n rest)),
       fc_er (snd (root_and_child_x b n rest))).
Proof.
  intros A b n rest.
  destruct b; cbn [root_and_child_x fb_er fc_er root_and_child fst snd];
    rewrite ?fc_er_fsingle; reflexivity.
Qed.

Definition node_push_x {A : Type} (s : fstored A) (n : fnode A) : fnode A :=
  match n with
  | FNode k p suf =>
      if bis_empty p
      then FNode k p (bpush s suf)
      else FNode k (bpush s p) suf
  end.

Lemma node_push_x_er : forall A (s : fstored A) n,
    fn_er (node_push_x s n) = node_push_f (fs_er s) (fn_er n).
Proof.
  intros A s [k p suf].
  unfold node_push_x, node_push_f.
  rewrite !fn_er_node, map_bis_empty.
  destruct (bis_empty p); rewrite fn_er_node, map_bpush; reflexivity.
Qed.

Definition node_inject_x {A : Type} (n : fnode A) (s : fstored A) : fnode A :=
  match n with
  | FNode k p suf =>
      if bis_empty suf
      then FNode k (binject p s) suf
      else FNode k p (binject suf s)
  end.

Lemma node_inject_x_er : forall A (n : fnode A) s,
    fn_er (node_inject_x n s) = node_inject_f (fn_er n) (fs_er s).
Proof.
  intros A [k p suf] s.
  unfold node_inject_x, node_inject_f.
  rewrite !fn_er_node, map_bis_empty.
  destruct (bis_empty suf); rewrite fn_er_node, map_binject; reflexivity.
Qed.

(** The fused packet update (mirror of OpsFused.upd_pkt), split over
    the two packet-cell constructors. *)
Definition upd_flat_x {A : Type} (upd : fnode A -> fnode A)
    (k : kind) (p s : buffer (fstored A)) (rest : fchain A) : fchain A :=
  tree_of_x (upd (FNode k p s)) rest.

Definition upd_single_x {A : Type} (upd : fnode A -> fnode A)
    (b : fbody A) (n : fnode A) (rest : fchain A) : fchain A :=
  match b with
  | FHole => tree_of_x (upd n) rest
  | FBSingle hn b' =>
      let hn' := upd hn in
      match node_color_x true hn' with
      | CG | CR => fsingle FHole hn' (fsingle b' n rest)
      | CY | CO => FSingle (FBSingle hn' b') n rest
      end
  | FBPairY hn b' rc =>
      let hn' := upd hn in
      match node_color_x true hn' with
      | CG | CR => fsingle FHole hn' (FPair (fsingle b' n rest) rc)
      | CY => FSingle (FBPairY hn' b' rc) n rest
      | CO =>
          match rc with
          | FFlat k2 p2 s2 rrest =>
              FSingle (FBPairO hn' (fsingle b' n rest) FHole)
                (FNode k2 p2 s2) rrest
          | FSingle rb rn rrest =>
              FSingle (FBPairO hn' (fsingle b' n rest) rb) rn rrest
          | _ => fsingle FHole hn' (FPair (fsingle b' n rest) rc)
          end
      end
  | FBPairO hn lc b' =>
      let hn' := upd hn in
      match node_color_x true hn' with
      | CG | CR => fsingle FHole hn' (FPair lc (fsingle b' n rest))
      | CO => FSingle (FBPairO hn' lc b') n rest
      | CY =>
          match lc with
          | FFlat k2 p2 s2 lrest =>
              FSingle (FBPairY hn' FHole (fsingle b' n rest))
                (FNode k2 p2 s2) lrest
          | FSingle lb ln lrest =>
              FSingle (FBPairY hn' lb (fsingle b' n rest)) ln lrest
          | _ => fsingle FHole hn' (FPair lc (fsingle b' n rest))
          end
      end
  end.

Lemma upd_flat_x_er : forall A (updx : fnode A -> fnode A) upd k p s rest,
    (forall m, fn_er (updx m) = upd (fn_er m)) ->
    fc_er (upd_flat_x updx k p s rest)
    = upd_pkt upd (Pkt BHole (Node k (map fs_er p) (map fs_er s)))
        (fc_er rest).
Proof.
  intros A updx upd k p s rest Hu.
  unfold upd_flat_x; cbn [upd_pkt].
  rewrite tree_of_x_er, Hu, fn_er_node, tree_of_f_eq. reflexivity.
Qed.

Lemma upd_single_x_er : forall A (updx : fnode A -> fnode A) upd b n rest,
    (forall m, fn_er (updx m) = upd (fn_er m)) ->
    fc_er (upd_single_x updx b n rest)
    = upd_pkt upd (Pkt (fb_er b) (fn_er n)) (fc_er rest).
Proof.
  intros A updx upd b n rest Hu.
  destruct b as [| hn b' | hn b' rc | hn lc b'];
    cbn [upd_single_x fb_er upd_pkt].
  - rewrite tree_of_x_er, Hu, tree_of_f_eq. reflexivity.
  - rewrite <- Hu, node_color_x_er.
    destruct (node_color_x true (updx hn));
      do 3 (rewrite ?fc_er_fsingle; cbn [fc_er fb_er]); reflexivity.
  - rewrite <- Hu, node_color_x_er.
    destruct (node_color_x true (updx hn));
      try (do 3 (rewrite ?fc_er_fsingle; cbn [fc_er fb_er]); reflexivity).
    destruct rc as [| k2 p2 s2 rrest | rb rn rrest |];
      do 3 (rewrite ?fc_er_fsingle; cbn [fc_er fb_er]); reflexivity.
  - rewrite <- Hu, node_color_x_er.
    destruct (node_color_x true (updx hn));
      try (do 3 (rewrite ?fc_er_fsingle; cbn [fc_er fb_er]); reflexivity).
    destruct lc as [| k2 p2 s2 lrest | lb ln lrest |];
      do 3 (rewrite ?fc_er_fsingle; cbn [fc_er fb_er]); reflexivity.
Qed.

Fixpoint push_chain_x {A : Type} (s : fstored A) (c : fchain A) : fchain A :=
  match c with
  | FEmpty => FFlat KOnly (b1 s) bempty FEmpty
  | FFlat k p sf rest => upd_flat_x (node_push_x s) k p sf rest
  | FSingle b n rest => upd_single_x (node_push_x s) b n rest
  | FPair l r => FPair (push_chain_x s l) r
  end.

Lemma push_chain_x_er : forall A (s : fstored A) c,
    fc_er (push_chain_x s c) = push_chain_v2 (fs_er s) (fc_er c).
Proof.
  intros A s c. revert s.
  induction c as [| k p sf rest _ | b n rest _ | l IHl r _]; intros s.
  - reflexivity.
  - cbn [push_chain_x].
    rewrite (upd_flat_x_er _ _ _ _ (fun m => node_push_x_er s m)).
    reflexivity.
  - cbn [push_chain_x].
    rewrite (upd_single_x_er _ _ _ (fun m => node_push_x_er s m)).
    reflexivity.
  - cbn [push_chain_x fc_er]. rewrite IHl. reflexivity.
Qed.

Fixpoint inject_chain_x {A : Type} (c : fchain A) (s : fstored A) : fchain A :=
  match c with
  | FEmpty => FFlat KOnly bempty (b1 s) FEmpty
  | FFlat k p sf rest => upd_flat_x (fun n => node_inject_x n s) k p sf rest
  | FSingle b n rest => upd_single_x (fun n => node_inject_x n s) b n rest
  | FPair l r => FPair l (inject_chain_x r s)
  end.

Lemma inject_chain_x_er : forall A (c : fchain A) (s : fstored A),
    fc_er (inject_chain_x c s) = inject_chain_v2 (fc_er c) (fs_er s).
Proof.
  intros A c. induction c as [| k p sf rest _ | b n rest _ | l _ r IHr];
    intros s.
  - reflexivity.
  - cbn [inject_chain_x].
    rewrite (upd_flat_x_er (upd := fun nn => node_inject_f nn (fs_er s)) _ _ _ _ (fun m => node_inject_x_er m s)).
    reflexivity.
  - cbn [inject_chain_x].
    rewrite (upd_single_x_er (upd := fun nn => node_inject_f nn (fs_er s)) _ _ _ (fun m => node_inject_x_er m s)).
    reflexivity.
  - cbn [inject_chain_x fc_er]. rewrite IHr. reflexivity.
Qed.

Definition cad_push_x {A : Type} (x : A) (d : fchain A) : fchain A :=
  push_chain_x (FGround x) d.

Lemma cad_push_x_er : forall A (x : A) d,
    fc_er (cad_push_x x d) = cad_push_v2 x (fc_er d).
Proof. intros. apply (push_chain_x_er (FGround x) d). Qed.

Definition cad_inject_x {A : Type} (d : fchain A) (x : A) : fchain A :=
  inject_chain_x d (FGround x).

Lemma cad_inject_x_er : forall A (d : fchain A) (x : A),
    fc_er (cad_inject_x d x) = cad_inject_v2 (fc_er d) x.
Proof. intros. apply (inject_chain_x_er d (FGround x)). Qed.
