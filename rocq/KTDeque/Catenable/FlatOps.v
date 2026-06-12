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

(* ========================================================================== *)
(* Concat.                                                                     *)
(* ========================================================================== *)

(** Decompose a packet cell (either fused form). *)
Definition fcell {A : Type} (c : fchain A)
  : option (fbody A * fnode A * fchain A) :=
  match c with
  | FFlat k p s rest => Some (FHole, FNode k p s, rest)
  | FSingle b n rest => Some (b, n, rest)
  | _ => None
  end.

Lemma fcell_er : forall A (c : fchain A) b n rest,
    fcell c = Some (b, n, rest) ->
    fc_er c = CSingle (Pkt (fb_er b) (fn_er n)) (fc_er rest).
Proof.
  intros A c b n rest H.
  destruct c; cbn [fcell] in H; inversion H; subst; reflexivity.
Qed.

Lemma fcell_none_er : forall A (c : fchain A),
    fcell c = None ->
    fc_er c = CEmpty \/ exists l r, fc_er c = CPair l r.
Proof.
  intros A c H.
  destruct c; cbn [fcell] in H; try discriminate.
  - left; reflexivity.
  - right. eexists _, _. reflexivity.
Qed.

Definition degenerate_buf_x {A : Type} (d : fchain A)
  : option (buffer (fstored A)) :=
  match d with
  | FFlat KOnly p s FEmpty =>
      if bis_empty p then Some s
      else if bis_empty s then Some p
      else None
  | FSingle FHole (FNode KOnly p s) FEmpty =>
      if bis_empty p then Some s
      else if bis_empty s then Some p
      else None
  | _ => None
  end.

Lemma degenerate_buf_x_er : forall A (d : fchain A),
    degenerate_buf_f (fc_er d)
    = option_map (map fs_er) (degenerate_buf_x d).
Proof.
  intros A d.
  destruct d as [| k p s rest | b n rest | l r]; try reflexivity.
  - cbn [degenerate_buf_x]. rewrite fc_er_flat.
    destruct k; try reflexivity.
    destruct rest as [| ? ? ? ? | ? ? ? |]; try reflexivity.
    cbn [degenerate_buf_f fc_er].
    rewrite !map_bis_empty.
    destruct (bis_empty p); [reflexivity|].
    destruct (bis_empty s); reflexivity.
  - cbn [degenerate_buf_x fc_er].
    destruct b; try (destruct n as [k p s]; destruct k; reflexivity).
    destruct n as [k p s]. rewrite fn_er_node. cbn [fb_er].
    destruct k; try reflexivity.
    destruct rest as [| ? ? ? ? | ? ? ? |]; try reflexivity.
    cbn [degenerate_buf_f fc_er].
    rewrite !map_bis_empty.
    destruct (bis_empty p); [reflexivity|].
    destruct (bis_empty s); reflexivity.
Qed.

Local Ltac er_done :=
  do 3 (rewrite ?fc_er_fsingle, ?tree_of_x_er,
          ?push_chain_x_er, ?inject_chain_x_er,
          ?push_chain_v2_eq, ?inject_chain_v2_eq,
          ?fs_er_big, ?fs_er_small, ?fn_er_node,
          ?map_bapp, ?map_b1, ?map_b2, ?map_b3,
          ?map_bpush, ?map_binject;
        cbn [fc_er fb_er option_map]);
  reflexivity.

Definition make_left_only_x {A : Type}
    (p1 : buffer (fstored A)) (d1 : fchain A) (s1 : buffer (fstored A))
  : option (fchain A) :=
  match d1 with
  | FEmpty =>
      if bsize s1 <=? 8 then
        match beject2 s1 with
        | Some (s1', y, z) =>
            Some (tree_of_x (FNode KLeft (bapp p1 s1') (b2 y z)) FEmpty)
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
                        Some (tree_of_x (FNode KLeft (bapp p1 (b3 a b c))
                                           (b2 y z))
                                (push_chain_x (FSmall smid) FEmpty))
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
          Some (tree_of_x (FNode KLeft p1 (b2 y z))
                  (inject_chain_x d1 (FSmall s1')))
      | None => None
      end
  end.

Lemma make_left_only_x_er : forall A (p1 : buffer (fstored A)) d1 s1,
    make_left_only_f (map fs_er p1) (fc_er d1) (map fs_er s1)
    = option_map fc_er (make_left_only_x p1 d1 s1).
Proof.
  intros A p1 d1 s1.
  unfold make_left_only_f, make_left_only_x.
  destruct d1 as [| k p s rest | b n rest | l r];
    [ (* FEmpty *)
      cbn [fc_er];
      rewrite map_bsize;
      destruct (bsize s1 <=? 8);
      [ rewrite map_beject2;
        destruct (beject2 s1) as [[[s1' y] z]|]; cbn [option_map];
        [er_done | reflexivity]
      | rewrite map_bpop;
        destruct (bpop s1) as [[a t1]|]; cbn [option_map]; [|reflexivity];
        rewrite map_bpop;
        destruct (bpop t1) as [[b t2]|]; cbn [option_map]; [|reflexivity];
        rewrite map_bpop;
        destruct (bpop t2) as [[c srest]|]; cbn [option_map]; [|reflexivity];
        rewrite map_beject2;
        destruct (beject2 srest) as [[[smid y] z]|]; cbn [option_map];
        [er_done | reflexivity] ]
    | (* non-empty arms *)
      rewrite ?fc_er_flat; cbn [fc_er];
      rewrite map_beject2;
      destruct (beject2 s1) as [[[s1' y] z]|]; cbn [option_map];
      [er_done | reflexivity] .. ].
Qed.

Definition make_left_x {A : Type} (d : fchain A) : option (fchain A) :=
  match d with
  | FEmpty => None
  | FPair l r =>
      match fcell l, fcell r with
      | Some (bl, nl, rl), Some (br, nr, rr) =>
          match root_and_child_x bl nl rl, root_and_child_x br nr rr with
          | (FNode _ p1 s1, d1), (FNode _ p2 s2, d2) =>
              match d1 with
              | FEmpty => make_left_only_x (bapp p1 (bapp s1 p2)) d2 s2
              | _ =>
                  match beject2 s2 with
                  | Some (s2', y, z) =>
                      Some (tree_of_x (FNode KLeft p1 (b2 y z))
                              (inject_chain_x d1
                                 (FBig (bapp s1 p2) d2 s2')))
                  | None => None
                  end
              end
          end
      | _, _ => None
      end
  | _ =>
      match fcell d with
      | Some (b, n, rest) =>
          match root_and_child_x b n rest with
          | (FNode _ p1 s1, d1) => make_left_only_x p1 d1 s1
          end
      | None => None
      end
  end.

(** Erased root decomposition of a packet cell, in the componentwise
    form the concat proofs consume. *)
Lemma root_and_child_cell : forall A (c : fchain A) b n rest,
    fcell c = Some (b, n, rest) ->
    root_and_child (Pkt (fb_er b) (fn_er n)) (fc_er rest)
    = (fn_er (fst (root_and_child_x b n rest)),
       fc_er (snd (root_and_child_x b n rest))).
Proof. intros. apply root_and_child_x_er. Qed.

Lemma make_left_x_er : forall A (d : fchain A),
    make_left_f (fc_er d) = option_map fc_er (make_left_x d).
Proof.
  intros A d.
  destruct d as [| k p s rest | b n rest | l r]; [reflexivity| | |].
  - (* FFlat: single cell *)
    cbn [make_left_x fcell].
    rewrite fc_er_flat.
    cbn [make_left_f root_and_child root_and_child_x].
    apply make_left_only_x_er.
  - (* FSingle: single cell *)
    cbn [make_left_x fcell fc_er make_left_f].
    rewrite (root_and_child_x_er b n rest).
    destruct (root_and_child_x b n rest) as [[k1 p1 s1] d1].
    cbn [fst snd]. rewrite fn_er_node.
    apply make_left_only_x_er.
  - (* FPair *)
    cbn [make_left_x fc_er make_left_f].
    destruct (fcell l) as [[[bl nl] rl]|] eqn:Hl;
      destruct (fcell r) as [[[br nr] rr]|] eqn:Hr.
    + rewrite (fcell_er Hl), (fcell_er Hr).
      rewrite (root_and_child_x_er bl nl rl),
              (root_and_child_x_er br nr rr).
      destruct (root_and_child_x bl nl rl) as [[k1 p1 s1] d1].
      destruct (root_and_child_x br nr rr) as [[k2 p2 s2] d2].
      cbn [fst snd]. rewrite !fn_er_node.
      destruct d1 as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite <- !map_bapp; apply make_left_only_x_er
        | (rewrite ?fc_er_flat; cbn [fc_er];
           rewrite map_beject2;
           destruct (beject2 s2) as [[[s2' y] z]|]; cbn [option_map];
           [er_done | reflexivity]) .. ].
    + rewrite ?(fcell_er Hl);
        destruct (fcell_none_er Hr) as [Hr' | (l2 & r2 & Hr')];
        rewrite ?Hr'; reflexivity.
    + rewrite ?(fcell_er Hr);
        destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
        rewrite ?Hl'; reflexivity.
    + destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
        destruct (fcell_none_er Hr) as [Hr' | (l3 & r3 & Hr')];
        rewrite ?Hl', ?Hr'; reflexivity.
Qed.

Definition make_right_only_x {A : Type}
    (p1 : buffer (fstored A)) (d1 : fchain A) (s1 : buffer (fstored A))
  : option (fchain A) :=
  match d1 with
  | FEmpty =>
      if bsize p1 <=? 8 then
        match bpop2 p1 with
        | Some (x, y, p1') =>
            Some (tree_of_x (FNode KRight (b2 x y) (bapp p1' s1)) FEmpty)
        | None => None
        end
      else
        match bpop2 p1 with
        | Some (x, y, p1') =>
            match beject3 p1' with
            | Some (pmid, a, b, c) =>
                Some (tree_of_x (FNode KRight (b2 x y) (bapp (b3 a b c) s1))
                        (push_chain_x (FSmall pmid) FEmpty))
            | None => None
            end
        | None => None
        end
  | _ =>
      match bpop2 p1 with
      | Some (x, y, p1') =>
          Some (tree_of_x (FNode KRight (b2 x y) s1)
                  (push_chain_x (FSmall p1') d1))
      | None => None
      end
  end.

Lemma make_right_only_x_er : forall A (p1 : buffer (fstored A)) d1 s1,
    make_right_only_f (map fs_er p1) (fc_er d1) (map fs_er s1)
    = option_map fc_er (make_right_only_x p1 d1 s1).
Proof.
  intros A p1 d1 s1.
  unfold make_right_only_f, make_right_only_x.
  destruct d1 as [| k p s rest | b n rest | l r];
    [ cbn [fc_er];
      rewrite map_bsize;
      destruct (bsize p1 <=? 8);
      [ rewrite map_bpop2;
        destruct (bpop2 p1) as [[[x y] p1']|]; cbn [option_map];
        [er_done | reflexivity]
      | rewrite map_bpop2;
        destruct (bpop2 p1) as [[[x y] p1']|]; cbn [option_map];
        [|reflexivity];
        rewrite map_beject3;
        destruct (beject3 p1') as [[[[pmid a] b] c]|]; cbn [option_map];
        [er_done | reflexivity] ]
    | rewrite ?fc_er_flat; cbn [fc_er];
      rewrite map_bpop2;
      destruct (bpop2 p1) as [[[x y] p1']|]; cbn [option_map];
      [er_done | reflexivity] .. ].
Qed.

Definition make_right_x {A : Type} (e : fchain A) : option (fchain A) :=
  match e with
  | FEmpty => None
  | FPair l r =>
      match fcell l, fcell r with
      | Some (bl, nl, rl), Some (br, nr, rr) =>
          match root_and_child_x bl nl rl, root_and_child_x br nr rr with
          | (FNode _ p1 s1, d1), (FNode _ p2 s2, d2) =>
              match d2 with
              | FEmpty => make_right_only_x p1 d1 (bapp s1 (bapp p2 s2))
              | _ =>
                  match bpop2 p1 with
                  | Some (x, y, p1') =>
                      Some (tree_of_x (FNode KRight (b2 x y) s2)
                              (push_chain_x
                                 (FBig p1' d1 (bapp s1 p2)) d2))
                  | None => None
                  end
              end
          end
      | _, _ => None
      end
  | _ =>
      match fcell e with
      | Some (b, n, rest) =>
          match root_and_child_x b n rest with
          | (FNode _ p1 s1, d1) => make_right_only_x p1 d1 s1
          end
      | None => None
      end
  end.

Lemma make_right_x_er : forall A (e : fchain A),
    make_right_f (fc_er e) = option_map fc_er (make_right_x e).
Proof.
  intros A e.
  destruct e as [| k p s rest | b n rest | l r]; [reflexivity| | |].
  - cbn [make_right_x fcell].
    rewrite fc_er_flat.
    cbn [make_right_f root_and_child root_and_child_x].
    apply make_right_only_x_er.
  - cbn [make_right_x fcell fc_er make_right_f].
    rewrite (root_and_child_x_er b n rest).
    destruct (root_and_child_x b n rest) as [[k1 p1 s1] d1].
    cbn [fst snd]. rewrite fn_er_node.
    apply make_right_only_x_er.
  - cbn [make_right_x fc_er make_right_f].
    destruct (fcell l) as [[[bl nl] rl]|] eqn:Hl;
      destruct (fcell r) as [[[br nr] rr]|] eqn:Hr.
    + rewrite (fcell_er Hl), (fcell_er Hr).
      rewrite (root_and_child_x_er bl nl rl),
              (root_and_child_x_er br nr rr).
      destruct (root_and_child_x bl nl rl) as [[k1 p1 s1] d1].
      destruct (root_and_child_x br nr rr) as [[k2 p2 s2] d2].
      cbn [fst snd]. rewrite !fn_er_node.
      destruct d2 as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite <- !map_bapp; apply make_right_only_x_er
        | (rewrite ?fc_er_flat; cbn [fc_er];
           rewrite map_bpop2;
           destruct (bpop2 p1) as [[[x y] p1']|]; cbn [option_map];
           [er_done | reflexivity]) .. ].
    + rewrite ?(fcell_er Hl);
        destruct (fcell_none_er Hr) as [Hr' | (l2 & r2 & Hr')];
        rewrite ?Hr'; reflexivity.
    + rewrite ?(fcell_er Hr);
        destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
        rewrite ?Hl'; reflexivity.
    + destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
        destruct (fcell_none_er Hr) as [Hr' | (l3 & r3 & Hr')];
        rewrite ?Hl', ?Hr'; reflexivity.
Qed.

Lemma bfold_right_push_x_er : forall A (e : fchain A) (b : buffer (fstored A)),
    fc_er (bfold_right push_chain_x e b)
    = bfold_right push_chain_f (fc_er e) (map fs_er b).
Proof.
  intros A e b. unfold bfold_right.
  induction b as [| x b IH]; cbn [fold_right map]; [reflexivity|].
  rewrite push_chain_x_er, push_chain_v2_eq, push_chain_f_eq, IH.
  rewrite <- push_chain_f_eq. reflexivity.
Qed.

Lemma bfold_left_inject_x_er : forall A (b : buffer (fstored A)) (d : fchain A),
    fc_er (bfold_left inject_chain_x b d)
    = bfold_left inject_chain_f (map fs_er b) (fc_er d).
Proof.
  intros A b. unfold bfold_left.
  induction b as [| x b IH]; intros d; cbn [fold_left map]; [reflexivity|].
  rewrite IH, inject_chain_x_er, inject_chain_v2_eq, inject_chain_f_eq.
  rewrite <- inject_chain_f_eq. reflexivity.
Qed.

Definition concat_small_left_x {A : Type}
    (p3 : buffer (fstored A)) (e : fchain A) : option (fchain A) :=
  if bsize p3 <? 8 then Some (bfold_right push_chain_x e p3)
  else
    match e with
    | FEmpty => None
    | FPair l rt =>
        match fcell l with
        | Some (bl, nl, rl) =>
            match root_and_child_x bl nl rl with
            | (FNode _ p2 s2, d2) =>
                Some (FPair (tree_of_x (FNode KLeft p3 s2)
                               (push_chain_x (FSmall p2) d2)) rt)
            end
        | None => None
        end
    | _ =>
        match fcell e with
        | Some (b, n, rest) =>
            match root_and_child_x b n rest with
            | (FNode _ p2 s2, d2) =>
                match d2 with
                | FEmpty =>
                    match beject2 p2 with
                    | Some (p2', y, z) =>
                        Some (tree_of_x
                                (FNode KOnly p3 (bpush y (bpush z s2)))
                                (push_chain_x (FSmall p2') FEmpty))
                    | None => None
                    end
                | _ =>
                    Some (tree_of_x (FNode KOnly p3 s2)
                            (push_chain_x (FSmall p2) d2))
                end
            end
        | None => None
        end
    end.

Lemma concat_small_left_x_er : forall A (p3 : buffer (fstored A)) e,
    concat_small_left_f (map fs_er p3) (fc_er e)
    = option_map fc_er (concat_small_left_x p3 e).
Proof.
  intros A p3 e.
  unfold concat_small_left_f, concat_small_left_x.
  rewrite map_bsize.
  destruct (bsize p3 <? 8).
  - cbn [option_map]. rewrite bfold_right_push_x_er. reflexivity.
  - destruct e as [| k p s rest | b n rest | l rt]; [reflexivity | | |].
    + (* FFlat single cell *)
      cbn [fcell]. rewrite fc_er_flat.
      cbn [root_and_child root_and_child_x].
      destruct rest as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_beject2;
          destruct (beject2 p) as [[[p2' y] z]|]; cbn [option_map];
          [er_done | reflexivity]
        | er_done .. ].
    + (* FSingle single cell *)
      cbn [fcell fc_er].
      rewrite (root_and_child_x_er b n rest).
      destruct (root_and_child_x b n rest) as [[k2 p2 s2] d2].
      cbn [fst snd]. rewrite fn_er_node.
      destruct d2 as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_beject2;
          destruct (beject2 p2) as [[[p2' y] z]|]; cbn [option_map];
          [er_done | reflexivity]
        | er_done .. ].
    + (* FPair *)
      cbn [fc_er].
      destruct (fcell l) as [[[bl nl] rl]|] eqn:Hl.
      * rewrite (fcell_er Hl).
        rewrite (root_and_child_x_er bl nl rl).
        destruct (root_and_child_x bl nl rl) as [[k2 p2 s2] d2].
        cbn [fst snd]. rewrite fn_er_node.
        er_done.
      * destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
          rewrite ?Hl'; reflexivity.
Qed.

Definition concat_small_right_x {A : Type}
    (d : fchain A) (s3 : buffer (fstored A)) : option (fchain A) :=
  if bsize s3 <? 8 then Some (bfold_left inject_chain_x s3 d)
  else
    match d with
    | FEmpty => None
    | FPair lt r =>
        match fcell r with
        | Some (br, nr, rr) =>
            match root_and_child_x br nr rr with
            | (FNode _ p1 s1, d1) =>
                Some (FPair lt (tree_of_x (FNode KRight p1 s3)
                                  (inject_chain_x d1 (FSmall s1))))
            end
        | None => None
        end
    | _ =>
        match fcell d with
        | Some (b, n, rest) =>
            match root_and_child_x b n rest with
            | (FNode _ p1 s1, d1) =>
                match d1 with
                | FEmpty =>
                    match bpop2 s1 with
                    | Some (x, y, s1') =>
                        Some (tree_of_x
                                (FNode KOnly (binject (binject p1 x) y) s3)
                                (push_chain_x (FSmall s1') FEmpty))
                    | None => None
                    end
                | _ =>
                    Some (tree_of_x (FNode KOnly p1 s3)
                            (inject_chain_x d1 (FSmall s1)))
                end
            end
        | None => None
        end
    end.

Lemma concat_small_right_x_er : forall A (d : fchain A) s3,
    concat_small_right_f (fc_er d) (map fs_er s3)
    = option_map fc_er (concat_small_right_x d s3).
Proof.
  intros A d s3.
  unfold concat_small_right_f, concat_small_right_x.
  rewrite map_bsize.
  destruct (bsize s3 <? 8).
  - cbn [option_map]. rewrite bfold_left_inject_x_er. reflexivity.
  - destruct d as [| k p s rest | b n rest | lt r]; [reflexivity | | |].
    + cbn [fcell]. rewrite fc_er_flat.
      cbn [root_and_child root_and_child_x].
      destruct rest as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_bpop2;
          destruct (bpop2 s) as [[[x y] s1']|]; cbn [option_map];
          [er_done | reflexivity]
        | er_done .. ].
    + cbn [fcell fc_er].
      rewrite (root_and_child_x_er b n rest).
      destruct (root_and_child_x b n rest) as [[k1 p1 s1] d1].
      cbn [fst snd]. rewrite fn_er_node.
      destruct d1 as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_bpop2;
          destruct (bpop2 s1) as [[[x y] s1']|]; cbn [option_map];
          [er_done | reflexivity]
        | er_done .. ].
    + cbn [fc_er].
      destruct (fcell r) as [[[br nr] rr]|] eqn:Hr.
      * rewrite (fcell_er Hr).
        rewrite (root_and_child_x_er br nr rr).
        destruct (root_and_child_x br nr rr) as [[k1 p1 s1] d1].
        cbn [fst snd]. rewrite fn_er_node.
        er_done.
      * destruct (fcell_none_er Hr) as [Hr' | (l2 & r2 & Hr')];
          rewrite ?Hr'; reflexivity.
Qed.

Definition cad_concat_x {A : Type} (d e : fchain A) : option (fchain A) :=
  match d, e with
  | FEmpty, _ => Some e
  | _, FEmpty => Some d
  | _, _ =>
      match degenerate_buf_x d, degenerate_buf_x e with
      | Some p, Some s =>
          if (bsize p <? 8) || (bsize s <? 8)
          then Some (FFlat KOnly (bapp p s) bempty FEmpty)
          else Some (FFlat KOnly p s FEmpty)
      | Some p, None => concat_small_left_x p e
      | None, Some s => concat_small_right_x d s
      | None, None =>
          match make_left_x d, make_right_x e with
          | Some t, Some u => Some (FPair t u)
          | _, _ => None
          end
      end
  end.

Lemma cad_concat_x_er : forall A (d e : fchain A),
    cad_concat_f (fc_er d) (fc_er e) = option_map fc_er (cad_concat_x d e).
Proof.
  intros A d e.
  pose proof (degenerate_buf_x_er d) as Hd.
  pose proof (degenerate_buf_x_er e) as He.
  pose proof (make_left_x_er d) as HL.
  pose proof (make_right_x_er e) as HR.
  assert (HCL : forall p, concat_small_left_f (map fs_er p) (fc_er e)
                          = option_map fc_er (concat_small_left_x p e))
    by (intros; apply concat_small_left_x_er).
  assert (HCR : forall sb, concat_small_right_f (fc_er d) (map fs_er sb)
                           = option_map fc_er (concat_small_right_x d sb))
    by (intros; apply concat_small_right_x_er).
  destruct d as [| kd pd sd rd | bd nd rd | ld rrd];
    destruct e as [| ke pe se re | be ne re | le rre];
    try (cbn [cad_concat_x cad_concat_f fc_er]; reflexivity);
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in Hd;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in He;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in HL;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in HR;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in HCL;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair in HCR;
    rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair;
    cbn [cad_concat_x cad_concat_f];
    rewrite Hd, He;
    (repeat match goal with
            | |- context [degenerate_buf_x ?x] =>
                destruct (degenerate_buf_x x); cbn [option_map]
            end;
     [ rewrite !map_bsize;
       destruct (_ || _); cbn [option_map];
       rewrite fc_er_flat, ?map_bapp; reflexivity
     | apply HCL
     | apply HCR
     | rewrite HL, HR;
       destruct (make_left_x _); cbn [option_map]; [|reflexivity];
       destruct (make_right_x _); cbn [option_map]; reflexivity ]).
Qed.

(* ========================================================================== *)
(* Pop / eject with repair.                                                    *)
(* ========================================================================== *)

Definition node_pop_x {A : Type} (n : fnode A)
  : option (fstored A * fnode A) :=
  match n with
  | FNode k p s =>
      match bpop p with
      | Some (x, p') => Some (x, FNode k p' s)
      | None =>
          match bpop s with
          | Some (x, s') => Some (x, FNode k p s')
          | None => None
          end
      end
  end.

Lemma node_pop_x_er : forall A (n : fnode A),
    node_pop_f (fn_er n)
    = option_map (fun '(x, n') => (fs_er x, fn_er n')) (node_pop_x n).
Proof.
  intros A [k p s].
  unfold node_pop_f, node_pop_x.
  rewrite fn_er_node, map_bpop.
  destruct (bpop p) as [[x p']|]; cbn [option_map].
  - rewrite fn_er_node. reflexivity.
  - rewrite map_bpop.
    destruct (bpop s) as [[x s']|]; cbn [option_map]; [|reflexivity].
    rewrite fn_er_node. reflexivity.
Qed.

Definition node_eject_x {A : Type} (n : fnode A)
  : option (fnode A * fstored A) :=
  match n with
  | FNode k p s =>
      match beject s with
      | Some (s', x) => Some (FNode k p s', x)
      | None =>
          match beject p with
          | Some (p', x) => Some (FNode k p' bempty, x)
          | None => None
          end
      end
  end.

Lemma node_eject_x_er : forall A (n : fnode A),
    node_eject_f (fn_er n)
    = option_map (fun '(n', x) => (fn_er n', fs_er x)) (node_eject_x n).
Proof.
  intros A [k p s].
  unfold node_eject_f, node_eject_x.
  rewrite fn_er_node, map_beject.
  destruct (beject s) as [[s' x]|]; cbn [option_map].
  - rewrite fn_er_node. reflexivity.
  - rewrite map_beject.
    destruct (beject p) as [[p' x]|]; cbn [option_map]; [|reflexivity].
    rewrite fn_er_node. reflexivity.
Qed.

Definition rebuild_childless_x {A : Type} (n : fnode A) : fchain A :=
  match n with
  | FNode k p s =>
      if bis_empty p && bis_empty s then FEmpty
      else
        match k with
        | KOnly =>
            if bis_empty p || bis_empty s
            then FFlat k p s FEmpty
            else if (bsize p <? 5) || (bsize s <? 5)
                 then FFlat KOnly (bapp p s) bempty FEmpty
                 else FFlat k p s FEmpty
        | _ => FFlat k p s FEmpty
        end
  end.

Lemma rebuild_childless_x_er : forall A (n : fnode A),
    rebuild_childless_f (fn_er n) = fc_er (rebuild_childless_x n).
Proof.
  intros A [k p s].
  unfold rebuild_childless_f, rebuild_childless_x.
  rewrite fn_er_node, !map_bis_empty.
  destruct (bis_empty p && bis_empty s); [reflexivity|].
  destruct k;
    [ destruct (bis_empty p || bis_empty s);
      [ rewrite fc_er_flat; reflexivity |];
      rewrite !map_bsize;
      destruct ((bsize p <? 5) || (bsize s <? 5));
      rewrite fc_er_flat, ?map_bapp; reflexivity
    | rewrite fc_er_flat; reflexivity
    | rewrite fc_er_flat; reflexivity ].
Qed.

Fixpoint pop_raw_x {A : Type} (c : fchain A)
  : option (fstored A * fchain A) :=
  match c with
  | FEmpty => None
  | FFlat k p s rest =>
      match node_pop_x (FNode k p s) with
      | Some (x, n') =>
          match rest with
          | FEmpty => Some (x, rebuild_childless_x n')
          | _ => Some (x, tree_of_x n' rest)
          end
      | None => None
      end
  | FSingle b n rest =>
      let '(n0, child) := root_and_child_x b n rest in
      match node_pop_x n0 with
      | Some (x, n') =>
          match child with
          | FEmpty => Some (x, rebuild_childless_x n')
          | _ => Some (x, tree_of_x n' child)
          end
      | None => None
      end
  | FPair l r =>
      match pop_raw_x l with
      | Some (x, l') =>
          match l' with
          | FEmpty => Some (x, r)
          | FFlat _ lp ls FEmpty =>
              if bsize lp <? 5
              then
                match fcell r with
                | Some (br, nr, rr) =>
                    match root_and_child_x br nr rr with
                    | (FNode _ p2 s2, d2) =>
                        Some (x, tree_of_x
                                   (FNode KOnly (bapp lp (bapp ls p2)) s2)
                                   d2)
                    end
                | None => None
                end
              else Some (x, FPair l' r)
          | FSingle FHole (FNode _ lp ls) FEmpty =>
              if bsize lp <? 5
              then
                match fcell r with
                | Some (br, nr, rr) =>
                    match root_and_child_x br nr rr with
                    | (FNode _ p2 s2, d2) =>
                        Some (x, tree_of_x
                                   (FNode KOnly (bapp lp (bapp ls p2)) s2)
                                   d2)
                    end
                | None => None
                end
              else Some (x, FPair l' r)
          | _ => Some (x, FPair l' r)
          end
      | None => None
      end
  end.

Lemma pop_raw_x_er : forall A (c : fchain A),
    pop_raw_f (fc_er c)
    = option_map (fun '(x, c') => (fs_er x, fc_er c')) (pop_raw_x c).
Proof.
  intros A c.
  induction c as [| k p s rest _ | b n rest _ | l IHl r _].
  - reflexivity.
  - rewrite fc_er_flat. cbn [pop_raw_f pop_raw_x root_and_child].
    rewrite <- fn_er_node, node_pop_x_er.
    destruct (node_pop_x (FNode k p s)) as [[x n']|]; cbn [option_map];
      [|reflexivity].
    destruct rest as [| ? ? ? ? | ? ? ? | ? ?];
      [ cbn [option_map]; rewrite rebuild_childless_x_er; reflexivity
      | cbn [option_map];
        rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, tree_of_x_er;
        reflexivity .. ].
  - rewrite fc_er_single. cbn [pop_raw_f pop_raw_x].
    rewrite (root_and_child_x_er b n rest).
    destruct (root_and_child_x b n rest) as [n0 child].
    cbn [fst snd].
    rewrite node_pop_x_er.
    destruct (node_pop_x n0) as [[x n']|]; cbn [option_map];
      [|reflexivity].
    destruct child as [| ? ? ? ? | ? ? ? | ? ?];
      [ cbn [option_map]; rewrite rebuild_childless_x_er; reflexivity
      | cbn [option_map];
        rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, tree_of_x_er;
        reflexivity .. ].
  - rewrite fc_er_pair. cbn [pop_raw_f pop_raw_x].
    rewrite IHl.
    destruct (pop_raw_x l) as [[x l']|]; cbn [option_map]; [|reflexivity].
    destruct l' as [| lk lp ls lrest | lb ln lrest | ll lr];
      cbn [option_map].
    + reflexivity.
    + (* FFlat: degenerate iff lrest = FEmpty *)
      rewrite fc_er_flat.
      destruct lrest as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_bsize;
          destruct (bsize lp <? 5);
          [ destruct (fcell r) as [[[br nr] rr]|] eqn:Hr;
            [ rewrite (fcell_er Hr), (root_and_child_x_er br nr rr);
              destruct (root_and_child_x br nr rr) as [[k2 p2 s2] d2];
              cbn [option_map fst snd];
              rewrite fn_er_node, tree_of_x_er, fn_er_node, !map_bapp;
              reflexivity
            | destruct (fcell_none_er Hr) as [Hr' | (l2 & r2 & Hr')];
              rewrite Hr'; reflexivity ]
          | reflexivity ]
        | rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair; reflexivity .. ].
    + (* FSingle: degenerate iff body hole, rest empty *)
      rewrite fc_er_single.
      destruct lb as [| ? ? | ? ? ? | ? ? ?];
        [ destruct ln as [lk lp ls]; rewrite fn_er_node; cbn [fb_er];
          destruct lrest as [| ? ? ? ? | ? ? ? | ? ?];
          [ rewrite map_bsize;
            destruct (bsize lp <? 5);
            [ destruct (fcell r) as [[[br nr] rr]|] eqn:Hr;
              [ rewrite (fcell_er Hr), (root_and_child_x_er br nr rr);
                destruct (root_and_child_x br nr rr) as [[k2 p2 s2] d2];
                cbn [option_map fst snd];
                rewrite fn_er_node, tree_of_x_er, fn_er_node, !map_bapp;
                reflexivity
              | destruct (fcell_none_er Hr) as [Hr' | (l2 & r2 & Hr')];
                rewrite Hr'; reflexivity ]
            | reflexivity ]
          | rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, ?fn_er_node;
            reflexivity .. ]
        | rewrite ?fc_er_pair, ?fc_er_single; reflexivity .. ].
    + rewrite !fc_er_pair. reflexivity.
Qed.

Fixpoint eject_raw_x {A : Type} (c : fchain A)
  : option (fchain A * fstored A) :=
  match c with
  | FEmpty => None
  | FFlat k p s rest =>
      match node_eject_x (FNode k p s) with
      | Some (n', x) =>
          match rest with
          | FEmpty => Some (rebuild_childless_x n', x)
          | _ => Some (tree_of_x n' rest, x)
          end
      | None => None
      end
  | FSingle b n rest =>
      let '(n0, child) := root_and_child_x b n rest in
      match node_eject_x n0 with
      | Some (n', x) =>
          match child with
          | FEmpty => Some (rebuild_childless_x n', x)
          | _ => Some (tree_of_x n' child, x)
          end
      | None => None
      end
  | FPair l r =>
      match eject_raw_x r with
      | Some (r', x) =>
          match r' with
          | FEmpty => Some (l, x)
          | FFlat _ rp rs FEmpty =>
              if bsize rs <? 5
              then
                match fcell l with
                | Some (bl, nl, rl) =>
                    match root_and_child_x bl nl rl with
                    | (FNode _ p1 s1, d1) =>
                        Some (tree_of_x
                                (FNode KOnly p1 (bapp s1 (bapp rp rs)))
                                d1, x)
                    end
                | None => None
                end
              else Some (FPair l r', x)
          | FSingle FHole (FNode _ rp rs) FEmpty =>
              if bsize rs <? 5
              then
                match fcell l with
                | Some (bl, nl, rl) =>
                    match root_and_child_x bl nl rl with
                    | (FNode _ p1 s1, d1) =>
                        Some (tree_of_x
                                (FNode KOnly p1 (bapp s1 (bapp rp rs)))
                                d1, x)
                    end
                | None => None
                end
              else Some (FPair l r', x)
          | _ => Some (FPair l r', x)
          end
      | None => None
      end
  end.

Lemma eject_raw_x_er : forall A (c : fchain A),
    eject_raw_f (fc_er c)
    = option_map (fun '(c', x) => (fc_er c', fs_er x)) (eject_raw_x c).
Proof.
  intros A c.
  induction c as [| k p s rest _ | b n rest _ | l _ r IHr].
  - reflexivity.
  - rewrite fc_er_flat. cbn [eject_raw_f eject_raw_x root_and_child].
    rewrite <- fn_er_node, node_eject_x_er.
    destruct (node_eject_x (FNode k p s)) as [[n' x]|]; cbn [option_map];
      [|reflexivity].
    destruct rest as [| ? ? ? ? | ? ? ? | ? ?];
      [ cbn [option_map]; rewrite rebuild_childless_x_er; reflexivity
      | cbn [option_map];
        rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, tree_of_x_er;
        reflexivity .. ].
  - rewrite fc_er_single. cbn [eject_raw_f eject_raw_x].
    rewrite (root_and_child_x_er b n rest).
    destruct (root_and_child_x b n rest) as [n0 child].
    cbn [fst snd].
    rewrite node_eject_x_er.
    destruct (node_eject_x n0) as [[n' x]|]; cbn [option_map];
      [|reflexivity].
    destruct child as [| ? ? ? ? | ? ? ? | ? ?];
      [ cbn [option_map]; rewrite rebuild_childless_x_er; reflexivity
      | cbn [option_map];
        rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, tree_of_x_er;
        reflexivity .. ].
  - rewrite fc_er_pair. cbn [eject_raw_f eject_raw_x].
    rewrite IHr.
    destruct (eject_raw_x r) as [[r' x]|]; cbn [option_map]; [|reflexivity].
    destruct r' as [| rk rp rs rrest | rb rn rrest | rl rr];
      cbn [option_map].
    + reflexivity.
    + rewrite fc_er_flat.
      destruct rrest as [| ? ? ? ? | ? ? ? | ? ?];
        [ rewrite map_bsize;
          destruct (bsize rs <? 5);
          [ destruct (fcell l) as [[[bl nl] rl]|] eqn:Hl;
            [ rewrite (fcell_er Hl), (root_and_child_x_er bl nl rl);
              destruct (root_and_child_x bl nl rl) as [[k1 p1 s1] d1];
              cbn [option_map fst snd];
              rewrite fn_er_node, tree_of_x_er, fn_er_node, !map_bapp;
              reflexivity
            | destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
              rewrite Hl'; reflexivity ]
          | reflexivity ]
        | rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair; reflexivity .. ].
    + rewrite fc_er_single.
      destruct rb as [| ? ? | ? ? ? | ? ? ?];
        [ destruct rn as [rk rp rs]; rewrite fn_er_node; cbn [fb_er];
          destruct rrest as [| ? ? ? ? | ? ? ? | ? ?];
          [ rewrite map_bsize;
            destruct (bsize rs <? 5);
            [ destruct (fcell l) as [[[bl nl] rl]|] eqn:Hl;
              [ rewrite (fcell_er Hl), (root_and_child_x_er bl nl rl);
                destruct (root_and_child_x bl nl rl) as [[k1 p1 s1] d1];
                cbn [option_map fst snd];
                rewrite fn_er_node, tree_of_x_er, fn_er_node, !map_bapp;
                reflexivity
              | destruct (fcell_none_er Hl) as [Hl' | (l2 & r2 & Hl')];
                rewrite Hl'; reflexivity ]
            | reflexivity ]
          | rewrite ?fc_er_flat, ?fc_er_single, ?fc_er_pair, ?fn_er_node;
            reflexivity .. ]
        | rewrite ?fc_er_pair, ?fc_er_single; reflexivity .. ].
    + rewrite !fc_er_pair. reflexivity.
Qed.
