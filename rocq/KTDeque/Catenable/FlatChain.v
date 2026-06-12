(** * KTDeque.Catenable.FlatChain — the fused spine representation.

    A verified DATA-CONSTRUCTOR-FUSION pass over the §6 chain (the
    fourth verified transformation, after OpsFast / OpsFused /
    SizedChain): the dominant spine shape
    [CSingle (Pkt BHole (Node k p s)) rest] — three nested heap blocks
    rebuilt by EVERY push/inject and by the green/red arms of every
    rebundle — becomes the single constructor [FFlat k p s rest], and
    the general packet cell [CSingle (Pkt b n) rest] becomes the single
    constructor [FSingle b n rest] (fusing the [CSingle]∘[Pkt]
    composition).

    Correctness is by a TOTAL ERASURE [fc_er : fchain -> cchain] (and
    its mutual companions) with per-operation commutation lemmas in
    FlatOps.v: [fc_er (op_x args) = op_f (erased args)].  Because the
    relation is an erasure rather than an isomorphism, the overlap
    between [FFlat k p s rest] and [FSingle FHole (FNode k p s) rest]
    is harmless — both erase to the same chain; the smart constructor
    [fsingle] keeps the fused form on every construction path, but no
    canonical-form invariant is needed for the keystone transfer
    (FlatKeystone.v).

    Cost: each fused constructor is one heap block where the erased
    form allocates two or three; the operation-level primitive counts
    of Cost.v are unchanged (the mirrors perform the same buffer
    primitive sequence — see FlatOps.v). *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model Color BufPrims.

Set Implicit Arguments.

(* ========================================================================== *)
(* The fused mutual family.                                                    *)
(* ========================================================================== *)

Inductive fstored (A : Type) : Type :=
| FGround : A -> fstored A
| FSmall  : buffer (fstored A) -> fstored A
| FBig    : buffer (fstored A) -> fchain A -> buffer (fstored A) -> fstored A
with fnode (A : Type) : Type :=
| FNode : kind -> buffer (fstored A) -> buffer (fstored A) -> fnode A
with fbody (A : Type) : Type :=
| FHole   : fbody A
| FBSingle : fnode A -> fbody A -> fbody A
| FBPairY  : fnode A -> fbody A -> fchain A -> fbody A
| FBPairO  : fnode A -> fchain A -> fbody A -> fbody A
with fchain (A : Type) : Type :=
| FEmpty  : fchain A
| FFlat   : kind -> buffer (fstored A) -> buffer (fstored A) -> fchain A
            -> fchain A
| FSingle : fbody A -> fnode A -> fchain A -> fchain A
| FPair   : fchain A -> fchain A -> fchain A.

Arguments FGround {A} _.
Arguments FSmall  {A} _.
Arguments FBig    {A} _ _ _.
Arguments FNode   {A} _ _ _.
Arguments FHole   {A}.
Arguments FBSingle {A} _ _.
Arguments FBPairY {A} _ _ _.
Arguments FBPairO {A} _ _ _.
Arguments FEmpty  {A}.
Arguments FFlat   {A} _ _ _ _.
Arguments FSingle {A} _ _ _.
Arguments FPair   {A} _ _.

(* ========================================================================== *)
(* Erasure to the model chain.                                                 *)
(* ========================================================================== *)

Fixpoint fs_er {A : Type} (s : fstored A) : stored A :=
  match s with
  | FGround a => SGround a
  | FSmall b =>
      SSmall ((fix go (l : list (fstored A)) : list (stored A) :=
                 match l with
                 | [] => []
                 | x :: r => fs_er x :: go r
                 end) b)
  | FBig p c q =>
      SBig ((fix go (l : list (fstored A)) : list (stored A) :=
               match l with
               | [] => []
               | x :: r => fs_er x :: go r
               end) p)
        (fc_er c)
        ((fix go (l : list (fstored A)) : list (stored A) :=
            match l with
            | [] => []
            | x :: r => fs_er x :: go r
            end) q)
  end
with fn_er {A : Type} (n : fnode A) : cnode A :=
  match n with
  | FNode k p s =>
      Node k
        ((fix go (l : list (fstored A)) : list (stored A) :=
            match l with
            | [] => []
            | x :: r => fs_er x :: go r
            end) p)
        ((fix go (l : list (fstored A)) : list (stored A) :=
            match l with
            | [] => []
            | x :: r => fs_er x :: go r
            end) s)
  end
with fb_er {A : Type} (b : fbody A) : cbody A :=
  match b with
  | FHole => BHole
  | FBSingle n b' => BSingle (fn_er n) (fb_er b')
  | FBPairY n b' rc => BPairY (fn_er n) (fb_er b') (fc_er rc)
  | FBPairO n lc b' => BPairO (fn_er n) (fc_er lc) (fb_er b')
  end
with fc_er {A : Type} (c : fchain A) : cchain A :=
  match c with
  | FEmpty => CEmpty
  | FFlat k p s rest =>
      CSingle
        (Pkt BHole
           (Node k
              ((fix go (l : list (fstored A)) : list (stored A) :=
                  match l with
                  | [] => []
                  | x :: r => fs_er x :: go r
                  end) p)
              ((fix go (l : list (fstored A)) : list (stored A) :=
                  match l with
                  | [] => []
                  | x :: r => fs_er x :: go r
                  end) s)))
        (fc_er rest)
  | FSingle b n rest => CSingle (Pkt (fb_er b) (fn_er n)) (fc_er rest)
  | FPair l r => CPair (fc_er l) (fc_er r)
  end.

(** The inner buffer fixes compute [map fs_er]. *)
Lemma fs_er_small : forall A (b : buffer (fstored A)),
    fs_er (FSmall b) = SSmall (map fs_er b).
Proof. reflexivity. Qed.

Lemma fs_er_big : forall A (p : buffer (fstored A)) c q,
    fs_er (FBig p c q) = SBig (map fs_er p) (fc_er c) (map fs_er q).
Proof. reflexivity. Qed.

Lemma fn_er_node : forall A k (p s : buffer (fstored A)),
    fn_er (FNode k p s) = Node k (map fs_er p) (map fs_er s).
Proof. reflexivity. Qed.

Lemma fc_er_flat : forall A k (p s : buffer (fstored A)) rest,
    fc_er (FFlat k p s rest)
    = CSingle (Pkt BHole (Node k (map fs_er p) (map fs_er s))) (fc_er rest).
Proof. reflexivity. Qed.

Lemma fc_er_empty : forall A, fc_er (@FEmpty A) = CEmpty.
Proof. reflexivity. Qed.

Lemma fc_er_single : forall A (b : fbody A) n rest,
    fc_er (FSingle b n rest)
    = CSingle (Pkt (fb_er b) (fn_er n)) (fc_er rest).
Proof. reflexivity. Qed.

Lemma fc_er_pair : forall A (l r : fchain A),
    fc_er (FPair l r) = CPair (fc_er l) (fc_er r).
Proof. reflexivity. Qed.

(** Erasure rewriting set: rewrite with the equations above instead of
    [cbn]-reducing an erasure application — [cbn] exposes the inner
    buffer fixes, which then defeat syntactic rewriting against the
    [map fs_er] forms. *)

(* ========================================================================== *)
(* The smart single constructor: keep hole-bodied packets fused.               *)
(* ========================================================================== *)

Definition fsingle {A : Type} (b : fbody A) (n : fnode A) (rest : fchain A)
  : fchain A :=
  match b with
  | FHole => match n with FNode k p s => FFlat k p s rest end
  | _ => FSingle b n rest
  end.

Lemma fc_er_fsingle : forall A (b : fbody A) n rest,
    fc_er (fsingle b n rest)
    = CSingle (Pkt (fb_er b) (fn_er n)) (fc_er rest).
Proof. intros A b n rest. destruct b; [destruct n|..]; reflexivity. Qed.

(* ========================================================================== *)
(* Buffer-map commutation toolkit (generic in the element map).                *)
(* ========================================================================== *)

Section MapPrims.
  Variables (X Y : Type) (f : X -> Y).

  Lemma map_bsize : forall b : buffer X, bsize (map f b) = bsize b.
  Proof. intros b. apply length_map. Qed.

  Lemma map_bis_empty : forall b : buffer X,
      bis_empty (map f b) = bis_empty b.
  Proof. intros [| x b]; reflexivity. Qed.

  Lemma map_bpush : forall x (b : buffer X),
      map f (bpush x b) = bpush (f x) (map f b).
  Proof. reflexivity. Qed.

  Lemma map_binject : forall (b : buffer X) x,
      map f (binject b x) = binject (map f b) (f x).
  Proof. intros b x. unfold binject. apply map_app. Qed.

  Lemma map_bapp : forall b c : buffer X,
      map f (bapp b c) = bapp (map f b) (map f c).
  Proof. intros b c. apply map_app. Qed.

  Lemma map_b1 : forall x, map f (b1 x) = b1 (f x).
  Proof. reflexivity. Qed.

  Lemma map_b2 : forall x y, map f (b2 x y) = b2 (f x) (f y).
  Proof. reflexivity. Qed.

  Lemma map_b3 : forall x y z, map f (b3 x y z) = b3 (f x) (f y) (f z).
  Proof. reflexivity. Qed.

  Lemma map_bempty : map f bempty = bempty.
  Proof. reflexivity. Qed.

  Lemma map_bpop : forall b : buffer X,
      bpop (map f b)
      = option_map (fun '(x, r) => (f x, map f r)) (bpop b).
  Proof. intros [| x b]; reflexivity. Qed.

  Lemma map_beject : forall b : buffer X,
      beject (map f b)
      = option_map (fun '(r, x) => (map f r, f x)) (beject b).
  Proof.
    intros b. unfold beject.
    rewrite <- map_rev. destruct (rev b) as [| x r]; cbn; [reflexivity|].
    rewrite <- map_rev. reflexivity.
  Qed.

  Lemma map_bpop2 : forall b : buffer X,
      bpop2 (map f b)
      = option_map (fun '(x, y, r) => (f x, f y, map f r)) (bpop2 b).
  Proof. intros [| x [| y b]]; reflexivity. Qed.

  Lemma map_beject2 : forall b : buffer X,
      beject2 (map f b)
      = option_map (fun '(r, y, z) => (map f r, f y, f z)) (beject2 b).
  Proof.
    intros b. unfold beject2.
    rewrite <- map_rev. destruct (rev b) as [| z [| y r]]; cbn; try reflexivity.
    rewrite <- map_rev. reflexivity.
  Qed.

  Lemma map_beject3 : forall b : buffer X,
      beject3 (map f b)
      = option_map (fun '(r, a, bb, c) => (map f r, f a, f bb, f c))
          (beject3 b).
  Proof.
    intros b. unfold beject3.
    rewrite <- map_rev.
    destruct (rev b) as [| c [| bb [| a r]]]; cbn; try reflexivity.
    rewrite <- map_rev. reflexivity.
  Qed.

End MapPrims.

(* ========================================================================== *)
(* Chain-level helpers.                                                        *)
(* ========================================================================== *)

Definition fchain_has_node {A : Type} (c : fchain A) : bool :=
  match c with FEmpty => false | _ => true end.

Lemma fchain_has_node_er : forall A (c : fchain A),
    chain_has_node (fc_er c) = fchain_has_node c.
Proof. intros A [| k p s rest | b n rest | l r]; reflexivity. Qed.

(* ========================================================================== *)
(* Cell-access wrappers (the §6 element-unboxing seam).                       *)
(*                                                                            *)
(* The §6 ops INSPECT stored cells in exactly two disciplines, and          *)
(* [chain_leveled] (part of [J]) makes each one total on its level:          *)
(* level-0 cells are always [FGround] (pop/eject read an element), and       *)
(* child-level cells are never ground (the repair web reads a structural     *)
(* cell).  Routing every cell match through the named wrappers below lets    *)
(* extraction map [fstored] to a ZERO-BOX carrier — a ground cell IS its     *)
(* payload, erasing one heap block PER ELEMENT — with the fallback arms      *)
(* dropped blindly.  Soundness of the blind extraction is the keystone       *)
(* itself: on [fJ] inputs (FlatKeystone.v) the fallback continuations are    *)
(* unreachable, exactly the ErasedTree/Eraw argument one layer up.           *)
(* ========================================================================== *)

Definition cell_case_ground {A R : Type} (c : fstored A)
    (kg : A -> R) (kf : R) : R :=
  match c with
  | FGround a => kg a
  | _ => kf
  end.

Definition cell_case_struct {A R : Type} (c : fstored A)
    (ks : buffer (fstored A) -> R)
    (kb : buffer (fstored A) -> fchain A -> buffer (fstored A) -> R)
    (kf : R) : R :=
  match c with
  | FGround _ => kf
  | FSmall b => ks b
  | FBig p d q => kb p d q
  end.
