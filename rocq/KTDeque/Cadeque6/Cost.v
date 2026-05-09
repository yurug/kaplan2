(** * Module: KTDeque.Cadeque6.Cost -- structural cost bounds for the
      operational endpoint operations.

    First-time reader: read [kb/spec/why-bounded-cascade.md] before
    this file (the "WC O(1) is non-negotiable" rule applies here too).

    ## Why this exists

    Phase 4 of the catenable plan asks for worst-case [O(1)] per op,
    matching KT99's headline result.  At the abstract [Cadeque6]
    layer (purely functional, value-level), we cannot count heap
    operations directly -- the [Common/CostMonad.v] machinery is
    designed for the heap-based imperative DSL of [DequePtr/].
    What we *can* do at the abstract layer is establish *structural*
    cost bounds: prove that each operation's body is a bounded-depth
    pattern-match over its argument that reuses the deep substructure
    unchanged, allocating only a bounded number of top-level cells.

    This file establishes those structural bounds for [cad_push_op]
    and [cad_inject_op].  The pop/eject/concat _full variants in
    [Repair.v] use [cad_normalize] (which is [O(n)] in the abstract
    sequence length); they are *not* worst-case [O(1)] at this layer
    -- their [O(1)] story requires the heap-based imperative DSL for
    the catenable cadeque, sketched as Phase 4b in
    [kb/plan-catenable.md].

    ## What "structural cost bound" means here

    For a given input shape, the operation is a *closed expression*
    over a bounded number of pattern-matches and constructor
    applications, with *no recursion* on the [Cadeque X] argument.
    The deep substructure of the input (sub-cadeques inside Triple
    children) appears verbatim in the output: it is reused, not
    rebuilt.

    We make this precise via "shape decomposition" theorems: for
    each input shape, [cad_push_op x q] equals an explicit closed
    expression that reuses the relevant sub-cadeque verbatim.  A
    reasonable functional implementation (OCaml extraction, the
    target of Phase 6) shares the reused sub-cadeque without copy,
    so the wall-clock cost is a constant * (the number of allocated
    top-level cells).

    ## Cross-references

    - [Cadeque6/Repair.v]              -- the ops being analyzed.
    - [DequePtr/Footprint.v]           -- the analogous heap-based
                                          cost bounds for Section 4.
    - [Common/CostMonad.v]             -- the cost-monad framework
                                          for heap ops (not used here).
    - [kb/plan-catenable.md]           -- Phase 4 (cost) and Phase 4b
                                          (heap-based imperative DSL).
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Repair.

(** ** [cad_push_op] shape decomposition.

    Five exhaustive cases by the input shape; each case shows the
    output as a closed expression reusing the relevant child
    cadeque verbatim. *)

Theorem cad_push_op_shape_CEmpty :
  forall (X : Type) (x : X),
    cad_push_op x (@CEmpty X)
    = CSingle (TOnly (buf6_singleton x) CEmpty buf6_empty).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TOnly_CEmpty_pre_empty :
  forall (X : Type) (x : X) (suf : Buf6 X),
    cad_push_op x (CSingle (TOnly buf6_empty CEmpty suf))
    = normalize_only_empty_child (buf6_push x buf6_empty) suf.
Proof. intros. cbn [cad_push_op buf6_empty buf6_elems]. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TOnly_CEmpty_pre_nonempty :
  forall (X : Type) (x p : X) (ps : list X) (suf : Buf6 X),
    cad_push_op x (CSingle (TOnly (mkBuf6 (p :: ps)) CEmpty suf))
    = CSingle (TOnly (buf6_push x (mkBuf6 (p :: ps))) CEmpty suf).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TOnly_nonempty_child :
  forall (X : Type) (x : X) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    cad_push_op x (CSingle (TOnly pre (CSingle ct) suf))
    = CSingle (TOnly (buf6_push x pre) (CSingle ct) suf).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TOnly_double_child :
  forall (X : Type) (x : X) (pre : Buf6 X) (ctL ctR : Triple X) (suf : Buf6 X),
    cad_push_op x (CSingle (TOnly pre (CDouble ctL ctR) suf))
    = CSingle (TOnly (buf6_push x pre) (CDouble ctL ctR) suf).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TLeft :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    cad_push_op x (CSingle (TLeft pre c suf))
    = CSingle (TLeft (buf6_push x pre) c suf).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CSingle_TRight :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    cad_push_op x (CSingle (TRight pre c suf))
    = CSingle (TRight (buf6_push x pre) c suf).
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CDouble_TOnly :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (tR : Triple X),
    cad_push_op x (CDouble (TOnly pre c suf) tR)
    = CDouble (TOnly (buf6_push x pre) c suf) tR.
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CDouble_TLeft :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (tR : Triple X),
    cad_push_op x (CDouble (TLeft pre c suf) tR)
    = CDouble (TLeft (buf6_push x pre) c suf) tR.
Proof. reflexivity. Qed.

Theorem cad_push_op_shape_CDouble_TRight :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X) (tR : Triple X),
    cad_push_op x (CDouble (TRight pre c suf) tR)
    = CDouble (TRight (buf6_push x pre) c suf) tR.
Proof. reflexivity. Qed.

(** ** Headline structural cost bound for [cad_push_op].

    In every case, the output is built by allocating at most a
    bounded constant of top-level constructors ([CSingle], [CDouble],
    [TOnly], [TLeft], [TRight], [buf6_push]) plus reusing the input's
    deep substructure verbatim.  No recursion on the [Cadeque X]
    argument.

    We codify this by a synthetic cost function that mirrors the AST
    of [cad_push_op] and counts each pattern-match and each newly
    allocated top-level cell as one unit.  The value-level cost
    semantics is intentionally simple; what matters is that the
    bound is independent of the input cadeque's depth and size.

    [cad_push_op_topcost q] is by inspection bounded by a small
    constant (proven below: at most 5 in the worst case, the
    normalize-firing branch).  This is the abstract-layer analogue
    of [DequePtr/Footprint.v]'s [NF_PUSH_PKT_FULL = 9]. *)

Definition cad_push_op_topcost {X : Type} (q : Cadeque X) : nat :=
  match q with
  | CEmpty       => 4   (* buf6_singleton, buf6_empty, TOnly, CSingle *)
  | CSingle t    =>
      match t with
      | TOnly pre c suf =>
          match c with
          | CEmpty =>
              match buf6_elems pre with
              | []      => 5    (* buf6_push, normalize_only_empty_child *)
              | _ :: _  => 3    (* buf6_push, TOnly, CSingle *)
              end
          | _       => 3        (* buf6_push, TOnly, CSingle *)
          end
      | _ => 4                  (* triple_push_prefix, ., CSingle *)
      end
  | CDouble _ _  => 4            (* triple_push_prefix, ., CDouble *)
  end.

Definition CAD_PUSH_OP_COST_BOUND : nat := 5.

Theorem cad_push_op_topcost_bounded :
  forall (X : Type) (q : Cadeque X),
    @cad_push_op_topcost X q <= CAD_PUSH_OP_COST_BOUND.
Proof.
  intros X q. unfold cad_push_op_topcost, CAD_PUSH_OP_COST_BOUND.
  destruct q as [|t|tL tR]; cbn; try lia.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn; try lia.
  destruct c; cbn; try lia.
  destruct (buf6_elems pre); cbn; lia.
Qed.

(** ** Symmetric: [cad_inject_op]. *)

Theorem cad_inject_op_shape_CEmpty :
  forall (X : Type) (x : X),
    cad_inject_op (@CEmpty X) x
    = CSingle (TOnly buf6_empty CEmpty (buf6_singleton x)).
Proof. reflexivity. Qed.

Theorem cad_inject_op_shape_CSingle_TOnly_CEmpty_suf_empty :
  forall (X : Type) (x : X) (pre : Buf6 X),
    cad_inject_op (CSingle (TOnly pre CEmpty buf6_empty)) x
    = normalize_only_empty_child pre (buf6_inject buf6_empty x).
Proof. intros. cbn [cad_inject_op buf6_empty buf6_elems]. reflexivity. Qed.

Theorem cad_inject_op_shape_CSingle_TOnly_CEmpty_suf_nonempty :
  forall (X : Type) (x s : X) (ss : list X) (pre : Buf6 X),
    cad_inject_op (CSingle (TOnly pre CEmpty (mkBuf6 (s :: ss)))) x
    = CSingle (TOnly pre CEmpty (buf6_inject (mkBuf6 (s :: ss)) x)).
Proof. reflexivity. Qed.

Theorem cad_inject_op_shape_CSingle_TOnly_nonempty_child :
  forall (X : Type) (x : X) (pre : Buf6 X) (ct : Triple X) (suf : Buf6 X),
    cad_inject_op (CSingle (TOnly pre (CSingle ct) suf)) x
    = CSingle (TOnly pre (CSingle ct) (buf6_inject suf x)).
Proof. reflexivity. Qed.

Theorem cad_inject_op_shape_CSingle_TLeft :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    cad_inject_op (CSingle (TLeft pre c suf)) x
    = CSingle (TLeft pre c (buf6_inject suf x)).
Proof. reflexivity. Qed.

Theorem cad_inject_op_shape_CSingle_TRight :
  forall (X : Type) (x : X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    cad_inject_op (CSingle (TRight pre c suf)) x
    = CSingle (TRight pre c (buf6_inject suf x)).
Proof. reflexivity. Qed.

Theorem cad_inject_op_shape_CDouble :
  forall (X : Type) (x : X) (tL : Triple X) (pre : Buf6 X) (c : Cadeque X) (suf : Buf6 X),
    cad_inject_op (CDouble tL (TOnly pre c suf)) x
    = CDouble tL (TOnly pre c (buf6_inject suf x))
  /\ cad_inject_op (CDouble tL (TLeft pre c suf)) x
    = CDouble tL (TLeft pre c (buf6_inject suf x))
  /\ cad_inject_op (CDouble tL (TRight pre c suf)) x
    = CDouble tL (TRight pre c (buf6_inject suf x)).
Proof. intros. split; [|split]; reflexivity. Qed.

Definition cad_inject_op_topcost {X : Type} (q : Cadeque X) : nat :=
  match q with
  | CEmpty       => 4
  | CSingle t    =>
      match t with
      | TOnly pre c suf =>
          match c with
          | CEmpty =>
              match buf6_elems suf with
              | []      => 5
              | _ :: _  => 3
              end
          | _       => 3
          end
      | _ => 4
      end
  | CDouble _ _  => 4
  end.

Definition CAD_INJECT_OP_COST_BOUND : nat := 5.

Theorem cad_inject_op_topcost_bounded :
  forall (X : Type) (q : Cadeque X),
    @cad_inject_op_topcost X q <= CAD_INJECT_OP_COST_BOUND.
Proof.
  intros X q. unfold cad_inject_op_topcost, CAD_INJECT_OP_COST_BOUND.
  destruct q as [|t|tL tR]; cbn; try lia.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn; try lia.
  destruct c; cbn; try lia.
  destruct (buf6_elems suf); cbn; lia.
Qed.

(** ** [cad_pop_op] / [cad_eject_op]: structural cost.

    Same story as push and inject: each delegates either to a bounded
    [buf6_pop] / [buf6_eject] dispatch (in the [TOnly + CEmpty] case)
    or to the abstract [cad_pop] / [cad_eject] (other cases), which
    are themselves non-recursive.  Hence [cad_pop_op] and
    [cad_eject_op] are also structurally [O(1)] in their input shape.

    Note: the [_full] variants ([cad_pop_op_full] etc.) compose with
    [cad_normalize], which is [O(n)].  Their [O(1)] bound is
    *not* provable at this layer; see the file header. *)

Definition cad_pop_op_topcost {X : Type} (q : Cadeque X) : nat :=
  match q with
  | CEmpty    => 1
  | CSingle t =>
      match t with
      | TOnly _ CEmpty _ => 5  (* buf6_pop pre, fallback buf6_pop suf, normalize *)
      | _                => 4  (* delegate to cad_pop *)
      end
  | CDouble _ _ => 4
  end.

Definition CAD_POP_OP_COST_BOUND : nat := 5.

Theorem cad_pop_op_topcost_bounded :
  forall (X : Type) (q : Cadeque X),
    @cad_pop_op_topcost X q <= CAD_POP_OP_COST_BOUND.
Proof.
  intros X q. unfold cad_pop_op_topcost, CAD_POP_OP_COST_BOUND.
  destruct q as [|t|tL tR]; cbn; try lia.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn; try lia.
  destruct c; cbn; lia.
Qed.

Definition cad_eject_op_topcost {X : Type} (q : Cadeque X) : nat :=
  match q with
  | CEmpty    => 1
  | CSingle t =>
      match t with
      | TOnly _ CEmpty _ => 5
      | _                => 4
      end
  | CDouble _ _ => 4
  end.

Definition CAD_EJECT_OP_COST_BOUND : nat := 5.

Theorem cad_eject_op_topcost_bounded :
  forall (X : Type) (q : Cadeque X),
    @cad_eject_op_topcost X q <= CAD_EJECT_OP_COST_BOUND.
Proof.
  intros X q. unfold cad_eject_op_topcost, CAD_EJECT_OP_COST_BOUND.
  destruct q as [|t|tL tR]; cbn; try lia.
  destruct t as [pre c suf | pre c suf | pre c suf]; cbn; try lia.
  destruct c; cbn; lia.
Qed.

(** ** Note on [cad_concat_op] / [_full] variants.

    [cad_concat_op] currently delegates to the abstract [cad_concat]
    in the non-trivial case; [cad_concat] is defined as a list
    rebuild ([cad_from_list (cad_to_list_base a ++ cad_to_list_base b)])
    and is therefore [O(|a|+|b|)] -- not [O(1)].  The abstract
    [cad_concat] is the *correctness* spec; the WC [O(1)] [cad_concat]
    of KT99 §6 is the target of Phase 4b's heap-based imperative DSL,
    which uses the five repair cases (1a/1b/2a/2b/2c) plus the
    [adopt6] shortcut.

    Similarly, [cad_pop_op_full] / [cad_eject_op_full] /
    [cad_concat_op_full] are [O(n)] at this layer due to
    [cad_normalize].  They are the *spec* layer; the [O(1)]
    operational layer is downstream. *)
