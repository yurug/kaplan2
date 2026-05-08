(** * Module: KTDeque.Buffer6.SmallMoves -- the small-move primitives
      used by the Section-6 cadeque repair cases.

    First-time reader: read [kb/spec/why-catenable.md] §3 and §4
    before this file, and [Buffer6/SizedBuffer.v] for the [Buf6]
    type definition.

    ## Why this exists

    The Section-6 cadeque repair primitives ([make_small6],
    [green_of_red6], etc., to be defined in [Cadeque6/]) need a
    small toolkit of buffer operations beyond push / pop / inject /
    eject:

    - **`buf6_take_first2`, `buf6_take_first3`**: pop the first 2
      or 3 elements as a tuple.  Used when shifting a small chunk
      of buffer content to a neighbour during repair.
    - **`buf6_take_last2`, `buf6_take_last3`**: mirror at the back.
    - **`buf6_concat`**: concatenate two buffers.  Used when a
      cadeque repair merges two adjacent buffers (e.g. a left
      triple's suffix with a right triple's prefix during a
      Case 2 / Case 3 fix).
    - **`buf6_halve`**: split a buffer into two equal-size halves.
      Used when a buffer grows large enough to be split into two.
    - **`buf6_move_all`**: take all of one buffer's elements and
      add them to the front (or back) of another.  Used when one
      buffer is small enough to absorb into a neighbour.

    All operations are list manipulations under the abstract spec.
    Their *cost* in the operational realization (where [Buf6] is
    backed by a Section-4 deque) is what the Section-6 cost proof
    in [Cadeque6/Footprint.v] will establish.

    ## Cross-references

    - [Buffer6/SizedBuffer.v]   -- the [Buf6] type and basic ops.
    - [kb/spec/why-catenable.md] §4 -- where these operations come
                                       from in the cadeque repair
                                       cases.
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.

(** ** Take the first / last 2 or 3 elements.

    These are partial: [buf6_take_first2] requires the buffer to
    have ≥ 2 elements.  We return [option] for the partial cases
    so callers can pattern-match. *)

Definition buf6_take_first2 {X : Type} (b : Buf6 X)
  : option (X * X * Buf6 X) :=
  match buf6_elems b with
  | x1 :: x2 :: rest => Some (x1, x2, mkBuf6 rest)
  | _                => None
  end.

Definition buf6_take_first3 {X : Type} (b : Buf6 X)
  : option (X * X * X * Buf6 X) :=
  match buf6_elems b with
  | x1 :: x2 :: x3 :: rest => Some (x1, x2, x3, mkBuf6 rest)
  | _                      => None
  end.

Definition buf6_take_last2 {X : Type} (b : Buf6 X)
  : option (Buf6 X * X * X) :=
  match rev (buf6_elems b) with
  | x2 :: x1 :: rest => Some (mkBuf6 (rev rest), x1, x2)
  | _                => None
  end.

Definition buf6_take_last3 {X : Type} (b : Buf6 X)
  : option (Buf6 X * X * X * X) :=
  match rev (buf6_elems b) with
  | x3 :: x2 :: x1 :: rest => Some (mkBuf6 (rev rest), x1, x2, x3)
  | _                      => None
  end.

(** ** Concatenation.

    [buf6_concat a b] joins [a] and [b] into a single buffer.  At
    the abstract level this is just [list] concatenation; the
    operational cost is what the Section-6 work bound depends on. *)

Definition buf6_concat {X : Type} (a b : Buf6 X) : Buf6 X :=
  mkBuf6 (buf6_elems a ++ buf6_elems b).

(** ** Move-all.

    [buf6_move_all_front src dst] takes all of [src]'s elements and
    prepends them to [dst].  Equivalent to [buf6_concat src dst].
    [buf6_move_all_back src dst] appends them.

    Used in cadeque repair cases where one buffer is small enough
    to absorb into its neighbour without restructuring. *)

Definition buf6_move_all_front {X : Type} (src dst : Buf6 X) : Buf6 X :=
  buf6_concat src dst.

Definition buf6_move_all_back {X : Type} (src dst : Buf6 X) : Buf6 X :=
  buf6_concat dst src.

(** ** Halve: split a buffer into two halves of (almost) equal size.

    For a buffer of size [n], [buf6_halve b = (left, right)] where
    [size left = n / 2] and [size right = n - n / 2].  Used in the
    Section-6 [make_small6] primitive when a buffer grows large
    enough to be split. *)

Definition buf6_halve {X : Type} (b : Buf6 X) : Buf6 X * Buf6 X :=
  let n := length (buf6_elems b) in
  let half := Nat.div n 2 in
  (mkBuf6 (firstn half (buf6_elems b)),
   mkBuf6 (skipn  half (buf6_elems b))).

(** ** Sequence laws.

    Every operation has a list-level meaning that is now proved
    against [buf6_to_list]. *)

(** [buf6_take_first2]: when [b] has at least 2 elements, taking the
    first 2 produces a buffer whose [to_list] equals the rest, and
    the original [to_list] is the two taken values prepended. *)
Lemma buf6_take_first2_seq :
  forall (X : Type) (b : Buf6 X) (x1 x2 : X) (b' : Buf6 X),
    buf6_take_first2 b = Some (x1, x2, b') ->
    buf6_to_list b = x1 :: x2 :: buf6_to_list b'.
Proof.
  intros X [xs] x1 x2 [b'] Heq.
  unfold buf6_take_first2, buf6_elems, buf6_to_list in *.
  destruct xs as [|y1 [|y2 ys]]; try discriminate.
  inversion Heq; subst. reflexivity.
Qed.

Lemma buf6_take_first3_seq :
  forall (X : Type) (b : Buf6 X) (x1 x2 x3 : X) (b' : Buf6 X),
    buf6_take_first3 b = Some (x1, x2, x3, b') ->
    buf6_to_list b = x1 :: x2 :: x3 :: buf6_to_list b'.
Proof.
  intros X [xs] x1 x2 x3 [b'] Heq.
  unfold buf6_take_first3, buf6_elems, buf6_to_list in *.
  destruct xs as [|y1 [|y2 [|y3 ys]]]; try discriminate.
  inversion Heq; subst. reflexivity.
Qed.

Lemma buf6_take_last2_seq :
  forall (X : Type) (b : Buf6 X) (b' : Buf6 X) (x1 x2 : X),
    buf6_take_last2 b = Some (b', x1, x2) ->
    buf6_to_list b = buf6_to_list b' ++ [x1; x2].
Proof.
  intros X [xs] [b'] x1 x2 Heq.
  unfold buf6_take_last2, buf6_elems, buf6_to_list in *.
  destruct (rev xs) as [|y2 [|y1 rest]] eqn:Hrev; try discriminate.
  inversion Heq; subst.
  apply (f_equal (@rev X)) in Hrev. rewrite rev_involutive in Hrev.
  cbn in Hrev. rewrite Hrev.
  rewrite <- app_assoc. cbn. reflexivity.
Qed.

Lemma buf6_take_last3_seq :
  forall (X : Type) (b : Buf6 X) (b' : Buf6 X) (x1 x2 x3 : X),
    buf6_take_last3 b = Some (b', x1, x2, x3) ->
    buf6_to_list b = buf6_to_list b' ++ [x1; x2; x3].
Proof.
  intros X [xs] [b'] x1 x2 x3 Heq.
  unfold buf6_take_last3, buf6_elems, buf6_to_list in *.
  destruct (rev xs) as [|y3 [|y2 [|y1 rest]]] eqn:Hrev; try discriminate.
  inversion Heq; subst.
  apply (f_equal (@rev X)) in Hrev. rewrite rev_involutive in Hrev.
  cbn in Hrev. rewrite Hrev.
  rewrite <- !app_assoc. cbn. reflexivity.
Qed.

Lemma buf6_concat_seq :
  forall (X : Type) (a b : Buf6 X),
    buf6_to_list (buf6_concat a b) = buf6_to_list a ++ buf6_to_list b.
Proof.
  intros X [xs] [ys]. unfold buf6_concat, buf6_to_list, buf6_elems.
  reflexivity.
Qed.

Lemma buf6_concat_size :
  forall (X : Type) (a b : Buf6 X),
    buf6_size (buf6_concat a b) = buf6_size a + buf6_size b.
Proof.
  intros X [xs] [ys]. unfold buf6_size, buf6_concat, buf6_elems.
  rewrite length_app. reflexivity.
Qed.

Lemma buf6_move_all_front_seq :
  forall (X : Type) (src dst : Buf6 X),
    buf6_to_list (buf6_move_all_front src dst)
    = buf6_to_list src ++ buf6_to_list dst.
Proof. intros. apply buf6_concat_seq. Qed.

Lemma buf6_move_all_back_seq :
  forall (X : Type) (src dst : Buf6 X),
    buf6_to_list (buf6_move_all_back src dst)
    = buf6_to_list dst ++ buf6_to_list src.
Proof. intros. apply buf6_concat_seq. Qed.

(** [buf6_halve]: the two halves concat back to the original.
    The [let '(l, r) := ... in ...] pattern is OCaml-style; in Rocq
    we use distinct identifiers (not [left]/[right] which clash with
    [sumbool] constructors). *)
Lemma buf6_halve_seq :
  forall (X : Type) (b : Buf6 X),
    let '(lo, hi) := buf6_halve b in
    buf6_to_list b = buf6_to_list lo ++ buf6_to_list hi.
Proof.
  intros X [xs]. unfold buf6_halve, buf6_to_list, buf6_elems. cbn.
  apply eq_sym, firstn_skipn.
Qed.

Lemma buf6_halve_size :
  forall (X : Type) (b : Buf6 X),
    let '(lo, hi) := buf6_halve b in
    buf6_size lo + buf6_size hi = buf6_size b.
Proof.
  intros X [xs].
  (* Halve preserves length.  Bypass [Nat.div]'s [divmod]-based
     unfolding by deriving the size law from the seq law: take
     [length] of both sides of [firstn_skipn k xs ++ skipn k xs = xs]
     for the specific [k = length xs / 2] (the value [buf6_halve]
     uses, but we don't need to inspect it). *)
  pose proof (firstn_skipn (Nat.div (length xs) 2) xs) as Hxs.
  apply (f_equal (@length X)) in Hxs.
  rewrite length_app in Hxs.
  unfold buf6_halve, buf6_size, buf6_elems. exact Hxs.
Qed.

(** ** Examples. *)

Example buf6_take_first2_ok :
  buf6_take_first2 (mkBuf6 [1; 2; 3; 4 : nat])
  = Some (1, 2, mkBuf6 [3; 4]).
Proof. reflexivity. Qed.

Example buf6_take_first2_too_small :
  buf6_take_first2 (mkBuf6 [1 : nat]) = None.
Proof. reflexivity. Qed.

Example buf6_concat_ex :
  buf6_to_list (buf6_concat (mkBuf6 [1; 2 : nat]) (mkBuf6 [3; 4]))
  = [1; 2; 3; 4].
Proof. reflexivity. Qed.

Example buf6_halve_ex :
  buf6_halve (mkBuf6 [1; 2; 3; 4 : nat])
  = (mkBuf6 [1; 2], mkBuf6 [3; 4]).
Proof. reflexivity. Qed.

Example buf6_halve_odd :
  buf6_halve (mkBuf6 [1; 2; 3; 4; 5 : nat])
  = (mkBuf6 [1; 2], mkBuf6 [3; 4; 5]).
Proof. reflexivity. Qed.
