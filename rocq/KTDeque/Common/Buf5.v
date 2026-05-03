(** * Module: KTDeque.Common.Buf5 -- six-constructor fixed-size buffer.

    Manual §5.2 + Q17.  A [Buf5 X] holds 0..5 elements.  We use six explicit
    constructors [B0..B5] rather than a length-indexed vector because:
    - it makes the runtime shape explicit (one tag, fixed fields);
    - proofs by case analysis are mechanical;
    - extraction produces idiomatic OCaml;
    - no [Equations] / [Program] dependency.

    Per ADR-0004 we use plain inductives.  Per the Buffer6 wrapper (§8 / [Buffer6/]),
    a [Buf5 X] is the underlying storage of a Section-4 deque cell prefix or
    suffix.  Its element type is [X], not the base [A] -- in higher levels of
    the deque, [X] becomes a pair (or higher) of base elements (per
    [Common/Prelude]).

    Cross-references:
    - kb/spec/data-model.md#3.2
    - kb/properties/functional.md#P10..P20 (Buffer6 helpers; Buf5 supplies the
      underlying primitive that those helpers are built on).
*)

From KTDeque.Common Require Import Prelude.

(** ** The six-constructor buffer. *)
Inductive Buf5 (X : Type) : Type :=
| B0 :                                 Buf5 X
| B1 : X ->                            Buf5 X
| B2 : X -> X ->                       Buf5 X
| B3 : X -> X -> X ->                  Buf5 X
| B4 : X -> X -> X -> X ->             Buf5 X
| B5 : X -> X -> X -> X -> X ->        Buf5 X.

Arguments B0 {X}.
Arguments B1 {X} _.
Arguments B2 {X} _ _.
Arguments B3 {X} _ _ _.
Arguments B4 {X} _ _ _ _.
Arguments B5 {X} _ _ _ _ _.

(** ** Size of a buffer (constant, by case). *)
Definition buf5_size {X : Type} (b : Buf5 X) : nat :=
  match b with
  | B0           => 0
  | B1 _         => 1
  | B2 _ _       => 2
  | B3 _ _ _     => 3
  | B4 _ _ _ _   => 4
  | B5 _ _ _ _ _ => 5
  end.

(** ** Sequence of a buffer, given a flattening function for its elements.

    For the public Section-4 buffer at level 0, [flat] is just the singleton
    function [fun x => [x]].  At level [l > 0], elements are themselves pairs
    (or higher) and [flat] flattens them.  Manual §3.1 / §5.3. *)
Definition buf5_seq {X A : Type} (flat : X -> list A) (b : Buf5 X) : list A :=
  match b with
  | B0             => []
  | B1 a           => flat a
  | B2 a b         => flat a ++ flat b
  | B3 a b c       => flat a ++ flat b ++ flat c
  | B4 a b c d     => flat a ++ flat b ++ flat c ++ flat d
  | B5 a b c d e   => flat a ++ flat b ++ flat c ++ flat d ++ flat e
  end.

(** ** Color of a buffer (manual §5.4 / KT99 §4).

    Buffer color depends only on size:
    - sizes 0, 5     -> Red3   (full or empty -- bad endpoints)
    - sizes 1, 4     -> Yellow3 (one step from bad)
    - sizes 2, 3     -> Green3 (safe middle)

    We provide both an inductive predicate and a computable function. *)

From KTDeque.RBR Require Import Model.   (* for Color3 *)

Definition buf5_color {X : Type} (b : Buf5 X) : Color3 :=
  match buf5_size b with
  | 0 | 5     => Red3
  | 1 | 4     => Yellow3
  | 2 | 3     => Green3
  | _         => Red3   (* unreachable: buf5_size <= 5 *)
  end.

(** Sanity: buffer size is always at most [buf4_cap]. *)
From KTDeque.Common Require Import Params.

Lemma buf5_size_bound : forall (X : Type) (b : Buf5 X),
    buf5_size b <= buf4_cap.
Proof.
  intros X b. unfold buf4_cap.
  destruct b; cbn; lia.
Qed.

(** ** Length lemma: [buf5_size] equals the length of [buf5_seq] when [flat]
    is the singleton mapping.  *)
Lemma buf5_size_length_singleton :
  forall (X : Type) (b : Buf5 X),
    buf5_size b = length (buf5_seq (fun x : X => [x]) b).
Proof.
  intros X b. destruct b; cbn; reflexivity.
Qed.

(** ** Examples. *)
Example buf5_size_B0 : @buf5_size nat B0 = 0.
Proof. reflexivity. Qed.

Example buf5_size_B3 : buf5_size (B3 1 2 3) = 3.
Proof. reflexivity. Qed.

Example buf5_seq_B3 : buf5_seq (fun x => [x]) (B3 1 2 3) = [1; 2; 3].
Proof. reflexivity. Qed.

Example buf5_color_B0 : @buf5_color nat B0 = Red3.
Proof. reflexivity. Qed.

Example buf5_color_B3 : buf5_color (B3 1 2 3) = Green3.
Proof. reflexivity. Qed.

(** ** Hint registrations. *)
#[export] Hint Resolve buf5_size_bound : ktdeque.
