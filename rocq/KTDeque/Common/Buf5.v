(** * Module: KTDeque.Common.Buf5 -- six-constructor fixed-size buffer.

    ## What it is

    [Buf5 X] is the level-local storage at every chain level: 0..5
    elements of type [X].  Six explicit constructors enumerate the
    sizes:

      [B0]                      0 elements
      [B1 a]                    1 element
      [B2 a b]                  2 elements
      [B3 a b c]                3 elements
      [B4 a b c d]              4 elements
      [B5 a b c d e]            5 elements

    The element type [X] is not the base type [A].  At level 0 of a
    chain, [X = E.t A] holds level-0 elements (one base value each);
    at deeper levels, the deque pairs elements up via [E.pair], so
    [X] still has type [E.t A] but now with elements at higher
    levels.

    ## Why six explicit constructors instead of a length-indexed vector?

    Per ADR-0004 we use plain inductives:
    - The runtime shape is explicit (one tag + fixed fields).
    - Proofs by case analysis are mechanical: [destruct b] gives the
      six cases directly.  See [DequePtr/OpsKTSeq.v]'s "Buffer-level
      sequence preservation" section for the recipe — essentially
      the same six-line proof for every buffer-level lemma.
    - OCaml extraction produces an idiomatic 6-constructor variant
      type with no [Obj.magic].
    - No dependency on [Equations] or [Program].

    ## Colour interpretation

    A buffer's *colour* is determined by its size:
      [B0] / [B5]      Red       (next op underflows or overflows)
      [B1] / [B4]      Yellow    (next op safe in at least one direction)
      [B2] / [B3]      Green     (next op safe in both directions)

    The colour discipline gives the algorithm its WC O(1) bound; see
    [kb/spec/why-bounded-cascade.md] §2.

    Manual §5.2 + Q17.

    Cross-references:
    - [Common/Color.v]                      -- buffer colour from size.
    - [DequePtr/OpsKT.v]                    -- the colour-dispatched ops
                                                that operate on Buf5.
    - [DequePtr/OpsKTSeq.v]                 -- the recurring six-case
                                                proof recipe.
    - [kb/spec/data-model.md] §3.2.
    - [kb/properties/functional.md] P10..P20.
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
