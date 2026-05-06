(** * Module: KTDeque.Common.Color -- Kaplan-Tarjan G/Y/R color tags.

    For *why* these three colors and *why* the regularity invariant
    "no two Reds adjacent" delivers worst-case O(1), read
    [kb/spec/why-bounded-cascade.md] first.  This module is the
    syntactic encoding; that document is the reason it exists.

    Color encoding mirroring Viennot's GADT colors:
      - Green  = "absorbable in both directions" (push or inject without overflow)
      - Yellow = "absorbable in at least one direction"
      - Red    = "overflow or underflow imminent"

    Color of a single buffer is determined by its size:
      - B0, B5      => Red    (empty is "underflow imminent"; full is "overflow imminent")
      - B1, B4      => Yellow
      - B2, B3      => Green

    Color of a packet's outer (= color of a chain link) is the *meet* of
    its prefix and suffix colors with the convention that a single Red
    dominates: Red >> Yellow >> Green.  This mirrors the C's
    [color_from_bufs]:
      - Both pre and suf in {B2, B3}: Green
      - Either pre or suf is B0 or B5: Red
      - Otherwise (at least one of B1, B4): Yellow.

    Cross-references:
    - bench/viennot/color_GYR.ml -- Viennot's GADT color encoding.
    - c/src/ktdeque_dequeptr.c (color_from_bufs) -- C runtime version.
*)

From KTDeque.Common Require Import Prelude Buf5.

(** ** The color type. *)
Inductive color : Type :=
| Green  : color
| Yellow : color
| Red    : color.

(** Equality is decidable. *)
Definition color_eq_dec (c1 c2 : color) : {c1 = c2} + {c1 <> c2}.
Proof. decide equality. Defined.

(** ** Color of a single buffer.  *)
Definition buf_color {X : Type} (b : Buf5 X) : color :=
  match b with
  | B0           => Red
  | B5 _ _ _ _ _ => Red
  | B1 _         => Yellow
  | B4 _ _ _ _   => Yellow
  | B2 _ _       => Green
  | B3 _ _ _     => Green
  end.

(** ** Color meet for combining prefix and suffix.

    Models the C's [color_from_bufs]: Red dominates Yellow dominates Green. *)
Definition color_meet (c1 c2 : color) : color :=
  match c1, c2 with
  | Red, _ | _, Red       => Red
  | Yellow, _ | _, Yellow => Yellow
  | Green, Green          => Green
  end.

Lemma color_meet_comm : forall c1 c2, color_meet c1 c2 = color_meet c2 c1.
Proof. intros c1 c2. destruct c1, c2; reflexivity. Qed.

Lemma color_meet_idem : forall c, color_meet c c = c.
Proof. intros c. destruct c; reflexivity. Qed.

Lemma color_meet_red_l : forall c, color_meet Red c = Red.
Proof. reflexivity. Qed.

Lemma color_meet_red_r : forall c, color_meet c Red = Red.
Proof. intros c. destruct c; reflexivity. Qed.

(** ** Predicates. *)

Definition is_green (c : color) : bool :=
  match c with Green => true | _ => false end.

Definition is_yellow (c : color) : bool :=
  match c with Yellow => true | _ => false end.

Definition is_red (c : color) : bool :=
  match c with Red => true | _ => false end.

(** "noyellow" = green or red — the input domain of Viennot's
    [ensure_green] and the post-condition of [make_yellow]'s tail
    invariant. *)
Definition is_noyellow (c : color) : bool :=
  match c with Yellow => false | _ => true end.

Lemma is_green_iff : forall c, is_green c = true <-> c = Green.
Proof. intros c. destruct c; split; intros; (reflexivity || discriminate || congruence). Qed.

Lemma is_red_iff : forall c, is_red c = true <-> c = Red.
Proof. intros c. destruct c; split; intros; (reflexivity || discriminate || congruence). Qed.

Lemma is_yellow_iff : forall c, is_yellow c = true <-> c = Yellow.
Proof. intros c. destruct c; split; intros; (reflexivity || discriminate || congruence). Qed.

(** ** Helper: characterizing buffer sizes by color. *)

Lemma buf_color_red_iff_b0_or_b5 :
  forall (X : Type) (b : Buf5 X),
    buf_color b = Red <-> (buf5_size b = 0 \/ buf5_size b = 5).
Proof. intros X b. destruct b; cbn; split; intros; intuition (auto with arith); discriminate. Qed.

Lemma buf_color_green_iff_b2_or_b3 :
  forall (X : Type) (b : Buf5 X),
    buf_color b = Green <-> (buf5_size b = 2 \/ buf5_size b = 3).
Proof. intros X b. destruct b; cbn; split; intros; intuition (auto with arith); discriminate. Qed.

Lemma buf_color_yellow_iff_b1_or_b4 :
  forall (X : Type) (b : Buf5 X),
    buf_color b = Yellow <-> (buf5_size b = 1 \/ buf5_size b = 4).
Proof. intros X b. destruct b; cbn; split; intros; intuition (auto with arith); discriminate. Qed.
