(** * Module: KTDeque.Common.Symmetry -- [Side] type for left/right-symmetric pairs.

    Per ADR-0006: [Side := Front | Back].  Used in mandatory mirrored pairs
    (push/inject, pop/eject, take_firstN/take_lastN).  Do NOT introduce a
    [Left | Right] alternative; that conflicts with Section-6 triple kinds.

    Cross-references:
    - kb/architecture/decisions/adr-0006-symmetry.md
    - kb/spec/data-model.md#6 -- where Side is referenced.
*)

From KTDeque.Common Require Import Prelude.

Inductive Side : Type :=
| Front : Side
| Back  : Side.

Definition flip_side (s : Side) : Side :=
  match s with
  | Front => Back
  | Back  => Front
  end.

Lemma flip_side_involution : forall s, flip_side (flip_side s) = s.
Proof. destruct s; reflexivity. Qed.

(** [pick] selects between two values based on a [Side].  Useful when an
    operation differs only in which buffer it touches. *)
Definition pick {A : Type} (s : Side) (front back : A) : A :=
  match s with
  | Front => front
  | Back  => back
  end.

Lemma pick_flip : forall (A : Type) (s : Side) (a b : A),
    pick (flip_side s) a b = pick s b a.
Proof. destruct s; reflexivity. Qed.

#[export] Hint Resolve flip_side_involution : ktdeque.
