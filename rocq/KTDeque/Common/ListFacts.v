(** * Module: KTDeque.Common.ListFacts -- small list lemmas not in stdlib.

    Lemmas that appear here are locally useful and small.  When a lemma is in
    [List] from stdlib already, prefer the stdlib version.

    Cross-references:
    - kb/conventions/proof-style.md -- [seq] hint database.
*)

From KTDeque.Common Require Import Prelude.

(** ** [snoc]: append a singleton at the back, mirroring [cons]. *)
Definition snoc {A : Type} (xs : list A) (x : A) : list A := xs ++ [x].

Lemma snoc_app : forall (A : Type) (xs : list A) (x : A),
    snoc xs x = xs ++ [x].
Proof. reflexivity. Qed.

Lemma length_snoc : forall (A : Type) (xs : list A) (x : A),
    length (snoc xs x) = S (length xs).
Proof.
  intros A xs x. unfold snoc. rewrite length_app. simpl. lia.
Qed.

(** ** [head_opt]: total alternative to [hd] when the empty case is meaningful. *)
Definition head_opt {A : Type} (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: _ => Some x
  end.

(** ** [tail_opt]: drop one from the front, returning [None] on empty. *)
Definition tail_opt {A : Type} (xs : list A) : option (list A) :=
  match xs with
  | [] => None
  | _ :: xs' => Some xs'
  end.

(** ** [last_opt] / [init_opt]: symmetric to head/tail. *)
Definition last_opt {A : Type} (xs : list A) : option A :=
  match rev xs with
  | [] => None
  | x :: _ => Some x
  end.

(** Hints for the [seq] database. *)
#[export] Hint Unfold snoc head_opt tail_opt last_opt : seq.
#[export] Hint Rewrite @app_nil_l @app_nil_r : seq.
