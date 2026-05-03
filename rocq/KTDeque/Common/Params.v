(** * Module: KTDeque.Common.Params -- numeric constants used in size / color reasoning.

    Per manual §19 and Q25 default: every literal that appears in size or color
    reasoning lives here as a [Definition].  Arithmetic lemmas reference these
    by name; no bare 5/6/7/8 in [Cadeque6/].

    Cross-references:
    - kb/spec/data-model.md#1.3 -- catalog of constants.
    - kb/properties/non-functional.md#NF9 -- centralization invariant.
    - kb/conventions/code-style.md -- "Constants policy".
*)

From KTDeque.Common Require Import Prelude.

(** ** Section 4 buffer cap -- [Buf5] holds at most this many elements.
    Manual §5.2 (and KT99 §4.1).  Color thresholds in Section 4 derive from this. *)
Definition buf4_cap : nat := 5.

(** ** Section 6 stored triple lower bound.
    Manual §10.5 (ST1, ST2). *)
Definition stored_min : nat := 3.

(** ** Section 6 only-triple lower bound.
    Manual §10.5 (OT1).  Both prefix and suffix must hit this. *)
Definition only_min : nat := 5.

(** ** Section 6 four-color thresholds.
    Manual §10.6 / KT99 §6.1.  Sizes ≥ 5 map as below; smaller sizes are
    forbidden by the size constraints. *)
Definition c6_red       : nat := 5.
Definition c6_orange    : nat := 6.
Definition c6_yellow    : nat := 7.
Definition c6_green_min : nat := 8.

(** Sanity lemma -- the thresholds are strictly increasing. *)
Lemma c6_thresholds_strict :
  c6_red < c6_orange /\ c6_orange < c6_yellow /\ c6_yellow < c6_green_min.
Proof. unfold c6_red, c6_orange, c6_yellow, c6_green_min. lia. Qed.

(** Sanity lemma -- only-triple lower bound matches the red threshold of Section 6. *)
Lemma only_min_eq_red : only_min = c6_red.
Proof. reflexivity. Qed.

(** Sanity lemma -- a stored triple's lower bound is strictly less than the
    only-triple lower bound (so a stored triple fits "inside" a buffer that an
    only-triple would consider undersized).  *)
Lemma stored_min_lt_only_min : stored_min < only_min.
Proof. unfold stored_min, only_min. lia. Qed.

(** ** Hints registered into [ktdeque] for unfold-friendly arithmetic. *)
#[export] Hint Unfold buf4_cap stored_min only_min c6_red c6_orange c6_yellow c6_green_min : ktdeque.
