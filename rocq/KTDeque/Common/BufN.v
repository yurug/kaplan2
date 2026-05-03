(** * Module: KTDeque.Common.BufN -- bounded-length buffer parameterized
      by capacity (a sketch).

    A [BufN n X] is a list of [X]'s with at most [n] elements. The
    intent of this module is to lay the groundwork for *experiments
    with buffer sizes other than 5*. The deque algorithm in
    [DequePtr/OpsKT.v] currently uses [Buf5] (six explicit
    constructors B0..B5); supporting larger buffers via that style
    means [n + 1] proof cases per buffer-shape lemma, which scales
    poorly past size ~7.

    The plan with [BufN] is to make capacity a parameter:

      [BufN 5 X]    = same shape as [Buf5 X]
      [BufN 7 X]    = up to 7 elements, no new code
      [BufN 4096 X] = up to 4096 elements, no new code

    Trade-offs explored in [kb/lessons.md]:

    - **Persistent setting** (extracted OCaml). Each push allocates a
      fresh top buffer of size up to [n]. Per-push cost is
      proportional to [n]; cascade frequency is roughly 1 per [n]
      pushes. Total per-push work is roughly constant in [n], with
      the constant dominated by allocator throughput. Empirically,
      [n = 5..7] is the sweet spot.
    - **Mutable setting** (the C port in [c/], or a Rust impl using
      mutable cells). Per-push cost stays O(1) regardless of [n].
      Larger [n] is unambiguously better, up to L1/L2 cache thresholds.

    ## Status of this module

    This is a *sketch*. The type and basic projections build. The
    operational lemmas ([buf_*_naive_seq], [buf_*_naive_size]) and
    the buffer-level operations ([buf_push_naive] etc.) are deferred:
    naive proofs against the carried [length _ <= n] proof field
    fight Coq's [inversion] tactic because of opaque [lia]-generated
    proof terms. A clean implementation needs either:

    - a [Program]-style definition with explicit obligation proofs, or
    - a switch to [Vector.t] (length-indexed lists) for stronger
      structural typing, or
    - dropping the static proof field and validating length at
      runtime.

    The deque algorithm port (rewriting [green_push], [make_small],
    [green_of_red], etc. in size-based rather than constructor-based
    terms) is a substantial follow-up regardless of which proof
    scaffolding is chosen.

    Cross-references:
    - [Buf5.v] -- the existing six-constructor buffer.
    - [kb/lessons.md] -- the analytical framework for buffer sizing.
*)

From Stdlib Require Import List PeanoNat Lia.
Import ListNotations.

From KTDeque.Common Require Import Prelude.

(** ** The bounded-length buffer. *)

Record BufN (n : nat) (X : Type) : Type := {
  buf_items : list X;
  buf_len_ok : length buf_items <= n
}.

Arguments Build_BufN {n X} _ _.
Arguments buf_items {n X} _.
Arguments buf_len_ok {n X} _.

(** ** Empty buffer. *)
Definition buf_empty {X : Type} (n : nat) : BufN n X :=
  Build_BufN [] (Nat.le_0_l n).

(** ** Size of a buffer. *)
Definition buf_size {n : nat} {X : Type} (b : BufN n X) : nat :=
  length (buf_items b).

(** ** Flatten a buffer to a list. *)
Definition buf_seq {n : nat} {X A : Type} (flat : X -> list A) (b : BufN n X) : list A :=
  flat_map flat (buf_items b).

(** ** Empty / size sanity. *)

Lemma buf_empty_size : forall n X, @buf_size n X (buf_empty n) = 0.
Proof. reflexivity. Qed.

Lemma buf_empty_seq : forall n X A (flat : X -> list A),
    buf_seq flat (buf_empty n) = [].
Proof. reflexivity. Qed.

(** ** Capacity bound holds by construction. *)

Lemma buf_size_bound : forall n X (b : BufN n X), buf_size b <= n.
Proof. intros. exact (buf_len_ok b). Qed.
