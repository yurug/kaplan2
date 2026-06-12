(** * KTDeque.Catenable.BufPrims — the buffer-primitive interface.

    The §6 operations (Ops.v) touch buffers through a small set of
    patterns: cons/uncons at the front, inject/eject at the back, size
    tests against constants <= 8, bounded-side appends, and per-element
    folds over (<8)-guarded buffers.  This file NAMES those patterns as
    definitional wrappers over the model's list buffers, so that:

    1. [OpsFast.v] can mirror every operation against the named
       primitives, with [op_f = op] equality lemmas that hold by
       conversion/small case analyses — the keystone and cost theorems
       transfer to the fast ops for free;
    2. extraction ([Extract/ExtractionFast.v]) can remap [buffer] and
       these primitives to an O(1)-both-ends production buffer (the
       proven §4 deque + an O(1) size field) without touching a single
       proof.  The remapping directives are the only trusted seam.

    Cost note: each primitive call is one "buffer primitive" in the
    sense of Cost.v's counters.  [bapp b c] is the splice primitive —
    every Ops.v call site has one CONSTANT-bounded side under [J]
    (audited in Cost.v); the production implementation folds the
    smaller side, hence O(min) = O(1) at every reachable call. *)

From Stdlib Require Import List Arith.
Import ListNotations.
From KTDeque.Common Require Import Prelude.
From KTDeque.Catenable Require Import Model.

Set Implicit Arguments.

Section Prims.
  Variable X : Type.

  Definition bempty : buffer X := [].

  Definition b1 (x : X) : buffer X := [x].

  Definition b2 (x y : X) : buffer X := [x; y].

  Definition b3 (x y z : X) : buffer X := [x; y; z].

  Definition bpush (x : X) (b : buffer X) : buffer X := x :: b.

  Definition binject (b : buffer X) (x : X) : buffer X := b ++ [x].

  Definition bpop (b : buffer X) : option (X * buffer X) :=
    match b with
    | [] => None
    | x :: r => Some (x, r)
    end.

  Definition beject (b : buffer X) : option (buffer X * X) :=
    match rev b with
    | [] => None
    | x :: r => Some (rev r, x)
    end.

  Definition bsize (b : buffer X) : nat := length b.

  Definition bis_empty (b : buffer X) : bool :=
    match b with [] => true | _ => false end.

  Definition bapp (b c : buffer X) : buffer X := b ++ c.

  (** Pop / eject two or three at once (concat's bounded transfers). *)
  Definition bpop2 (b : buffer X) : option (X * X * buffer X) :=
    match b with
    | x :: y :: r => Some (x, y, r)
    | _ => None
    end.

  Definition beject2 (b : buffer X) : option (buffer X * X * X) :=
    match rev b with
    | z :: y :: r => Some (rev r, y, z)
    | _ => None
    end.

  Definition beject3 (b : buffer X) : option (buffer X * X * X * X) :=
    match rev b with
    | c :: bb :: a :: r => Some (rev r, a, bb, c)
    | _ => None
    end.

End Prims.

Arguments bempty {X}.

(** Folds (used only on (<8)-guarded buffers in Ops.v). *)
Definition bfold_right {X Z : Type} (f : X -> Z -> Z) (z : Z) (b : buffer X)
  : Z := fold_right f z b.

Definition bfold_left {X Z : Type} (f : Z -> X -> Z) (b : buffer X) (z : Z)
  : Z := fold_left f b z.
