(** * Module: KTDeque.DequePtr.OpsKT --
    Worst-case O(1) deque operations on [KChain].

    This module mechanizes the Viennot-Wendling-Guéneau-Pottier
    presentation of the Kaplan-Tarjan persistent real-time deque (PLDI
    2024). The overall algorithm — color-dispatched buffer helpers,
    [make_small] (9-case rebalance), [green_of_red] (3-case red→green
    fix), [ensure_green], and the four color-dispatched
    [push] / [pop] / [inject] / [eject] — is taken directly from
    Viennot's reference OCaml [bench/viennot/deque_core.ml].

    The KT99 invariant we maintain is "no two reds in a row, and a
    Red's tail must be Green or [KEnding]".  The non-recursive top-level
    operations use [ensure_green] to fix at most one Red per call,
    which is what makes each operation worst-case O(1).

    ## What is taken from Viennot

    - The buffer helpers [green_push], [green_inject], [yellow_push],
      [yellow_inject], [green_pop], [green_eject], [yellow_pop],
      [yellow_eject].
    - The decomposition helpers [prefix_decompose], [suffix_decompose],
      [buffer_unsandwich], [buffer_halve], [prefix_rot], [suffix_rot].
    - The concat helpers [green_prefix_concat], [green_suffix_concat],
      [prefix_concat], [suffix_concat] (with the level-equality
      witnesses at [E.pair] sites).
    - The shape of [make_small], [green_of_red] (Cases 1/2/3),
      [ensure_green], [make_yellow_k], [make_red_k], and [push_kt2] etc.

    ## What is novel

    Three design choices distinguish this development from a literal
    Rocq port of Viennot's GADT-typed presentation.

    ### 1. Explicit-color [KChain], not a GADT.

    Viennot's chain is type-indexed by color:

    {v
        chain α β where β ∈ {green, yellow, red, …}
    v}

    so the type system enforces the colored regularity invariant. Rocq
    can express that as a GADT, but mechanizing makes the proofs
    awkward (positivity workarounds, dependent matches everywhere).
    Our [KChain] is a plain inductive carrying an explicit [color] tag
    on each link:

    {v
        Inductive KChain A :=
        | KEnding : Buf5 (E.t A) -> KChain A
        | KCons   : color -> Packet A -> KChain A -> KChain A.
    v}

    Regularity is then a separate [Prop]-level invariant
    ([regular_kt] in [OpsKTRegular.v]). This is the standard *extrinsic*
    encoding: the data structure carries enough information at the
    value level to recover the colored shape without typing tricks.

    Note that the colour tag is *not* derivable from buffer sizes alone:
    after a [green_of_red] Case 3, the freshly-tagged Red packet may
    happen to have green-ish-sized buffers, so the tag is *contextual*.
    The explicit tag is what lets [ensure_green] dispatch correctly at
    the next operation.

    ### 2. Three execution variants ([kt2], [kt3], [kt4]).

    The same algorithm appears three times in this file:

    - [push_kt2] / [inject_kt2] / [pop_kt2] / [eject_kt2]: a clean,
      almost-literal translation of Viennot. Used as the *proof target*
      in [OpsKTSeq.v]. Returns [option (KChain A)].
    - [push_kt3] / etc.: inlines [yellow_wrap] (= [make_yellow_k] with
      the non-Red fast path special-cased) and short-circuits Yellow
      buffer transitions that don't need to fire [green_of_red_k].
      Same return type as [kt2].
    - [push_kt4] / etc.: same algorithm as [kt3] but uses dedicated
      result types ([push_result] = [PushFail | PushOk c'], [pop_result]
      = [PopFail | PopOk x c']) instead of [option (E.t A * KChain A)].

    The motivation is purely about extracted-OCaml allocation cost.
    The naïve [option (X * Y)] return extracts to a nested allocation:
    [Some] wraps a tuple block. By using a flat 2-constructor sum, we
    save one allocation per successful op, which the bench's hot loop
    is allocation-bound on. [kt4] is the production target;
    [kt2] is the proof target; [kt3] is the middle ground.

    ### 3. The [E.t] element abstraction.

    Pair-trees ([(1,2)], [((1,2),(3,4))], …) appear at every chain
    level: the buffer at depth [k] holds elements of "level [k]" type,
    which is a perfectly balanced binary tree of [2^k] base elements.

    Viennot uses a dependently typed [t α β] where [β] tracks the
    level. We hide this behind a [Module Type ELEMENT]
    ([Common/Element.v]) with the canonical instance [ElementTree]
    (= [{ l : nat & xpow A l }]). Operations refer to the abstract
    [E.t A], [E.pair], [E.unpair], [E.to_list]; the concrete
    representation is hidden.

    This abstraction is what makes future representation changes
    cheap: a different [ELEMENT] instance does not touch [OpsKT.v] at
    all.

    ## Small pair-tree optimization: [ElementFlat]

    The [ElementTree] instance represents level-[k] elements as nested
    pairs in a perfectly balanced binary tree:

    {v
        ((a, b), (c, d))           -- level 2 = a 2-deep nested pair
        (((a, b), (c, d)), …)      -- level 3 = a 3-deep nested pair
        …
    v}

    Each level adds one pair allocation in the extracted OCaml. For
    workloads that operate at small levels (which is the *typical*
    case — a 1M-element deque only reaches level ≈ 20, but most of
    the working set sits at levels 0-3), this is a measurable
    overhead.

    [Common/Element.v] also provides [ElementFlat], an alternative
    [ELEMENT] instance that uses multi-arity constructors at small
    levels:

    {v
        level 0:  XF0 a                  -- 1 block of size 1
        level 1:  XF1 a b                -- 1 block of size 2
        level 2:  XF2 a b c d            -- 1 block of size 4 (NOT nested)
        level 3+: XFP x y                -- 1 block of size 2 (recursive)
    v}

    Because the deque code is parameterized over the [ELEMENT] module
    type, swapping [ElementTree] for [ElementFlat] in
    [DequePtr/Model.v] does not require touching [OpsKT.v],
    [OpsKTSeq.v], or [OpsKTRegular.v]. The sequence-preservation
    theorems are stated abstractly over [E] and carry through
    unchanged.

    A/B benchmark on the [ocaml/bench/crossover] harness shows the
    optimization is **not** a clear win: it speeds up [inject] by
    15-33% on small/mid sizes but slows [eject] by 15-25% on the same
    sizes; [push] / [pop] / adversarial workloads are unchanged. The
    pair-time savings (one block of size 4 instead of three blocks for
    a level-2 element) are eaten back at unpair-time, where
    [unpair (XF1 a b) = Some (XF0 a, XF0 b)] allocates two new
    wrapper blocks that the existential-based [ElementTree] avoids
    (it returns the projected components inside fresh [ExistT]
    wrappers, the same allocation count, but the OCaml compiler
    optimizes the existential pattern more aggressively).

    [ElementFlat] is therefore retained as a documented alternative
    in [Common/Element.v] but [Model.E := ElementTree] in production.
    A future variant that flattens *only* in one direction (e.g.,
    paired-arity constructors at small levels with an unpair that
    re-uses children rather than re-wrapping) might salvage the win.

    See [kb/lessons.md] for the general principle ("the abstraction
    is what makes representation changes cheap" — and the corollary
    that "cheap to try" does not guarantee "cheap to win").

    ## Cross-references

    - [bench/viennot/deque_core.ml] — the reference being mirrored.
    - [c/ktdeque_dequeptr.c] — the hand-translated C version.
    - [KTDeque.Common.Color] — color types.
    - [KTDeque.Common.Element] — the [ELEMENT] interface and its
      canonical [ElementTree] instance.
    - [KTDeque.DequePtr.OpsKTSeq] — sequence preservation proofs for
      all twelve variants ([kt2] / [kt3] / [kt4] × four operations).
    - [KTDeque.DequePtr.OpsKTRegular] — the regularity invariant.
    - [KTDeque.DequePtr.OpsAbstract] — earlier one-step ops on the
      uncolored [Chain]; kept as building blocks.
*)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Common Require Import Prelude Element Buf5 Buf5Ops Color.
From KTDeque.DequePtr Require Import Model.

(** Reuse [Model.E] (= [ElementTree]) instead of declaring a fresh alias so
    [pair_one] etc. unify with [Model.E.to_list_pair] in [OpsKTSeq.v]
    proofs. *)
Module E := Model.E.

(* ========================================================================== *)
(* Buffer-level helpers (Viennot deque_core.ml lines 60-185).                  *)
(* ========================================================================== *)

(** [green_push x b]: push onto a *green* buffer (B2 or B3). Returns
    [None] for off-domain inputs.  The result is a *yellow* buffer
    (size 3 or 4). *)
Definition green_push {X : Type} (x : X) (b : Buf5 X) : option (Buf5 X) :=
  match b with
  | B2 a b1     => Some (B3 x a b1)
  | B3 a b1 c   => Some (B4 x a b1 c)
  | _           => None
  end.

Definition green_inject {X : Type} (b : Buf5 X) (x : X) : option (Buf5 X) :=
  match b with
  | B2 a b1     => Some (B3 a b1 x)
  | B3 a b1 c   => Some (B4 a b1 c x)
  | _           => None
  end.

(** [yellow_push x b]: push onto a *yellow* buffer (B1 .. B4). Result is
    *red* (B2 .. B5). *)
Definition yellow_push {X : Type} (x : X) (b : Buf5 X) : option (Buf5 X) :=
  match b with
  | B1 a            => Some (B2 x a)
  | B2 a b1         => Some (B3 x a b1)
  | B3 a b1 c       => Some (B4 x a b1 c)
  | B4 a b1 c d     => Some (B5 x a b1 c d)
  | _               => None
  end.

Definition yellow_inject {X : Type} (b : Buf5 X) (x : X) : option (Buf5 X) :=
  match b with
  | B1 a            => Some (B2 a x)
  | B2 a b1         => Some (B3 a b1 x)
  | B3 a b1 c       => Some (B4 a b1 c x)
  | B4 a b1 c d     => Some (B5 a b1 c d x)
  | _               => None
  end.

(** Pops/ejects from non-empty buffers.  Result is "less-than-input"
    color: green→yellow (size 2/3 → 1/2), yellow→red (size 1/4 → 0/3). *)

Definition green_pop {X : Type} (b : Buf5 X) : option (X * Buf5 X) :=
  match b with
  | B2 a b1     => Some (a, B1 b1)
  | B3 a b1 c   => Some (a, B2 b1 c)
  | _           => None
  end.

Definition green_eject {X : Type} (b : Buf5 X) : option (Buf5 X * X) :=
  match b with
  | B2 a b1     => Some (B1 a, b1)
  | B3 a b1 c   => Some (B2 a b1, c)
  | _           => None
  end.

Definition yellow_pop {X : Type} (b : Buf5 X) : option (X * Buf5 X) :=
  match b with
  | B1 a            => Some (a, B0)
  | B2 a b1         => Some (a, B1 b1)
  | B3 a b1 c       => Some (a, B2 b1 c)
  | B4 a b1 c d     => Some (a, B3 b1 c d)
  | _               => None
  end.

Definition yellow_eject {X : Type} (b : Buf5 X) : option (Buf5 X * X) :=
  match b with
  | B1 a            => Some (B0, a)
  | B2 a b1         => Some (B1 a, b1)
  | B3 a b1 c       => Some (B2 a b1, c)
  | B4 a b1 c d     => Some (B3 a b1 c, d)
  | _               => None
  end.

(** [prefix23 opt p] / [suffix23 p opt]: merge an option element with a pair
    to form a green buffer (size 2 or 3). *)
Definition prefix23 {X : Type} (opt : option X) (p : X * X) : Buf5 X :=
  let '(b, c) := p in
  match opt with
  | None   => B2 b c
  | Some a => B3 a b c
  end.

Definition suffix23 {X : Type} (p : X * X) (opt : option X) : Buf5 X :=
  let '(a, b) := p in
  match opt with
  | None   => B2 a b
  | Some c => B3 a b c
  end.

(** [suffix12 x opt]: yellow buffer (size 1 or 2). *)
Definition suffix12 {X : Type} (x : X) (opt : option X) : Buf5 X :=
  match opt with
  | None   => B1 x
  | Some y => B2 x y
  end.

(** ** Buffer decomposition (Viennot lines 202-234).

    Three modes for a buffer:
    - Underflow: 0 or 1 elements (the optional one).
    - Ok: 2 or 3 elements (already green).
    - Overflow_pre b' p: prefix overflow — green prefix b' plus a
      "removed-from-end" pair p.
    - Overflow_suf b' p: suffix overflow — green suffix b' plus a
      "removed-from-start" pair p. *)

Inductive bdecomp_pre (X : Type) : Type :=
| BD_pre_underflow : option X -> bdecomp_pre X
| BD_pre_ok        : Buf5 X -> bdecomp_pre X
| BD_pre_overflow  : Buf5 X -> X -> X -> bdecomp_pre X.
Arguments BD_pre_underflow {X} _.
Arguments BD_pre_ok        {X} _.
Arguments BD_pre_overflow  {X} _ _ _.

Inductive bdecomp_suf (X : Type) : Type :=
| BD_suf_underflow : option X -> bdecomp_suf X
| BD_suf_ok        : Buf5 X -> bdecomp_suf X
| BD_suf_overflow  : Buf5 X -> X -> X -> bdecomp_suf X.
Arguments BD_suf_underflow {X} _.
Arguments BD_suf_ok        {X} _.
Arguments BD_suf_overflow  {X} _ _ _.

Definition prefix_decompose {X : Type} (b : Buf5 X) : bdecomp_pre X :=
  match b with
  | B0           => BD_pre_underflow None
  | B1 x         => BD_pre_underflow (Some x)
  | B2 _ _       => BD_pre_ok b
  | B3 _ _ _     => BD_pre_ok b
  | B4 a b1 c d  => BD_pre_overflow (B2 a b1) c d
  | B5 a b1 c d e => BD_pre_overflow (B3 a b1 c) d e
  end.

Definition suffix_decompose {X : Type} (b : Buf5 X) : bdecomp_suf X :=
  match b with
  | B0           => BD_suf_underflow None
  | B1 x         => BD_suf_underflow (Some x)
  | B2 _ _       => BD_suf_ok b
  | B3 _ _ _     => BD_suf_ok b
  | B4 a b1 c d  => BD_suf_overflow (B2 c d) a b1
  | B5 a b1 c d e => BD_suf_overflow (B3 c d e) a b1
  end.

(** [buffer_unsandwich b]: if [b] has size ≥ 2, peel off first and last;
    return Some(first, middle, last) where middle has size [|b|-2]. *)

Inductive bsandwich (X : Type) : Type :=
| BS_alone    : option X -> bsandwich X
| BS_sandwich : X -> Buf5 X -> X -> bsandwich X.
Arguments BS_alone    {X} _.
Arguments BS_sandwich {X} _ _ _.

Definition buffer_unsandwich {X : Type} (b : Buf5 X) : bsandwich X :=
  match b with
  | B0              => BS_alone None
  | B1 a            => BS_alone (Some a)
  | B2 a b1         => BS_sandwich a B0 b1
  | B3 a b1 c       => BS_sandwich a (B1 b1) c
  | B4 a b1 c d     => BS_sandwich a (B2 b1 c) d
  | B5 a b1 c d e   => BS_sandwich a (B3 b1 c d) e
  end.

(** [prefix_rot x b]: push x onto front of b, then eject the last; size
    preserved. *)
Definition prefix_rot {X : Type} (x : X) (b : Buf5 X) : Buf5 X * X :=
  match b with
  | B0              => (B0, x)
  | B1 a            => (B1 x, a)
  | B2 a b1         => (B2 x a, b1)
  | B3 a b1 c       => (B3 x a b1, c)
  | B4 a b1 c d     => (B4 x a b1 c, d)
  | B5 a b1 c d e   => (B5 x a b1 c d, e)
  end.

(** [suffix_rot b x]: inject x onto back of b, then pop the first;
    size preserved. *)
Definition suffix_rot {X : Type} (b : Buf5 X) (x : X) : X * Buf5 X :=
  match b with
  | B0              => (x, B0)
  | B1 a            => (a, B1 x)
  | B2 a b1         => (a, B2 b1 x)
  | B3 a b1 c       => (a, B3 b1 c x)
  | B4 a b1 c d     => (a, B4 b1 c d x)
  | B5 a b1 c d e   => (a, B5 b1 c d e x)
  end.

(** [buffer_halve b]: convert buffer to buffer-of-pairs; if odd size,
    the first element is returned as an option. *)
Definition buffer_halve {X : Type} (b : Buf5 X) : option X * Buf5 (X * X) :=
  match b with
  | B0              => (None, B0)
  | B1 a            => (Some a, B0)
  | B2 a b1         => (None, B1 (a, b1))
  | B3 a b1 c       => (Some a, B1 (b1, c))
  | B4 a b1 c d     => (None, B2 (a, b1) (c, d))
  | B5 a b1 c d e   => (Some a, B2 (b1, c) (d, e))
  end.

(* ========================================================================== *)
(* Cross-buffer concat helpers (Viennot lines 275-340).                        *)
(*                                                                            *)
(* In our [E.t A]-extrinsic encoding, b1/b2 are both [Buf5 (E.t A)] but their  *)
(* element levels differ: b1's elements are at level k, b2's at level k+1.    *)
(* "Push a pair (c, d) onto b2" means: pair via [E.pair] with a level-eq      *)
(* witness, then push the resulting [E.t A].  "Pop a pair from b2" means:     *)
(* pop one element [E.t A] and [E.unpair] it.                                 *)
(*                                                                            *)
(* All return [option] to handle level-eq mismatches (which never occur under *)
(* well-formed [packet_levels] / [chain_levels] invariants).                  *)
(* ========================================================================== *)

Definition green_prefix_concat {A : Type}
    (b1 : Buf5 (E.t A)) (b2 : Buf5 (E.t A))
    : option (Buf5 (E.t A) * Buf5 (E.t A)) :=
  match prefix_decompose b1 with
  | BD_pre_underflow opt =>
      match green_pop b2 with
      | Some (ab, b2') =>
          match E.unpair A ab with
          | Some (a, b) => Some (prefix23 opt (a, b), b2')
          | None        => None
          end
      | None => None
      end
  | BD_pre_ok b1' => Some (b1', b2)
  | BD_pre_overflow b1' c d =>
      match Nat.eq_dec (E.level A c) (E.level A d) with
      | left eq =>
          match green_push (E.pair A c d eq) b2 with
          | Some b2' => Some (b1', b2')
          | None     => None
          end
      | right _ => None
      end
  end.

Definition green_suffix_concat {A : Type}
    (b1 : Buf5 (E.t A)) (b2 : Buf5 (E.t A))
    : option (Buf5 (E.t A) * Buf5 (E.t A)) :=
  match suffix_decompose b2 with
  | BD_suf_underflow opt =>
      match green_eject b1 with
      | Some (b1', ab) =>
          match E.unpair A ab with
          | Some (a, b) => Some (b1', suffix23 (a, b) opt)
          | None        => None
          end
      | None => None
      end
  | BD_suf_ok b2' => Some (b1, b2')
  | BD_suf_overflow b2' a b =>
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          match green_inject b1 (E.pair A a b eq) with
          | Some b1' => Some (b1', b2')
          | None     => None
          end
      | right _ => None
      end
  end.

Definition prefix_concat {A : Type}
    (b1 : Buf5 (E.t A)) (b2 : Buf5 (E.t A))
    : option (Buf5 (E.t A) * Buf5 (E.t A)) :=
  match prefix_decompose b1 with
  | BD_pre_underflow opt =>
      match yellow_pop b2 with
      | Some (ab, b2') =>
          match E.unpair A ab with
          | Some (a, b) => Some (prefix23 opt (a, b), b2')
          | None        => None
          end
      | None => None
      end
  | BD_pre_ok b1' => Some (b1', b2)
  | BD_pre_overflow b1' c d =>
      match Nat.eq_dec (E.level A c) (E.level A d) with
      | left eq =>
          match yellow_push (E.pair A c d eq) b2 with
          | Some b2' => Some (b1', b2')
          | None     => None
          end
      | right _ => None
      end
  end.

Definition suffix_concat {A : Type}
    (b1 : Buf5 (E.t A)) (b2 : Buf5 (E.t A))
    : option (Buf5 (E.t A) * Buf5 (E.t A)) :=
  match suffix_decompose b2 with
  | BD_suf_underflow opt =>
      match yellow_eject b1 with
      | Some (b1', ab) =>
          match E.unpair A ab with
          | Some (a, b) => Some (b1', suffix23 (a, b) opt)
          | None        => None
          end
      | None => None
      end
  | BD_suf_ok b2' => Some (b1, b2')
  | BD_suf_overflow b2' a b =>
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          match yellow_inject b1 (E.pair A a b eq) with
          | Some b1' => Some (b1', b2')
          | None     => None
          end
      | right _ => None
      end
  end.

(* ========================================================================== *)
(* make_small (Viennot lines 345-421): collapse a depth-1 red chain to a      *)
(* depth-≤1 green chain by rebalancing across the three buffers.              *)
(*                                                                            *)
(* Inputs:                                                                    *)
(*   b1 : outer prefix (E.t A elements at level k)                            *)
(*   b2 : inner buffer (E.t A elements at level k+1, i.e. paired)             *)
(*   b3 : outer suffix (E.t A elements at level k)                            *)
(* Output: a green-headed Chain A.                                            *)
(*                                                                            *)
(* 9 cases by (prefix_decompose b1) × (suffix_decompose b3).  Each case is a  *)
(* faithful translation of Viennot's match arm.                               *)
(* ========================================================================== *)

(** [buffer_push_chain x b]: like [buf5_push_naive] but returns a Chain
    that handles the B5 split.  Mirrors Viennot's [buffer_push]. *)
Definition buffer_push_chain {A : Type} (x : E.t A) (b : Buf5 (E.t A)) : Chain A :=
  match b with
  | B0           => Ending (B1 x)
  | B1 a         => Ending (B2 x a)
  | B2 a b1      => Ending (B3 x a b1)
  | B3 a b1 c    => Ending (B4 x a b1 c)
  | B4 a b1 c d  => Ending (B5 x a b1 c d)
  | B5 a b1 c d e =>
      ChainCons (PNode (B3 x a b1) Hole (B3 c d e)) (Ending B0)
  end.

Definition buffer_inject_chain {A : Type} (b : Buf5 (E.t A)) (x : E.t A) : Chain A :=
  match b with
  | B0           => Ending (B1 x)
  | B1 a         => Ending (B2 a x)
  | B2 a b1      => Ending (B3 a b1 x)
  | B3 a b1 c    => Ending (B4 a b1 c x)
  | B4 a b1 c d  => Ending (B5 a b1 c d x)
  | B5 a b1 c d e =>
      ChainCons (PNode (B3 a b1 c) Hole (B3 d e x)) (Ending B0)
  end.

(** Helper used inside make_small (Underflow, Underflow + Sandwich): merge an
    outer prefix [opt] with paired pair [ab] (each element [a, b] is at level
    k) into a green Buf5 of size 2 or 3. *)

(** Case-merger: produce Ending B0..B4 from optional outer p1, optional inner
    pair (already unpaired), optional outer s1.  Used in (Underflow, Underflow)
    + Alone case of make_small. *)
(** [pair_each_buf b]: given a [Buf5 (E.t A * E.t A)] (each element is an
    OCaml pair of two level-k+1 elements), pair them via [E.pair] to yield a
    [Buf5 (E.t A)] of level-k+2 elements.  Returns [None] on level mismatch. *)
Definition pair_one {A : Type} (p : E.t A * E.t A) : option (E.t A) :=
  let '(x, y) := p in
  match Nat.eq_dec (E.level A x) (E.level A y) with
  | left eq => Some (E.pair A x y eq)
  | right _ => None
  end.

Definition pair_each_buf {A : Type} (b : Buf5 (E.t A * E.t A))
    : option (Buf5 (E.t A)) :=
  match b with
  | B0 => Some B0
  | B1 p =>
      match pair_one p with
      | Some xp => Some (B1 xp)
      | None    => None
      end
  | B2 p1 p2 =>
      match pair_one p1, pair_one p2 with
      | Some x1, Some x2 => Some (B2 x1 x2)
      | _, _ => None
      end
  | B3 p1 p2 p3 =>
      match pair_one p1, pair_one p2, pair_one p3 with
      | Some x1, Some x2, Some x3 => Some (B3 x1 x2 x3)
      | _, _, _ => None
      end
  | B4 p1 p2 p3 p4 =>
      match pair_one p1, pair_one p2, pair_one p3, pair_one p4 with
      | Some x1, Some x2, Some x3, Some x4 => Some (B4 x1 x2 x3 x4)
      | _, _, _, _ => None
      end
  | B5 p1 p2 p3 p4 p5 =>
      match pair_one p1, pair_one p2, pair_one p3, pair_one p4, pair_one p5 with
      | Some x1, Some x2, Some x3, Some x4, Some x5 => Some (B5 x1 x2 x3 x4 x5)
      | _, _, _, _, _ => None
      end
  end.

Definition mk_ending_from_options {A : Type}
    (p1 : option (E.t A)) (mid : option (E.t A * E.t A)) (s1 : option (E.t A))
    : Chain A :=
  match p1, mid, s1 with
  | None,   None,        None      => Ending B0
  | Some a, None,        None      => Ending (B1 a)
  | None,   None,        Some a    => Ending (B1 a)
  | Some a, None,        Some b    => Ending (B2 a b)
  | None,   Some (a, b), None      => Ending (B2 a b)
  | Some a, Some (b, c), None      => Ending (B3 a b c)
  | None,   Some (a, b), Some c    => Ending (B3 a b c)
  | Some a, Some (b, c), Some d    => Ending (B4 a b c d)
  end.

Definition make_small {A : Type}
    (b1 : Buf5 (E.t A))
    (b2 : Buf5 (E.t A))
    (b3 : Buf5 (E.t A))
    : option (Chain A) :=
  match prefix_decompose b1, suffix_decompose b3 with
  (* Case (Underflow, Underflow) *)
  | BD_pre_underflow p1opt, BD_suf_underflow s1opt =>
      match buffer_unsandwich b2 with
      | BS_alone midopt =>
          (* midopt : option (E.t A) where the E.t A is a "pair" element. *)
          match midopt with
          | None => Some (mk_ending_from_options p1opt None s1opt)
          | Some elem =>
              match E.unpair A elem with
              | Some pair_elt =>
                  Some (mk_ending_from_options p1opt (Some pair_elt) s1opt)
              | None => None
              end
          end
      | BS_sandwich ab rest cd =>
          (* ab, cd are E.t A "pair" elements; need to unpair both *)
          match E.unpair A ab, E.unpair A cd with
          | Some pair_ab, Some pair_cd =>
              Some (ChainCons
                      (PNode (prefix23 p1opt pair_ab) Hole
                             (suffix23 pair_cd s1opt))
                      (Ending rest))
          | _, _ => None
          end
      end

  (* Case (Underflow, Ok) *)
  | BD_pre_underflow p1opt, BD_suf_ok s1' =>
      match buf5_pop_naive b2, p1opt with
      | None, None         => Some (Ending s1')
      | None, Some x       =>
          (* Push x onto s1' (green) — yields yellow, encode as buffer_push. *)
          (* buffer_push x s1': size+1 *)
          match buf5_push_naive x s1' with
          | Some s1'' => Some (Ending s1'')
          | None      => None  (* shouldn't happen; s1' is green *)
          end
      | Some (cd, rest), _ =>
          match E.unpair A cd with
          | Some pair_cd =>
              Some (ChainCons
                      (PNode (prefix23 p1opt pair_cd) Hole s1')
                      (Ending rest))
          | None => None
          end
      end

  (* Case (Underflow, Overflow): suffix overflowed, prefix underflowed *)
  | BD_pre_underflow p1opt, BD_suf_overflow s1' a b =>
      (* Inject (a, b) onto front of b2 via suffix_rot, take the resulting
         "paired" element and push it onto pre.  Mirror Viennot:
            let cd, center = suffix_rot b2 ab in
            Chain (G, Packet (prefix23 p1 cd, Hole, s1), Ending center) *)
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          let ab_paired := E.pair A a b eq in
          let '(cd_paired, center) := suffix_rot b2 ab_paired in
          match E.unpair A cd_paired with
          | Some pair_cd =>
              Some (ChainCons
                      (PNode (prefix23 p1opt pair_cd) Hole s1')
                      (Ending center))
          | None => None
          end
      | right _ => None
      end

  (* Case (Ok, Underflow): symmetric to (Underflow, Ok) *)
  | BD_pre_ok p1', BD_suf_underflow s1opt =>
      match buf5_eject_naive b2, s1opt with
      | None, None      => Some (Ending p1')
      | None, Some x    =>
          match buf5_inject_naive p1' x with
          | Some p1'' => Some (Ending p1'')
          | None      => None
          end
      | Some (rest, ab), _ =>
          match E.unpair A ab with
          | Some pair_ab =>
              Some (ChainCons
                      (PNode p1' Hole (suffix23 pair_ab s1opt))
                      (Ending rest))
          | None => None
          end
      end

  (* Case (Ok, Ok): both prefix and suffix already green *)
  | BD_pre_ok p1', BD_suf_ok s1' =>
      Some (ChainCons (PNode p1' Hole s1') (Ending b2))

  (* Case (Ok, Overflow): inject overflow's pair into b2 — may split if b2 was B4/B5 *)
  | BD_pre_ok p1', BD_suf_overflow s1' a b =>
      match Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq =>
          let ab_paired := E.pair A a b eq in
          let c2 := buffer_inject_chain b2 ab_paired in
          Some (ChainCons (PNode p1' Hole s1') c2)
      | right _ => None
      end

  (* Case (Overflow, Underflow): symmetric to (Underflow, Overflow) *)
  | BD_pre_overflow p1' c d, BD_suf_underflow s1opt =>
      match Nat.eq_dec (E.level A c) (E.level A d) with
      | left eq =>
          let cd_paired := E.pair A c d eq in
          let '(center, ab_paired) := prefix_rot cd_paired b2 in
          match E.unpair A ab_paired with
          | Some pair_ab =>
              Some (ChainCons
                      (PNode p1' Hole (suffix23 pair_ab s1opt))
                      (Ending center))
          | None => None
          end
      | right _ => None
      end

  (* Case (Overflow, Ok): push prefix overflow's pair onto b2 — may split *)
  | BD_pre_overflow p1' c d, BD_suf_ok s1' =>
      match Nat.eq_dec (E.level A c) (E.level A d) with
      | left eq =>
          let cd_paired := E.pair A c d eq in
          let c2 := buffer_push_chain cd_paired b2 in
          Some (ChainCons (PNode p1' Hole s1') c2)
      | right _ => None
      end

  (* Case (Overflow, Overflow): both buffers overflow, build depth-2 nested packet *)
  | BD_pre_overflow p1' c d, BD_suf_overflow s1' a b =>
      match Nat.eq_dec (E.level A c) (E.level A d),
            Nat.eq_dec (E.level A a) (E.level A b) with
      | left eq_cd, left eq_ab =>
          let cd_paired := E.pair A c d eq_cd in   (* level k+1 *)
          let ab_paired := E.pair A a b eq_ab in   (* level k+1 *)
          let '(midopt, rest_pairs) := buffer_halve b2 in
          (* midopt : option (E.t A) at level k+1.
             rest_pairs : Buf5 (E.t A * E.t A) where each (x,y) has x,y at level k+1.
             Need to pair each (x,y) into a level-k+2 element via E.pair. *)
          match pair_each_buf rest_pairs with
          | Some rest =>
              let p2 := suffix12 cd_paired midopt in   (* level k+1 *)
              Some (ChainCons
                      (PNode p1' (PNode p2 Hole (B1 ab_paired)) s1')
                      (Ending rest))
          | None => None
          end
      | _, _ => None
      end
  end.

(* ========================================================================== *)
(* green_of_red (Viennot lines 423-440): convert a red-headed chain to a      *)
(* green-headed chain.  Three cases.                                          *)
(* ========================================================================== *)

Definition green_of_red {A : Type} (c : Chain A) : option (Chain A) :=
  match c with
  (* Case 1: depth-1 red, tail is Ending. *)
  | ChainCons (PNode pre1 Hole suf1) (Ending b) =>
      make_small pre1 b suf1

  (* Case 2: depth-1 red, tail is depth-≥1 ChainCons (the "G" tail by KT99
     invariant, but we don't enforce that statically — caller's responsibility). *)
  | ChainCons (PNode pre1 Hole suf1)
              (ChainCons (PNode pre2 child suf2) c2) =>
      match green_prefix_concat pre1 pre2,
            green_suffix_concat suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          Some (ChainCons (PNode pre1' (PNode pre2' child suf2') suf1') c2)
      | _, _ => None
      end

  (* Case 3: depth-≥2 red. *)
  | ChainCons (PNode pre1 (PNode pre2 child suf2) suf1) c1 =>
      match prefix_concat pre1 pre2, suffix_concat suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          Some (ChainCons (PNode pre1' Hole suf1')
                          (ChainCons (PNode pre2' child suf2') c1))
      | _, _ => None
      end

  | _ => None
  end.

(* ========================================================================== *)
(* ensure_green (Viennot lines 443-448): if top is red, apply green_of_red.   *)
(* ========================================================================== *)

(** [pkt_outer_color]: derive packet color from buffer sizes.  This is
    only used in select fast paths; the authoritative color tag is
    carried explicitly on each [KCons] in [KChain]. *)
Definition pkt_outer_color {A : Type} (p : Packet A) : color :=
  match p with
  | Hole          => Green
  | PNode pre _ suf => color_meet (buf_color pre) (buf_color suf)
  end.

Definition chain_top_color {A : Type} (c : Chain A) : color :=
  match c with
  | Ending b => buf_color b
  | ChainCons p _ => pkt_outer_color p
  end.

Definition ensure_green {A : Type} (c : Chain A) : option (Chain A) :=
  match c with
  | Ending _ => Some c
  | ChainCons p _ =>
      match pkt_outer_color p with
      | Red => green_of_red c
      | _   => Some c
      end
  end.

(* ========================================================================== *)
(* make_yellow / make_red: thin constructors that call ensure_green.          *)
(* ========================================================================== *)

Definition make_yellow {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : Chain A) : option (Chain A) :=
  match ensure_green c with
  | Some c' => Some (ChainCons (PNode pre i suf) c')
  | None    => None
  end.

Definition make_red {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : Chain A) : option (Chain A) :=
  green_of_red (ChainCons (PNode pre i suf) c).

(* ========================================================================== *)
(* push, inject, pop, eject (Viennot lines 470-516).                           *)
(* Color-dispatched, non-recursive, WC O(1).                                   *)
(* ========================================================================== *)

(** [push_kt x c]: push [x] onto the front of [c].

    Mirrors Viennot:
      | Ending b         -> T (buffer_push x b)
      | Chain (G, p, c)  -> let p1 = green_push x p1 in make_yellow p1 child s1 c
      | Chain (Y, p, c)  -> let p1 = yellow_push x p1 in make_red p1 child s1 c

    [buffer_push x b] is [buf5_push_naive x b] when the result is non-B5,
    or a depth-1 fresh chain when input was B5 (split). *)

Definition push_kt {A : Type} (x : E.t A) (c : Chain A) : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_push_naive x b with
      | Some b' => Some (Ending b')
      | None    =>
          (* b was B5: split into Chain(G, Packet(B3(x,a,b), Hole, B3(c,d,e)), Ending B0).
             Need to E.pair adjacent elements... but Viennot's split keeps original
             5 elements as B3+B3 unpaired (same level).  Just rearrange. *)
          match b with
          | B5 a1 b1 c1 d1 e1 =>
              (* Push x onto B5 a b c d e gives 6 elements.  Split as
                 [x, a, b] [c, d, e] (both B3) at the SAME level, with
                 a fresh Ending(B0) below.  This is correct because the
                 outer level is unchanged; b had elements at level k,
                 and the new B3s at level k.  But the inner Ending B0
                 needs to be at level k+1 — and B0 has no elements so
                 no level constraint. *)
              Some (ChainCons (PNode (B3 x a1 b1) Hole (B3 c1 d1 e1))
                              (Ending B0))
          | _ => None
          end
      end
  | ChainCons (PNode pre i suf) c' =>
      match buf_color pre with
      | Green =>
          match green_push x pre with
          | Some pre' => make_yellow pre' i suf c'
          | None      => None  (* invariant violation *)
          end
      | Yellow =>
          match yellow_push x pre with
          | Some pre' => make_red pre' i suf c'
          | None      => None
          end
      | Red => None  (* invariant violation: input top should be G or Y *)
      end
  | ChainCons Hole _ => None  (* invariant violation: chain top is Hole *)
  end.

Definition inject_kt {A : Type} (c : Chain A) (x : E.t A) : option (Chain A) :=
  match c with
  | Ending b =>
      match buf5_inject_naive b x with
      | Some b' => Some (Ending b')
      | None    =>
          match b with
          | B5 a1 b1 c1 d1 e1 =>
              Some (ChainCons (PNode (B3 a1 b1 c1) Hole (B3 d1 e1 x))
                              (Ending B0))
          | _ => None
          end
      end
  | ChainCons (PNode pre i suf) c' =>
      match buf_color suf with
      | Green =>
          match green_inject suf x with
          | Some suf' => make_yellow pre i suf' c'
          | None      => None
          end
      | Yellow =>
          match yellow_inject suf x with
          | Some suf' => make_red pre i suf' c'
          | None      => None
          end
      | Red => None
      end
  | ChainCons Hole _ => None
  end.

Definition pop_kt {A : Type} (c : Chain A) : option (E.t A * Chain A) :=
  match c with
  | Ending b =>
      match buf5_pop_naive b with
      | Some (x, b') => Some (x, Ending b')
      | None         => None  (* truly empty *)
      end
  | ChainCons (PNode pre i suf) c' =>
      match buf_color pre with
      | Green =>
          match green_pop pre with
          | Some (x, pre') =>
              match make_yellow pre' i suf c' with
              | Some c'' => Some (x, c'')
              | None     => None
              end
          | None => None
          end
      | Yellow =>
          match yellow_pop pre with
          | Some (x, pre') =>
              match make_red pre' i suf c' with
              | Some c'' => Some (x, c'')
              | None     => None
              end
          | None => None
          end
      | Red => None
      end
  | ChainCons Hole _ => None
  end.

Definition eject_kt {A : Type} (c : Chain A) : option (Chain A * E.t A) :=
  match c with
  | Ending b =>
      match buf5_eject_naive b with
      | Some (b', x) => Some (Ending b', x)
      | None         => None
      end
  | ChainCons (PNode pre i suf) c' =>
      match buf_color suf with
      | Green =>
          match green_eject suf with
          | Some (suf', x) =>
              match make_yellow pre i suf' c' with
              | Some c'' => Some (c'', x)
              | None     => None
              end
          | None => None
          end
      | Yellow =>
          match yellow_eject suf with
          | Some (suf', x) =>
              match make_red pre i suf' c' with
              | Some c'' => Some (c'', x)
              | None     => None
              end
          | None => None
          end
      | Red => None
      end
  | ChainCons Hole _ => None
  end.

(* ========================================================================== *)
(* KChain: chain with explicit color tag at each link.                        *)
(*                                                                            *)
(* The Chain-based ops above (push_kt etc.) are broken in the iterated case   *)
(* because we cannot derive each packet's "true" color (per Viennot's GADT    *)
(* typing) from buffer sizes alone.  KChain carries the color explicitly,    *)
(* which is the proper analogue of Viennot's regularity tag.                  *)
(*                                                                            *)
(* This is the WC O(1) implementation that mirrors Viennot's algorithm        *)
(* faithfully and is suitable for benchmarking.                               *)
(* ========================================================================== *)

Inductive KChain (A : Type) : Type :=
| KEnding : Buf5 (E.t A) -> KChain A
| KCons   : color -> Packet A -> KChain A -> KChain A.

Arguments KEnding {A} _.
Arguments KCons   {A} _ _ _.

Definition empty_kchain {A : Type} : KChain A := KEnding B0.

Definition kchain_top_color {A : Type} (c : KChain A) : color :=
  match c with
  | KEnding _     => Green   (* Ending is always allowed everywhere *)
  | KCons col _ _ => col
  end.

(** Convert a Chain (with all-green tags) to KChain.  Only applicable when
    the Chain came from a [make_small] / [buffer_push_chain] /
    [buffer_inject_chain] result — those produce green-headed chains
    whose deeper levels are also green (or Ending). *)
Fixpoint chain_to_kchain_g {A : Type} (c : Chain A) : KChain A :=
  match c with
  | Ending b        => KEnding b
  | ChainCons p c'  => KCons Green p (chain_to_kchain_g c')
  end.

(** [kchain_to_list]: sequence semantics by reusing [chain_seq] via a
    forgetful mapping (drops color tags). *)
Fixpoint kchain_to_chain {A : Type} (c : KChain A) : Chain A :=
  match c with
  | KEnding b       => Ending b
  | KCons _ p c'    => ChainCons p (kchain_to_chain c')
  end.

Definition kchain_to_list {A : Type} (c : KChain A) : list A :=
  chain_to_list (kchain_to_chain c).

(* ---------- KChain version of green_of_red, ensure_green, push, etc. ---- *)

Definition green_of_red_k {A : Type} (c : KChain A) : option (KChain A) :=
  match c with
  (* Case 1: R with Hole inner, Ending tail. *)
  | KCons Red (PNode pre1 Hole suf1) (KEnding b) =>
      match make_small pre1 b suf1 with
      | Some c'' => Some (chain_to_kchain_g c'')
      | None     => None
      end

  (* Case 2: R with Hole inner, ChainCons tail (must be G or Ending per KT99). *)
  | KCons Red (PNode pre1 Hole suf1)
              (KCons _ (PNode pre2 child suf2) c2) =>
      match green_prefix_concat pre1 pre2,
            green_suffix_concat suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          (* Result: G outer with yellow-run inner.  Tag G. *)
          Some (KCons Green
                      (PNode pre1' (PNode pre2' child suf2') suf1')
                      c2)
      | _, _ => None
      end

  (* Case 3: R with PNode inner. *)
  | KCons Red (PNode pre1 (PNode pre2 child suf2) suf1) c1 =>
      match prefix_concat pre1 pre2, suffix_concat suf2 suf1 with
      | Some (pre1', pre2'), Some (suf2', suf1') =>
          (* Result: G outer + new R inner + original c1 (preserved with its tag). *)
          Some (KCons Green (PNode pre1' Hole suf1')
                            (KCons Red (PNode pre2' child suf2') c1))
      | _, _ => None
      end

  | _ => None
  end.

Definition ensure_green_k {A : Type} (c : KChain A) : option (KChain A) :=
  match c with
  | KEnding _      => Some c
  | KCons Red _ _  => green_of_red_k c
  | _              => Some c
  end.

Definition make_yellow_k {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : KChain A) : option (KChain A) :=
  match ensure_green_k c with
  | Some c' => Some (KCons Yellow (PNode pre i suf) c')
  | None    => None
  end.

Definition make_red_k {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : KChain A) : option (KChain A) :=
  green_of_red_k (KCons Red (PNode pre i suf) c).

(** [push_kt2 x c]: push onto KChain.  Color-dispatched per Viennot. *)
Definition push_kt2 {A : Type} (x : E.t A) (c : KChain A) : option (KChain A) :=
  match c with
  | KEnding b =>
      match buf5_push_naive x b with
      | Some b' => Some (KEnding b')
      | None    =>
          match b with
          | B5 a1 b1 c1 d1 e1 =>
              Some (KCons Green
                          (PNode (B3 x a1 b1) Hole (B3 c1 d1 e1))
                          (KEnding B0))
          | _ => None
          end
      end
  | KCons Green (PNode pre i suf) c' =>
      match green_push x pre with
      | Some pre' => make_yellow_k pre' i suf c'
      | None      => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match yellow_push x pre with
      | Some pre' => make_red_k pre' i suf c'
      | None      => None
      end
  | KCons Red _ _ => None  (* invariant violation: top should be G or Y *)
  | KCons _ Hole _ => None
  end.

Definition inject_kt2 {A : Type} (c : KChain A) (x : E.t A) : option (KChain A) :=
  match c with
  | KEnding b =>
      match buf5_inject_naive b x with
      | Some b' => Some (KEnding b')
      | None    =>
          match b with
          | B5 a1 b1 c1 d1 e1 =>
              Some (KCons Green
                          (PNode (B3 a1 b1 c1) Hole (B3 d1 e1 x))
                          (KEnding B0))
          | _ => None
          end
      end
  | KCons Green (PNode pre i suf) c' =>
      match green_inject suf x with
      | Some suf' => make_yellow_k pre i suf' c'
      | None      => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match yellow_inject suf x with
      | Some suf' => make_red_k pre i suf' c'
      | None      => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

Definition pop_kt2 {A : Type} (c : KChain A) : option (E.t A * KChain A) :=
  match c with
  | KEnding b =>
      match buf5_pop_naive b with
      | Some (x, b') => Some (x, KEnding b')
      | None         => None
      end
  | KCons Green (PNode pre i suf) c' =>
      match green_pop pre with
      | Some (x, pre') =>
          match make_yellow_k pre' i suf c' with
          | Some c'' => Some (x, c'')
          | None     => None
          end
      | None => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match yellow_pop pre with
      | Some (x, pre') =>
          match make_red_k pre' i suf c' with
          | Some c'' => Some (x, c'')
          | None     => None
          end
      | None => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

Definition eject_kt2 {A : Type} (c : KChain A) : option (KChain A * E.t A) :=
  match c with
  | KEnding b =>
      match buf5_eject_naive b with
      | Some (b', x) => Some (KEnding b', x)
      | None         => None
      end
  | KCons Green (PNode pre i suf) c' =>
      match green_eject suf with
      | Some (suf', x) =>
          match make_yellow_k pre i suf' c' with
          | Some c'' => Some (c'', x)
          | None     => None
          end
      | None => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match yellow_eject suf with
      | Some (suf', x) =>
          match make_red_k pre i suf' c' with
          | Some c'' => Some (c'', x)
          | None     => None
          end
      | None => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

(* ========================================================================== *)
(* Optimized variants: push_kt3 / pop_kt3 / inject_kt3 / eject_kt3            *)
(*                                                                            *)
(* Inline [make_yellow_k] / [ensure_green_k] / [make_red_k] into the body of  *)
(* each op, and special-case the common "tail is not Red" path to avoid the   *)
(* dispatch through [green_of_red_k].                                         *)
(*                                                                            *)
(* The outputs are operationally equivalent to the *_kt2 versions; this is a  *)
(* pure constant-factor optimization for OCaml extraction.                    *)
(* ========================================================================== *)

(** [yellow_wrap pre i suf c]: equivalent to [make_yellow_k pre i suf c] but
    with [ensure_green_k] inlined and the non-Red fast path special-cased. *)
Definition yellow_wrap {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : KChain A) : option (KChain A) :=
  match c with
  | KCons Red _ _ =>
      (* Rare: tail is R, must fix via green_of_red_k. *)
      match green_of_red_k c with
      | Some c' => Some (KCons Yellow (PNode pre i suf) c')
      | None    => None
      end
  | _ =>
      (* Fast path: tail is Ending or G or Y; ensure_green is a no-op. *)
      Some (KCons Yellow (PNode pre i suf) c)
  end.

Definition push_kt3 {A : Type} (x : E.t A) (c : KChain A) : option (KChain A) :=
  match c with
  | KEnding b =>
      match b with
      | B0           => Some (KEnding (B1 x))
      | B1 a         => Some (KEnding (B2 x a))
      | B2 a b1      => Some (KEnding (B3 x a b1))
      | B3 a b1 c1   => Some (KEnding (B4 x a b1 c1))
      | B4 a b1 c1 d => Some (KEnding (B5 x a b1 c1 d))
      | B5 a b1 c1 d e =>
          Some (KCons Green
                      (PNode (B3 x a b1) Hole (B3 c1 d e))
                      (KEnding B0))
      end
  | KCons Green (PNode pre i suf) c' =>
      match pre with
      | B2 a b1     => yellow_wrap (B3 x a b1) i suf c'
      | B3 a b1 c1  => yellow_wrap (B4 x a b1 c1) i suf c'
      | _           => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match pre with
      | B1 a            => Some (KCons Yellow (PNode (B2 x a) i suf) c')
      | B2 a b1         => Some (KCons Yellow (PNode (B3 x a b1) i suf) c')
      | B3 a b1 c1      => Some (KCons Yellow (PNode (B4 x a b1 c1) i suf) c')
      | B4 a b1 c1 d    =>
          (* Push gives B5, fire green_of_red. *)
          green_of_red_k (KCons Red (PNode (B5 x a b1 c1 d) i suf) c')
      | _ => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

Definition inject_kt3 {A : Type} (c : KChain A) (x : E.t A) : option (KChain A) :=
  match c with
  | KEnding b =>
      match b with
      | B0           => Some (KEnding (B1 x))
      | B1 a         => Some (KEnding (B2 a x))
      | B2 a b1      => Some (KEnding (B3 a b1 x))
      | B3 a b1 c1   => Some (KEnding (B4 a b1 c1 x))
      | B4 a b1 c1 d => Some (KEnding (B5 a b1 c1 d x))
      | B5 a b1 c1 d e =>
          Some (KCons Green
                      (PNode (B3 a b1 c1) Hole (B3 d e x))
                      (KEnding B0))
      end
  | KCons Green (PNode pre i suf) c' =>
      match suf with
      | B2 a b1     => yellow_wrap pre i (B3 a b1 x) c'
      | B3 a b1 c1  => yellow_wrap pre i (B4 a b1 c1 x) c'
      | _           => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match suf with
      | B1 a            => Some (KCons Yellow (PNode pre i (B2 a x)) c')
      | B2 a b1         => Some (KCons Yellow (PNode pre i (B3 a b1 x)) c')
      | B3 a b1 c1      => Some (KCons Yellow (PNode pre i (B4 a b1 c1 x)) c')
      | B4 a b1 c1 d    =>
          green_of_red_k (KCons Red (PNode pre i (B5 a b1 c1 d x)) c')
      | _ => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

Definition pop_kt3 {A : Type} (c : KChain A) : option (E.t A * KChain A) :=
  match c with
  | KEnding b =>
      match b with
      | B0           => None
      | B1 a         => Some (a, KEnding B0)
      | B2 a b1      => Some (a, KEnding (B1 b1))
      | B3 a b1 c1   => Some (a, KEnding (B2 b1 c1))
      | B4 a b1 c1 d => Some (a, KEnding (B3 b1 c1 d))
      | B5 a b1 c1 d e => Some (a, KEnding (B4 b1 c1 d e))
      end
  | KCons Green (PNode pre i suf) c' =>
      match pre with
      | B2 a b1 =>
          match yellow_wrap (B1 b1) i suf c' with
          | Some c'' => Some (a, c'')
          | None     => None
          end
      | B3 a b1 c1 =>
          match yellow_wrap (B2 b1 c1) i suf c' with
          | Some c'' => Some (a, c'')
          | None     => None
          end
      | _ => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match pre with
      | B1 a =>
          match green_of_red_k (KCons Red (PNode B0 i suf) c') with
          | Some c'' => Some (a, c'')
          | None     => None
          end
      | B2 a b1 => Some (a, KCons Yellow (PNode (B1 b1) i suf) c')
      | B3 a b1 c1 => Some (a, KCons Yellow (PNode (B2 b1 c1) i suf) c')
      | B4 a b1 c1 d => Some (a, KCons Yellow (PNode (B3 b1 c1 d) i suf) c')
      | _ => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

Definition eject_kt3 {A : Type} (c : KChain A) : option (KChain A * E.t A) :=
  match c with
  | KEnding b =>
      match b with
      | B0           => None
      | B1 a         => Some (KEnding B0, a)
      | B2 a b1      => Some (KEnding (B1 a), b1)
      | B3 a b1 c1   => Some (KEnding (B2 a b1), c1)
      | B4 a b1 c1 d => Some (KEnding (B3 a b1 c1), d)
      | B5 a b1 c1 d e => Some (KEnding (B4 a b1 c1 d), e)
      end
  | KCons Green (PNode pre i suf) c' =>
      match suf with
      | B2 a b1 =>
          match yellow_wrap pre i (B1 a) c' with
          | Some c'' => Some (c'', b1)
          | None     => None
          end
      | B3 a b1 c1 =>
          match yellow_wrap pre i (B2 a b1) c' with
          | Some c'' => Some (c'', c1)
          | None     => None
          end
      | _ => None
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match suf with
      | B1 a =>
          match green_of_red_k (KCons Red (PNode pre i B0) c') with
          | Some c'' => Some (c'', a)
          | None     => None
          end
      | B2 a b1 => Some (KCons Yellow (PNode pre i (B1 a)) c', b1)
      | B3 a b1 c1 => Some (KCons Yellow (PNode pre i (B2 a b1)) c', c1)
      | B4 a b1 c1 d => Some (KCons Yellow (PNode pre i (B3 a b1 c1)) c', d)
      | _ => None
      end
  | KCons Red _ _ => None
  | KCons _ Hole _ => None
  end.

(* ========================================================================== *)
(* push_kt4 / pop_kt4 / inject_kt4 / eject_kt4: no-option variants.            *)
(*                                                                            *)
(* These return a custom 2-constructor sum type instead of [option (X * Y)].  *)
(* OCaml extracts [option (X * Y)] as nested allocations: the outer [Some]    *)
(* holds a heap pointer to a [(X, Y)] tuple block.  By using a flat            *)
(* constructor [PopOk : X -> Y -> push_result] we save one allocation per     *)
(* successful op (and the bench's hot loop is allocation-bound).              *)
(* ========================================================================== *)

Inductive push_result (A : Type) : Type :=
| PushFail : push_result A
| PushOk   : KChain A -> push_result A.
Arguments PushFail {A}.
Arguments PushOk   {A} _.

Inductive pop_result (A : Type) : Type :=
| PopFail : pop_result A
| PopOk   : E.t A -> KChain A -> pop_result A.
Arguments PopFail {A}.
Arguments PopOk   {A} _ _.

(** [yellow_wrap_pr]: yellow_wrap variant returning push_result. *)
Definition yellow_wrap_pr {A : Type}
    (pre : Buf5 (E.t A)) (i : Packet A) (suf : Buf5 (E.t A))
    (c : KChain A) : push_result A :=
  match c with
  | KCons Red _ _ =>
      match green_of_red_k c with
      | Some c' => PushOk (KCons Yellow (PNode pre i suf) c')
      | None    => PushFail
      end
  | _ =>
      PushOk (KCons Yellow (PNode pre i suf) c)
  end.

Definition push_kt4 {A : Type} (x : E.t A) (c : KChain A) : push_result A :=
  match c with
  | KEnding b =>
      match b with
      | B0           => PushOk (KEnding (B1 x))
      | B1 a         => PushOk (KEnding (B2 x a))
      | B2 a b1      => PushOk (KEnding (B3 x a b1))
      | B3 a b1 c1   => PushOk (KEnding (B4 x a b1 c1))
      | B4 a b1 c1 d => PushOk (KEnding (B5 x a b1 c1 d))
      | B5 a b1 c1 d e =>
          PushOk (KCons Green
                        (PNode (B3 x a b1) Hole (B3 c1 d e))
                        (KEnding B0))
      end
  | KCons Green (PNode pre i suf) c' =>
      match pre with
      | B2 a b1     => yellow_wrap_pr (B3 x a b1) i suf c'
      | B3 a b1 c1  => yellow_wrap_pr (B4 x a b1 c1) i suf c'
      | _           => PushFail
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match pre with
      | B1 a            => PushOk (KCons Yellow (PNode (B2 x a) i suf) c')
      | B2 a b1         => PushOk (KCons Yellow (PNode (B3 x a b1) i suf) c')
      | B3 a b1 c1      => PushOk (KCons Yellow (PNode (B4 x a b1 c1) i suf) c')
      | B4 a b1 c1 d    =>
          match green_of_red_k (KCons Red (PNode (B5 x a b1 c1 d) i suf) c') with
          | Some c'' => PushOk c''
          | None     => PushFail
          end
      | _ => PushFail
      end
  | KCons Red _ _ => PushFail
  | KCons _ Hole _ => PushFail
  end.

Definition inject_kt4 {A : Type} (c : KChain A) (x : E.t A) : push_result A :=
  match c with
  | KEnding b =>
      match b with
      | B0           => PushOk (KEnding (B1 x))
      | B1 a         => PushOk (KEnding (B2 a x))
      | B2 a b1      => PushOk (KEnding (B3 a b1 x))
      | B3 a b1 c1   => PushOk (KEnding (B4 a b1 c1 x))
      | B4 a b1 c1 d => PushOk (KEnding (B5 a b1 c1 d x))
      | B5 a b1 c1 d e =>
          PushOk (KCons Green
                        (PNode (B3 a b1 c1) Hole (B3 d e x))
                        (KEnding B0))
      end
  | KCons Green (PNode pre i suf) c' =>
      match suf with
      | B2 a b1     => yellow_wrap_pr pre i (B3 a b1 x) c'
      | B3 a b1 c1  => yellow_wrap_pr pre i (B4 a b1 c1 x) c'
      | _           => PushFail
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match suf with
      | B1 a            => PushOk (KCons Yellow (PNode pre i (B2 a x)) c')
      | B2 a b1         => PushOk (KCons Yellow (PNode pre i (B3 a b1 x)) c')
      | B3 a b1 c1      => PushOk (KCons Yellow (PNode pre i (B4 a b1 c1 x)) c')
      | B4 a b1 c1 d    =>
          match green_of_red_k (KCons Red (PNode pre i (B5 a b1 c1 d x)) c') with
          | Some c'' => PushOk c''
          | None     => PushFail
          end
      | _ => PushFail
      end
  | KCons Red _ _ => PushFail
  | KCons _ Hole _ => PushFail
  end.

Definition pop_kt4 {A : Type} (c : KChain A) : pop_result A :=
  match c with
  | KEnding b =>
      match b with
      | B0           => PopFail
      | B1 a         => PopOk a (KEnding B0)
      | B2 a b1      => PopOk a (KEnding (B1 b1))
      | B3 a b1 c1   => PopOk a (KEnding (B2 b1 c1))
      | B4 a b1 c1 d => PopOk a (KEnding (B3 b1 c1 d))
      | B5 a b1 c1 d e => PopOk a (KEnding (B4 b1 c1 d e))
      end
  | KCons Green (PNode pre i suf) c' =>
      match pre with
      | B2 a b1 =>
          match yellow_wrap_pr (B1 b1) i suf c' with
          | PushOk c'' => PopOk a c''
          | PushFail   => PopFail
          end
      | B3 a b1 c1 =>
          match yellow_wrap_pr (B2 b1 c1) i suf c' with
          | PushOk c'' => PopOk a c''
          | PushFail   => PopFail
          end
      | _ => PopFail
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match pre with
      | B1 a =>
          match green_of_red_k (KCons Red (PNode B0 i suf) c') with
          | Some c'' => PopOk a c''
          | None     => PopFail
          end
      | B2 a b1 => PopOk a (KCons Yellow (PNode (B1 b1) i suf) c')
      | B3 a b1 c1 => PopOk a (KCons Yellow (PNode (B2 b1 c1) i suf) c')
      | B4 a b1 c1 d => PopOk a (KCons Yellow (PNode (B3 b1 c1 d) i suf) c')
      | _ => PopFail
      end
  | KCons Red _ _ => PopFail
  | KCons _ Hole _ => PopFail
  end.

Definition eject_kt4 {A : Type} (c : KChain A) : pop_result A :=
  match c with
  | KEnding b =>
      match b with
      | B0           => PopFail
      | B1 a         => PopOk a (KEnding B0)
      | B2 a b1      => PopOk b1 (KEnding (B1 a))
      | B3 a b1 c1   => PopOk c1 (KEnding (B2 a b1))
      | B4 a b1 c1 d => PopOk d (KEnding (B3 a b1 c1))
      | B5 a b1 c1 d e => PopOk e (KEnding (B4 a b1 c1 d))
      end
  | KCons Green (PNode pre i suf) c' =>
      match suf with
      | B2 a b1 =>
          match yellow_wrap_pr pre i (B1 a) c' with
          | PushOk c'' => PopOk b1 c''
          | PushFail   => PopFail
          end
      | B3 a b1 c1 =>
          match yellow_wrap_pr pre i (B2 a b1) c' with
          | PushOk c'' => PopOk c1 c''
          | PushFail   => PopFail
          end
      | _ => PopFail
      end
  | KCons Yellow (PNode pre i suf) c' =>
      match suf with
      | B1 a =>
          match green_of_red_k (KCons Red (PNode pre i B0) c') with
          | Some c'' => PopOk a c''
          | None     => PopFail
          end
      | B2 a b1 => PopOk b1 (KCons Yellow (PNode pre i (B1 a)) c')
      | B3 a b1 c1 => PopOk c1 (KCons Yellow (PNode pre i (B2 a b1)) c')
      | B4 a b1 c1 d => PopOk d (KCons Yellow (PNode pre i (B3 a b1 c1)) c')
      | _ => PopFail
      end
  | KCons Red _ _ => PopFail
  | KCons _ Hole _ => PopFail
  end.
