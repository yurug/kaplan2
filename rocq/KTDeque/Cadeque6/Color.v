(** * Module: KTDeque.Cadeque6.Color -- Section-6 four-color discipline.

    First-time reader: read [kb/spec/why-catenable.md] §3 and
    manual §10.6 before this file.

    ## Why this exists

    Phase 5.5 of the catenable plan introduces the regularity
    invariant for cadeques.  The invariant is colour-based: each
    triple has a colour (Green / Yellow / Orange / Red) determined
    by buffer sizes and structure, and the regular shapes are
    those satisfying KT99 §6 / manual §10.8's preferred-path
    rules.

    This file is the foundation: the colour datatype, the
    "worse-of" operator on colours, and the mathematical functions
    [buf6_color] and [triple_color] that read off the colour of a
    buffer / triple.

    The regularity *predicate* itself ([regular_cad], plus
    [semiregular_cad], plus the preservation theorems) is in
    [Cadeque6/Regularity.v], which imports this file.

    ## Important: extrinsic vs intrinsic

    The colour functions defined here are *mathematical* — they
    read the colour off the structure.  This is fine for the
    extrinsic invariant ("a triple is regular when its mathematical
    colour satisfies the preferred-path rules").

    The Section-4 lesson (recorded in
    [kb/conventions/proof-style.md] / agent memory) was that the
    *operational* layer must carry colour as an explicit constructor
    tag, not derive it from buffer sizes — because [green_of_red]
    Case 3 produces R-tagged packets with G-looking buffers.  That
    rule applies to the future intrinsic [KCadeque] type (Phase 5.6+),
    not to the predicates defined here.  This file is the abstract
    colour spec.

    ## Manual reference

    Manual §10.6 (verbatim):
    >  5 -> Red4
    >  6 -> Orange4
    >  7 -> Yellow4
    >  8 and above -> Green4
    >  Stored triples are always green.
    >  Ordinary triples:
    >  - if child is empty, green;
    >  - if Only, worse of prefix and suffix colours;
    >  - if Left, prefix colour;
    >  - if Right, suffix colour.

    Sizes 0..4 are not handled by §10.6 because no well-formed
    triple has them in the colour-determining buffer position
    ([(OT1)..(OT4)] forbid this).  We extend [buf6_color] to a
    total function that returns [Green4] for sizes outside 5..7;
    the only valid call sites are sizes ≥ 5.

    ## Cross-references

    - [kb/spec/why-catenable.md]    -- intuition layer.
    - [kb/execution-manual-v3.md]   -- §10.5-10.8 colour rules.
    - [Cadeque6/Regularity.v]       -- the predicate built on top.
    - [DequePtr/Colored.v]          -- the parallel Section-4
                                       colour module (different
                                       palette: G/Y/R only).
*)

From Stdlib Require Import List Lia.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.
From KTDeque.Cadeque6 Require Import Model.

(** ** [Color4]: the four colours of Section 6.

    Ordering by "worseness" (worst first): [Red4] is worst,
    [Green4] is best.  The order matters for the [color4_meet]
    operator (worse-of). *)

Inductive Color4 : Type :=
| Green4
| Yellow4
| Orange4
| Red4.

(** ** [color4_meet]: worse-of operator.

    [color4_meet c1 c2] is the worse of [c1] and [c2].  Used for
    [TOnly] triples whose colour is the worse of prefix and suffix
    colours. *)

Definition color4_meet (c1 c2 : Color4) : Color4 :=
  match c1, c2 with
  | Red4, _    | _, Red4    => Red4
  | Orange4, _ | _, Orange4 => Orange4
  | Yellow4, _ | _, Yellow4 => Yellow4
  | Green4, Green4          => Green4
  end.

(** ** [color4_meet] sanity laws. *)

Lemma color4_meet_idem :
  forall c, color4_meet c c = c.
Proof. intros c; destruct c; reflexivity. Qed.

Lemma color4_meet_comm :
  forall c1 c2, color4_meet c1 c2 = color4_meet c2 c1.
Proof. intros c1 c2; destruct c1, c2; reflexivity. Qed.

Lemma color4_meet_assoc :
  forall c1 c2 c3,
    color4_meet (color4_meet c1 c2) c3
    = color4_meet c1 (color4_meet c2 c3).
Proof. intros c1 c2 c3; destruct c1, c2, c3; reflexivity. Qed.

Lemma color4_meet_green_l :
  forall c, color4_meet Green4 c = c.
Proof. intros c; destruct c; reflexivity. Qed.

Lemma color4_meet_green_r :
  forall c, color4_meet c Green4 = c.
Proof. intros c; destruct c; reflexivity. Qed.

Lemma color4_meet_red_l :
  forall c, color4_meet Red4 c = Red4.
Proof. intros c; destruct c; reflexivity. Qed.

Lemma color4_meet_red_r :
  forall c, color4_meet c Red4 = Red4.
Proof. intros c; destruct c; reflexivity. Qed.

(** ** [buf6_color]: Section-6 colour from buffer size (manual §10.6).

    Sizes 5/6/7 → Red/Orange/Yellow.  Sizes 8+ → Green.  Sizes 0..4
    are not handled by the algorithm in colour-determining
    positions; we return [Green4] as a defensive default — call
    sites should already enforce size ≥ 5 via the regularity
    invariant. *)

Definition buf6_color {X : Type} (b : Buf6 X) : Color4 :=
  match buf6_size b with
  | 5 => Red4
  | 6 => Orange4
  | 7 => Yellow4
  | _ => Green4
  end.

(** ** Sanity: [buf6_color] of an 8-element buffer is Green. *)

Example buf6_color_eight :
  buf6_color (mkBuf6 [1;2;3;4;5;6;7;8]) = Green4.
Proof. reflexivity. Qed.

(** ** Sanity: [buf6_color] of a 5-element buffer is Red. *)

Example buf6_color_five :
  buf6_color (mkBuf6 [1;2;3;4;5]) = Red4.
Proof. reflexivity. Qed.

(** ** [triple_color]: Section-6 colour of an ordinary triple
    (manual §10.6).

    Rule:
    - child empty (any kind)        → [Green4];
    - [TOnly]  with non-empty child → worse of pre and suf colours;
    - [TLeft]  with non-empty child → prefix colour;
    - [TRight] with non-empty child → suffix colour. *)

Definition triple_color {X : Type} (t : Triple X) : Color4 :=
  match t with
  | TOnly  pre c suf =>
      match c with
      | CEmpty => Green4
      | _      => color4_meet (buf6_color pre) (buf6_color suf)
      end
  | TLeft  pre c _ =>
      match c with
      | CEmpty => Green4
      | _      => buf6_color pre
      end
  | TRight _ c suf =>
      match c with
      | CEmpty => Green4
      | _      => buf6_color suf
      end
  end.

(** ** [stored_color]: Stored triples are always Green (manual §10.6).

    Trivially defined; included so client code can write uniformly
    against [Color4]-returning functions without special-casing. *)

Definition stored_color {X : Type} (_ : Stored X) : Color4 := Green4.

Lemma stored_color_always_green :
  forall (X : Type) (s : Stored X),
    stored_color s = Green4.
Proof. intros. reflexivity. Qed.

(** ** [is_green4] / [is_yellow4] / [is_orange4] / [is_red4]:
    boolean predicates on colours.  Useful for case-by-case
    rewriting in proofs about preservation. *)

Definition is_green4 (c : Color4) : bool :=
  match c with Green4 => true | _ => false end.

Definition is_yellow4 (c : Color4) : bool :=
  match c with Yellow4 => true | _ => false end.

Definition is_orange4 (c : Color4) : bool :=
  match c with Orange4 => true | _ => false end.

Definition is_red4 (c : Color4) : bool :=
  match c with Red4 => true | _ => false end.

(** ** Pushing onto an empty cadeque produces a green triple.

    Sanity check that the colour function agrees with the manual's
    "child empty → green" rule on the trivial post-push shape. *)

Lemma push_empty_color :
  forall (X : Type) (x : X),
    triple_color (TOnly (buf6_singleton x) CEmpty buf6_empty) = Green4.
Proof. intros. reflexivity. Qed.

(** ** Buffer-colour transitions on push.

    Push grows a buffer's size by 1.  Combining with the §10.6
    thresholds (5/6/7/8+ → R/O/Y/G), we get:

    Yellow (size 7) push   → Green (size 8)
    Green  (size ≥ 8) push → Green (size ≥ 9)

    Stated as a single lemma keyed on size ≥ 7: in either case the
    result is Green.  The Orange→Yellow and Red→Orange transitions
    are similar but rarely useful for preservation since regular
    cadeques avoid Red triples in colour-determining positions. *)

Lemma buf6_color_push_grows_to_green :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_size b >= 7 ->
    buf6_color (buf6_push x b) = Green4.
Proof.
  intros X x b Hsz.
  unfold buf6_color. rewrite buf6_push_size.
  remember (buf6_size b) as n eqn:Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]];
    cbn in Hsz; try lia; reflexivity.
Qed.

(** ** Symmetric for inject. *)

Lemma buf6_color_inject_grows_to_green :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_size b >= 7 ->
    buf6_color (buf6_inject b x) = Green4.
Proof.
  intros X b x Hsz.
  unfold buf6_color. rewrite buf6_inject_size.
  remember (buf6_size b) as n eqn:Hn.
  destruct n as [|[|[|[|[|[|[|[|n']]]]]]]];
    cbn in Hsz; try lia; reflexivity.
Qed.

(** ** A Green buffer (in the proper size range, ≥ 8) stays Green
    after push.

    This is the workhorse for regularity preservation: if a Green
    triple's prefix has size ≥ 8 (the "true" Green range, not the
    defensive default for sizes 0..4), then push keeps the prefix
    Green. *)

Lemma buf6_color_push_green_stays_green :
  forall (X : Type) (x : X) (b : Buf6 X),
    buf6_size b >= 8 ->
    buf6_color (buf6_push x b) = Green4.
Proof.
  intros. apply buf6_color_push_grows_to_green. lia.
Qed.

Lemma buf6_color_inject_green_stays_green :
  forall (X : Type) (b : Buf6 X) (x : X),
    buf6_size b >= 8 ->
    buf6_color (buf6_inject b x) = Green4.
Proof.
  intros. apply buf6_color_inject_grows_to_green. lia.
Qed.
