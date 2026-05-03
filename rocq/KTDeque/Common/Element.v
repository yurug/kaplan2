(** * Module: KTDeque.Common.Element -- abstract level-l element interface.

    Per ADR-0011 (option (a)'): the deque is parameterized by an abstract
    [t A] type representing "an element at some level".  This decouples the
    deque algorithm from the leaf representation, enabling cache-friendly
    target-specific instances (e.g., flat arrays for shallow levels +
    pointer pairs for deep levels — preserving worst-case O(1) when the
    array threshold is a constant).

    For Coq proofs we use the canonical [ElementTree] instance, which
    represents [t A] as [{ l : nat & xpow A l }] — a pair of a level and a
    perfectly balanced binary tree of [A]'s.

    Cross-references:
    - kb/architecture/decisions/adr-0011-element-abstraction.md
*)

From KTDeque.Common Require Import Prelude.

(* Element module types interact poorly with global [Set Implicit Arguments]
   because the parameter type families are auto-detected for implicit args
   inconsistently between Module Type declarations and instances.  We
   disable implicit-arg auto-detection locally; callers use explicit type
   arguments when needed. *)
Local Unset Implicit Arguments.

(** ** [xpow]: iterated product type, [xpow A l = A^(2^l)]. *)
Fixpoint xpow (A : Type) (l : nat) : Type :=
  match l with
  | 0    => A
  | S l' => xpow A l' * xpow A l'
  end.

(** [xflat l x] flattens a value of [xpow A l] into a list of [2^l] base
    [A]s, in left-to-right order. *)
Fixpoint xflat (A : Type) (l : nat) : xpow A l -> list A :=
  match l return xpow A l -> list A with
  | 0    => fun a => [a]
  | S l' => fun p => match p with (x, y) => @xflat A l' x ++ @xflat A l' y end
  end.

Lemma xflat_length : forall (A : Type) (l : nat) (x : xpow A l),
    length (@xflat A l x) = 2 ^ l.
Proof.
  intros A. induction l as [|l' IH]; intros x; cbn.
  - reflexivity.
  - destruct x as [a b].
    rewrite length_app, (IH a), (IH b). cbn. lia.
Qed.

(** ** Module Type ELEMENT.

    An [ELEMENT] provides:
    - a type [t A] of "level-l elements over A" for any [l],
    - a denotation [to_list : t A -> list A],
    - a [level] projection,
    - constructors [base] and [pair] (with a level-equality precondition),
    - a destructor [unpair].

    The axioms relate [to_list], [level], and the constructors. *)

Module Type ELEMENT.

  Parameter t : Type -> Type.

  Parameter to_list : forall (A : Type), t A -> list A.
  Parameter level   : forall (A : Type), t A -> nat.
  Parameter base    : forall (A : Type), A -> t A.
  Parameter pair    : forall (A : Type) (x y : t A)
                             (e : level A x = level A y), t A.
  Parameter unpair  : forall (A : Type), t A -> option (t A * t A).

  Axiom to_list_base :
    forall (A : Type) (a : A), to_list A (base A a) = [a].

  Axiom to_list_pair :
    forall (A : Type) (x y : t A) (e : level A x = level A y),
      to_list A (pair A x y e) = to_list A x ++ to_list A y.

  Axiom level_base :
    forall (A : Type) (a : A), level A (base A a) = 0.

  Axiom level_pair :
    forall (A : Type) (x y : t A) (e : level A x = level A y),
      level A (pair A x y e) = S (level A x).

  Axiom unpair_base :
    forall (A : Type) (a : A), unpair A (base A a) = None.

  Axiom unpair_pair :
    forall (A : Type) (x y : t A) (e : level A x = level A y),
      unpair A (pair A x y e) = Some (x, y).

End ELEMENT.

(** Make [A] implicit at use sites for ergonomics. *)
(* These declarations apply outside the Module Type to instances. *)

(** ** [ElementTree]: canonical instance using [{ l : nat & xpow A l }].

    Proofs use this instance.  It is the simplest mathematical model: a
    pair of a level and a perfectly balanced tree of [A]s.  No runtime
    optimization (every internal node is a Coq pair). *)

Module ElementTree <: ELEMENT.

  Definition t (A : Type) : Type := { l : nat & xpow A l }.

  Definition to_list (A : Type) (e : t A) : list A :=
    @xflat A (projT1 e) (projT2 e).

  Definition level (A : Type) (e : t A) : nat := projT1 e.

  Definition base (A : Type) (a : A) : t A := existT _ 0 a.

  (** [pair x y e] constructs a level-(S l) element from two level-l elements. *)
  Definition pair (A : Type) (x y : t A) (e : level A x = level A y) : t A.
  Proof.
    refine (existT _ (S (level A x)) _).
    destruct x as [lx px], y as [ly py]. cbn in *.
    subst ly.   (* level x = level y means lx = ly *)
    exact (px, py).
  Defined.

  Definition unpair (A : Type) (e : t A) : option (t A * t A) :=
    match e with
    | existT 0 _ => None
    | existT (S l') p =>
        match p with
        | (x, y) => Some (existT (xpow A) l' x, existT (xpow A) l' y)
        end
    end.

  Lemma to_list_base : forall A (a : A), to_list A (base A a) = [a].
  Proof. intros. unfold to_list, base. cbn. reflexivity. Qed.

  Lemma level_base : forall A (a : A), level A (base A a) = 0.
  Proof. intros. reflexivity. Qed.

  Lemma level_pair : forall A (x y : t A) (e : level A x = level A y),
      level A (pair A x y e) = S (level A x).
  Proof. intros. unfold level, pair. cbn. reflexivity. Qed.

  Lemma to_list_pair : forall A (x y : t A) (e : level A x = level A y),
      to_list A (pair A x y e) = to_list A x ++ to_list A y.
  Proof.
    intros A x y eq. unfold to_list, pair, level in *.
    destruct x as [lx px], y as [ly py]. cbn in eq. subst ly.
    cbn. reflexivity.
  Qed.

  Lemma unpair_base : forall A (a : A), unpair A (base A a) = None.
  Proof. intros. reflexivity. Qed.

  Lemma unpair_pair : forall A (x y : t A) (e : level A x = level A y),
      unpair A (pair A x y e) = Some (x, y).
  Proof.
    intros A x y eq. unfold unpair, pair, level in *.
    destruct x as [lx px], y as [ly py]. cbn in eq. subst ly.
    cbn. reflexivity.
  Qed.

  (** ** [unpair_to_list]: unpair preserves the flatten relation.

      If [unpair p = Some (x, y)], then the flattened sequence of [p]
      is the concatenation of those of [x] and [y]. *)
  Lemma unpair_to_list :
    forall (A : Type) (p x y : t A),
      unpair A p = Some (x, y) ->
      to_list A p = to_list A x ++ to_list A y.
  Proof.
    intros A p x y H.
    destruct p as [lp pp].
    unfold unpair, to_list in *. cbn in H.
    destruct lp as [|lp']; [discriminate|].
    destruct pp as [a b].
    inversion H; subst x y; clear H.
    cbn. reflexivity.
  Qed.

  (** [unpair] returns [Some] iff the level is non-zero, and the children
      are at the predecessor level. *)
  Lemma unpair_level :
    forall (A : Type) (p x y : t A),
      unpair A p = Some (x, y) ->
      level A p = S (level A x) /\ level A x = level A y.
  Proof.
    intros A p x y H.
    destruct p as [lp pp].
    unfold unpair, level in *. cbn in H.
    destruct lp as [|lp']; [discriminate|].
    destruct pp as [a b].
    inversion H; subst x y; clear H. cbn; auto.
  Qed.

End ElementTree.

(** ** [ElementFlat]: small-arity-flattened instance.

    Same observable behavior as [ElementTree], but at small levels uses
    multi-arity constructors so the extracted OCaml gets fewer
    allocations:

    {v
        level 0:  XF0 a              -- 1 block (1 field)
        level 1:  XF1 a b            -- 1 block (2 fields)
        level 2:  XF2 a b c d        -- 1 block (4 fields)   <-- key win
        level 3+: XFP x y            -- 1 block (2 fields, recursive)
    v}

    A nested-pair representation at level 2 is `((a,b),(c,d))` = 3
    blocks (2 inner pairs of size 2 + 1 outer of size 2 = 9 words
    total). The flat XF2 is 1 block of size 4 = 5 words. ~45% saving
    at level 2, where most of a typical deque's working set sits.

    The trick: we don't index the inductive by level. Instead, pair
    dispatches on the input shape. The ELEMENT axioms hold because
    [level] and [to_list] are defined to agree with the structural
    interpretation of each constructor. *)

Module ElementFlat <: ELEMENT.

  Inductive xflat_t (A : Type) : Type :=
  | XF0 : A -> xflat_t A
  | XF1 : A -> A -> xflat_t A
  | XF2 : A -> A -> A -> A -> xflat_t A
  | XFP : xflat_t A -> xflat_t A -> xflat_t A.

  Arguments XF0 {A} _.
  Arguments XF1 {A} _ _.
  Arguments XF2 {A} _ _ _ _.
  Arguments XFP {A} _ _.

  Definition t (A : Type) : Type := xflat_t A.

  Fixpoint level (A : Type) (x : t A) : nat :=
    match x with
    | XF0 _       => 0
    | XF1 _ _     => 1
    | XF2 _ _ _ _ => 2
    | XFP a _     => S (level A a)
    end.

  Fixpoint to_list (A : Type) (x : t A) : list A :=
    match x with
    | XF0 a           => [a]
    | XF1 a b         => [a; b]
    | XF2 a b c d     => [a; b; c; d]
    | XFP l r         => to_list A l ++ to_list A r
    end.

  Definition base (A : Type) (a : A) : t A := XF0 a.

  (** [pair_xf x y]: dispatch on input shape to flatten when possible.

      For ill-shaped inputs (different levels) we fall back to [XFP];
      [pair] is only meant to be called when the levels match (the
      ELEMENT contract via [e : level x = level y]). The axioms hold
      uniformly. *)
  Definition pair_xf (A : Type) (x y : t A) : t A :=
    match x, y with
    | XF0 a, XF0 b                         => XF1 a b
    | XF1 a b, XF1 c d                     => XF2 a b c d
    | _, _                                 => XFP x y
    end.

  Definition pair (A : Type) (x y : t A) (_ : level A x = level A y) : t A :=
    pair_xf A x y.

  (** [unpair] guards [XFP] with a level-equality check so the
      [unpair_level] lemma — used by callers — holds unconditionally.
      In practice [XFP] is only constructed via [pair_xf] with matching
      levels, so the guard always passes. *)
  Definition unpair (A : Type) (x : t A) : option (t A * t A) :=
    match x with
    | XF0 _           => None
    | XF1 a b         => Some (XF0 a, XF0 b)
    | XF2 a b c d     => Some (XF1 a b, XF1 c d)
    | XFP l r         =>
        match Nat.eq_dec (level A l) (level A r) with
        | left _  => Some (l, r)
        | right _ => None
        end
    end.

  Lemma to_list_base : forall A (a : A), to_list A (base A a) = [a].
  Proof. intros. reflexivity. Qed.

  Lemma level_base : forall A (a : A), level A (base A a) = 0.
  Proof. intros. reflexivity. Qed.

  Lemma level_pair : forall A (x y : t A) (e : level A x = level A y),
      level A (pair A x y e) = S (level A x).
  Proof.
    intros A x y e. unfold pair, pair_xf.
    destruct x, y; cbn in e; try discriminate; reflexivity.
  Qed.

  Lemma to_list_pair : forall A (x y : t A) (e : level A x = level A y),
      to_list A (pair A x y e) = to_list A x ++ to_list A y.
  Proof.
    intros A x y e. unfold pair, pair_xf.
    destruct x, y; cbn in e; try discriminate; reflexivity.
  Qed.

  Lemma unpair_base : forall A (a : A), unpair A (base A a) = None.
  Proof. intros. reflexivity. Qed.

  Lemma unpair_pair : forall A (x y : t A) (e : level A x = level A y),
      unpair A (pair A x y e) = Some (x, y).
  Proof.
    intros A x y e. unfold pair, pair_xf, unpair.
    destruct x, y; cbn in e; try discriminate; try reflexivity;
      (destruct (Nat.eq_dec _ _) as [|ne]; [reflexivity | exfalso; apply ne; cbn; exact e]).
  Qed.

  (** Same dual lemma as on [ElementTree]: a successful unpair flattens
      as the concat of its components. *)
  Lemma unpair_to_list :
    forall (A : Type) (p x y : t A),
      unpair A p = Some (x, y) ->
      to_list A p = to_list A x ++ to_list A y.
  Proof.
    intros A p x y H.
    destruct p; cbn in H; try discriminate.
    - inversion H; reflexivity.
    - inversion H. cbn. reflexivity.
    - destruct (Nat.eq_dec _ _) as [|]; [|discriminate].
      inversion H. cbn. reflexivity.
  Qed.

  (** A successful unpair returns children at level [l - 1] when the
      input is at level [l > 0], and the two children share a level. *)
  Lemma unpair_level :
    forall (A : Type) (p x y : t A),
      unpair A p = Some (x, y) ->
      level A p = S (level A x) /\ level A x = level A y.
  Proof.
    intros A p x y H.
    destruct p; cbn in H; try discriminate.
    - inversion H; subst; clear H. cbn; auto.
    - inversion H; subst; clear H. cbn; auto.
    - destruct (Nat.eq_dec _ _) as [Heq|]; [|discriminate].
      inversion H; subst; clear H. cbn. split; [reflexivity | exact Heq].
  Qed.

End ElementFlat.

(** ** Useful derived functions for any [ELEMENT].

    These don't depend on a specific instance — they wrap calls with the
    level-equality decision. *)

Module ElementOps (E : ELEMENT).

  (** Decide level equality at runtime.  Returns [Some] iff levels match. *)
  Definition pair_safe (A : Type) (x y : E.t A) : option (E.t A) :=
    match Nat.eq_dec (E.level A x) (E.level A y) with
    | left e => Some (E.pair A x y e)
    | right _ => None
    end.

  Lemma pair_safe_some_iff : forall A (x y : E.t A),
      (exists r, pair_safe A x y = Some r) <-> E.level A x = E.level A y.
  Proof.
    intros A x y. unfold pair_safe.
    destruct (Nat.eq_dec (E.level A x) (E.level A y)) as [e | ne]; split.
    - intros _. exact e.
    - intros _. eauto.
    - intros [r H]. discriminate.
    - intros e. contradiction.
  Qed.

  Lemma pair_safe_to_list : forall A (x y : E.t A) (r : E.t A),
      pair_safe A x y = Some r ->
      E.to_list A r = E.to_list A x ++ E.to_list A y.
  Proof.
    intros A x y r H. unfold pair_safe in H.
    destruct (Nat.eq_dec (E.level A x) (E.level A y)) as [e|]; [|discriminate].
    inversion H; subst.
    apply E.to_list_pair.
  Qed.

  Lemma pair_safe_level : forall A (x y : E.t A) (r : E.t A),
      pair_safe A x y = Some r ->
      E.level A r = S (E.level A x).
  Proof.
    intros A x y r H. unfold pair_safe in H.
    destruct (Nat.eq_dec (E.level A x) (E.level A y)) as [e|]; [|discriminate].
    inversion H; subst.
    apply E.level_pair.
  Qed.

End ElementOps.
