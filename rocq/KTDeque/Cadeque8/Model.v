(** * Module: KTDeque.Cadeque8.Model — strict WC O(1) catenable deque
      via the KT99 §6 head/middle/tail mechanism.

    Cadeque7 achieves WC O(1) push / inject / concat structurally,
    but pop/eject after a concat fall back to a list-rebuild — that's
    amortized, not strict-WC.  Under persistent forking the fallback
    re-triggers and the amortization breaks.

    Cadeque8 uses the §6 design directly:

    - A [K8Triple] has a small head buffer, a middle "spine" deque of
      [Stored8] cells, and a small tail buffer.
    - Push enters the head buffer; inject enters the tail buffer.
    - Concat wraps the boundary as a [StoredBig8] cell and injects
      it into the middle (one [buf6_inject] — WC O(1) via the
      Phase 5d shim that routes through [KTDeque.kt2_*]).
    - Pop drains the head buffer; when the head empties, it pops the
      leftmost stored cell from the middle and unfolds it into the
      new head — constant work per pop because stored cells'
      prefix/suffix buffers are bounded.

    The middle is [Buf6 (Stored8 X)], i.e. a [Buf6] whose elements are
    [Stored8] cells.  At extraction time the [Buf6] type maps to the
    [KCadequeShim.buf6] record which holds a certified [KTDeque.kChain]
    — so middle push / inject / pop / eject are all WC O(1) per call.

    Buffers carrying user data are still [Buf6 (KElem8 X)] backed by
    the same shim — push / inject / pop / eject on individual buffers
    is WC O(1) (Phase 5d).

    The strict positivity check accepts this design: [Buf6] is a
    record over [list X] (singleton inductive, positive in X), so
    [Buf6 (Stored8 X)] and [Buf6 (KElem8 X)] are both positive uses
    of the mutual parameters [Stored8] and [KElem8]. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.

(** ** The mutually-recursive type family.

    Three types: [KElem8] (buffer element), [Stored8] (packed cell),
    [KCadeque8] (top-level catenable deque). *)

Inductive KElem8 (X : Type) : Type :=
  | XBase8   : X -> KElem8 X
  | XStored8 : Stored8 X -> KElem8 X

with Stored8 (X : Type) : Type :=
  | StoredSmall8 : Buf6 (KElem8 X) -> Stored8 X
  | StoredBig8   : Buf6 (KElem8 X) ->            (* prefix      *)
                   KCadeque8 X ->                 (* subcadeque  *)
                   Buf6 (KElem8 X) ->            (* suffix      *)
                   Stored8 X

with KCadeque8 (X : Type) : Type :=
  | K8Empty  : KCadeque8 X
  | K8Simple : Buf6 (KElem8 X) -> KCadeque8 X
  | K8Triple : Buf6 (KElem8 X) ->                (* head buffer       *)
               Buf6 (Stored8 X) ->                (* middle spine deque *)
               Buf6 (KElem8 X) ->                (* tail buffer       *)
               KCadeque8 X.

Arguments XBase8        {X} _.
Arguments XStored8      {X} _.
Arguments StoredSmall8  {X} _.
Arguments StoredBig8    {X} _ _ _.
Arguments K8Empty       {X}.
Arguments K8Simple      {X} _.
Arguments K8Triple      {X} _ _ _.

(** ** Distinguished values. *)

Definition kcad8_empty {X : Type} : KCadeque8 X := K8Empty.

Definition kcad8_singleton {X : Type} (x : X) : KCadeque8 X :=
  K8Simple (mkBuf6 [XBase8 x]).

(** ** Sequence semantics: flatten the structure to a [list X]. *)

Section to_list8.
  Variable X : Type.

  (* The mutual fixpoint flattens [KElem8] / [Stored8] / [KCadeque8].
     Following the Cadeque7 pattern: inline [fix go] for buffer
     traversal because Coq's mutual guard checker doesn't accept a
     factored buffer-flattener as a cross-mutual call. *)

  Fixpoint kelem8_to_list (e : KElem8 X) {struct e} : list X :=
    match e with
    | XBase8 x   => [x]
    | XStored8 s => stored8_to_list s
    end

  with stored8_to_list (s : Stored8 X) {struct s} : list X :=
    match s with
    | StoredSmall8 b =>
        (fix go (l : list (KElem8 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem8_to_list e ++ go es
           end) (buf6_elems b)
    | StoredBig8 pre c suf =>
        (fix go (l : list (KElem8 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem8_to_list e ++ go es
           end) (buf6_elems pre)
        ++ kcad8_to_list c
        ++ (fix go (l : list (KElem8 X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem8_to_list e ++ go es
              end) (buf6_elems suf)
    end

  with kcad8_to_list (k : KCadeque8 X) {struct k} : list X :=
    match k with
    | K8Empty    => []
    | K8Simple b =>
        (fix go (l : list (KElem8 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem8_to_list e ++ go es
           end) (buf6_elems b)
    | K8Triple h m t =>
        (fix go (l : list (KElem8 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem8_to_list e ++ go es
           end) (buf6_elems h)
        ++ (fix go_m (l : list (Stored8 X)) : list X :=
              match l with
              | []      => []
              | s :: ss => stored8_to_list s ++ go_m ss
              end) (buf6_elems m)
        ++ (fix go (l : list (KElem8 X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem8_to_list e ++ go es
              end) (buf6_elems t)
    end.

End to_list8.

Arguments kelem8_to_list   {X} _.
Arguments stored8_to_list  {X} _.
Arguments kcad8_to_list    {X} _.

(** ** Sanity checks. *)

Example empty_to_list8 :
  forall A : Type, kcad8_to_list (@kcad8_empty A) = [].
Proof. intros; reflexivity. Qed.

Example singleton_to_list8 :
  forall (A : Type) (x : A), kcad8_to_list (kcad8_singleton x) = [x].
Proof. intros; reflexivity. Qed.

Example triple_to_list8 :
  forall (A : Type) (a b : A),
    kcad8_to_list (K8Triple (mkBuf6 [XBase8 a])
                            (mkBuf6 [])
                            (mkBuf6 [XBase8 b]))
    = [a; b].
Proof. intros; reflexivity. Qed.
