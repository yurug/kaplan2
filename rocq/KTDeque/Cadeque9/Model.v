(** * Module: KTDeque.Cadeque9.Model — paper-faithful KT99 §6
      catenable deque.

    Cadeque9 differs from Cadeque8 in two structural ways that
    matter for strict WC O(1):

    1. **No nested sub-deque inside stored cells.**  Where Cadeque8
       has [StoredBig8 _ (KCadeque8 X) _], Cadeque9 has
       [StoredBig9 _ (Buf6 (Stored9 X)) _].  The middle of a
       StoredBig9 is a CHAIN of more stored cells (just a buf6),
       not a recursive deque.  This matches Viennot's
       formalization (`Big {l qp qs ...} : prefix' ... -> chain ... ->
       suffix' ...`).

    2. **Size lower bounds enforced extrinsically** (in [WFStrong.v]):
       node boundary buffers have size ≥ 5, stored cell prefixes
       and suffixes have size ≥ 3.  Cadeque8 only requires ≥ 1.
       The stronger bounds are what makes [kcad9_concat] trivially
       O(1) and rebalance always able to refill the boundary.

    These two changes together close the (T+T) eject WC O(1) bug
    that's intractable in Cadeque8.  See
    [kb/spec/cadeque9-paper-faithful-plan.md].

    ## Sequence semantics

    Three types, with the mutual fixpoint flattening
    [KElem9] / [Stored9] (KCadeque9 is non-mutually-recursive
    because it doesn't appear inside Stored9 anymore — that's the
    structural change).  The inline [fix go] pattern follows
    Cadeque8/Model.v for guard-checker compatibility. *)

From Stdlib Require Import List.
Import ListNotations.

From KTDeque.Buffer6 Require Import SizedBuffer.

(** ** The mutually-recursive type family.

    Two mutually-recursive types: [KElem9] (buffer element) and
    [Stored9] (packed cell).  [KCadeque9] is a separate type
    parametrised by them (no mutual recursion — the structural
    win over Cadeque8). *)

Inductive KElem9 (X : Type) : Type :=
  | XBase9   : X -> KElem9 X
  | XStored9 : Stored9 X -> KElem9 X

with Stored9 (X : Type) : Type :=
  | StoredSmall9 : Buf6 (KElem9 X) -> Stored9 X
  | StoredBig9   : Buf6 (KElem9 X) ->            (* prefix      *)
                   Buf6 (Stored9 X) ->            (* sm = stored chain *)
                   Buf6 (KElem9 X) ->            (* suffix      *)
                   Stored9 X
  | StoredMiddle9 : Buf6 (Stored9 X) ->           (* explicit middle chain *)
                    Stored9 X.

Inductive KCadeque9 (X : Type) : Type :=
  | K9Empty  : KCadeque9 X
  | K9Simple : Buf6 (KElem9 X) -> KCadeque9 X
  | K9Triple : Buf6 (KElem9 X) ->                (* head boundary       *)
               Buf6 (Stored9 X) ->                (* middle spine deque   *)
               Buf6 (KElem9 X) ->                (* tail boundary       *)
               KCadeque9 X.

Arguments XBase9        {X} _.
Arguments XStored9      {X} _.
Arguments StoredSmall9  {X} _.
Arguments StoredBig9    {X} _ _ _.
Arguments StoredMiddle9 {X} _.
Arguments K9Empty       {X}.
Arguments K9Simple      {X} _.
Arguments K9Triple      {X} _ _ _.

(** ** Distinguished values. *)

Definition kcad9_empty {X : Type} : KCadeque9 X := K9Empty.

Definition kcad9_singleton {X : Type} (x : X) : KCadeque9 X :=
  K9Simple (mkBuf6 [XBase9 x]).

Definition stored9_middle {X : Type} (sm : Buf6 (Stored9 X)) : Stored9 X :=
  StoredMiddle9 sm.

(** ** Sequence semantics: flatten the structure to a [list X]. *)

Section to_list9.
  Variable X : Type.

  (* The mutual fixpoint flattens [KElem9] and [Stored9].  Stored9
     references Buf6 (Stored9 X) — a chain of stored cells — which
     we traverse with an inline [fix go_sm].  Stored9 also references
     Buf6 (KElem9 X) for prefix/suffix; that's traversed with another
     inline [fix go].  No nested KCadeque9 (the key structural
     difference from Cadeque8). *)

  Fixpoint kelem9_to_list (e : KElem9 X) {struct e} : list X :=
    match e with
    | XBase9 x   => [x]
    | XStored9 s => stored9_to_list s
    end

  with stored9_to_list (s : Stored9 X) {struct s} : list X :=
    match s with
    | StoredSmall9 b =>
        (fix go (l : list (KElem9 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem9_to_list e ++ go es
           end) (buf6_elems b)
    | StoredBig9 pre sm suf =>
        (fix go (l : list (KElem9 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem9_to_list e ++ go es
           end) (buf6_elems pre)
        ++ (fix go_sm (l : list (Stored9 X)) : list X :=
              match l with
              | []      => []
              | s' :: ss => stored9_to_list s' ++ go_sm ss
              end) (buf6_elems sm)
        ++ (fix go (l : list (KElem9 X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem9_to_list e ++ go es
              end) (buf6_elems suf)
    | StoredMiddle9 sm =>
        (fix go_sm (l : list (Stored9 X)) : list X :=
           match l with
           | []      => []
           | s' :: ss => stored9_to_list s' ++ go_sm ss
           end) (buf6_elems sm)
    end.

  (** [kcad9_to_list]: NOT in the mutual recursion (since Stored9
      doesn't contain KCadeque9 anymore).  Defined as a separate
      function that uses [kelem9_to_list] and [stored9_to_list]. *)
  Definition kcad9_to_list (k : KCadeque9 X) : list X :=
    match k with
    | K9Empty    => []
    | K9Simple b =>
        (fix go (l : list (KElem9 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem9_to_list e ++ go es
           end) (buf6_elems b)
    | K9Triple h m t =>
        (fix go (l : list (KElem9 X)) : list X :=
           match l with
           | []      => []
           | e :: es => kelem9_to_list e ++ go es
           end) (buf6_elems h)
        ++ (fix go_m (l : list (Stored9 X)) : list X :=
              match l with
              | []      => []
              | s :: ss => stored9_to_list s ++ go_m ss
              end) (buf6_elems m)
        ++ (fix go (l : list (KElem9 X)) : list X :=
              match l with
              | []      => []
              | e :: es => kelem9_to_list e ++ go es
              end) (buf6_elems t)
    end.

End to_list9.

Arguments kelem9_to_list   {X} _.
Arguments stored9_to_list  {X} _.
Arguments kcad9_to_list    {X} _.

(** ** Sanity checks. *)

Example empty_to_list9 :
  forall A : Type, kcad9_to_list (@kcad9_empty A) = [].
Proof. intros; reflexivity. Qed.

Example singleton_to_list9 :
  forall (A : Type) (x : A), kcad9_to_list (kcad9_singleton x) = [x].
Proof. intros; reflexivity. Qed.

Example storedsmall9_flat :
  forall (X : Type) (x y : X),
    stored9_to_list (StoredSmall9 (mkBuf6 [XBase9 x; XBase9 y])) = [x; y].
Proof. intros; reflexivity. Qed.

Example storedbig9_flat :
  forall (X : Type) (a b c d : X),
    stored9_to_list
      (StoredBig9 (mkBuf6 [XBase9 a])
                  (mkBuf6 [StoredSmall9 (mkBuf6 [XBase9 b; XBase9 c])])
                  (mkBuf6 [XBase9 d]))
    = [a; b; c; d].
Proof. intros; reflexivity. Qed.

Example storedmiddle9_flat :
  forall (X : Type) (a b c : X),
    stored9_to_list
      (StoredMiddle9
         (mkBuf6
            [StoredSmall9 (mkBuf6 [XBase9 a; XBase9 b]);
             StoredSmall9 (mkBuf6 [XBase9 c])]))
    = [a; b; c].
Proof. intros; reflexivity. Qed.

(** A K9Triple flattens as h ++ (cells of m, each flattened) ++ t. *)
Example k9triple_flat :
  forall (X : Type) (a b c d e f : X),
    kcad9_to_list
      (K9Triple (mkBuf6 [XBase9 a; XBase9 b])
                (mkBuf6 [StoredSmall9 (mkBuf6 [XBase9 c; XBase9 d])])
                (mkBuf6 [XBase9 e; XBase9 f]))
    = [a; b; c; d; e; f].
Proof. intros; reflexivity. Qed.

(** ** Demonstration of the structural advantage over Cadeque8.

    [StoredBig9] keeps the child middle as a flat [Buf6 (Stored9 X)]
    rather than a nested catenable deque.  The abstract [Ops.v] concat
    still uses [buf6_concat] for its simple proof surface; the
    OCaml-shaped constant-work bridge is modeled separately in
    [Normalize.v]. *)
