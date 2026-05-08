(** * Module: KTDeque.Buffer6.Correctness -- re-export bundle for Buf6.

    Single import point for the abstract [Buf6] specification.  A
    file that needs the [Buf6] type, basic ops, and small-move
    helpers can write

      [From KTDeque.Buffer6 Require Import Correctness.]

    and have everything in scope.  This file does not introduce any
    new definitions or theorems; it is purely a convenience.

    For files that need only the type and basic ops, importing
    [SizedBuffer] alone is lighter.  For files that also need the
    small-move primitives ([buf6_take_first2], [buf6_concat], etc.),
    [Correctness] picks up both.

    ## Cross-references

    - [Buffer6/SizedBuffer.v]   -- the [Buf6] type and basic ops.
    - [Buffer6/SmallMoves.v]    -- the take/concat/halve primitives.
*)

From KTDeque.Buffer6 Require Export SizedBuffer SmallMoves.
