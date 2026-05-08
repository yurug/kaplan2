(** * Module: KTDeque.Cadeque6.Correctness -- re-export bundle.

    Single import point for the abstract Cadeque6 spec.

    A file that needs the Cadeque6 types and the abstract
    operations can write

      [From KTDeque.Cadeque6 Require Import Correctness.]

    and have the [Triple] / [Cadeque] / [Stored] types, the
    flattening machinery, and the abstract operations + their
    proved sequence laws all in scope.

    This file does not introduce any new definitions or theorems;
    it is purely a convenience.

    ## Cross-references

    - [Cadeque6/Model.v]            -- types + flattening.
    - [Cadeque6/OpsAbstract.v]      -- operations + sequence laws.
    - [kb/spec/why-catenable.md]    -- intuition layer.
*)

From KTDeque.Cadeque6 Require Export Model OpsAbstract.
