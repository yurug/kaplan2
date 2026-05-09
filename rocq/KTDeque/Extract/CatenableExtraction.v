(** * Module: KTDeque.Extract.CatenableExtraction -- OCaml extraction
      of the Section-6 catenable cadeque (Cadeque6).

    Extracts the abstract catenable cadeque developed in
    [rocq/KTDeque/Cadeque6/].  The output is a single OCaml module
    [KTCatenableDeque] (file [kTCatenableDeque.ml]) containing:

    - The data types: [buf6], [triple], [cadeque], [stored].
    - The abstract operations: [cad_push] / [cad_inject] / [cad_pop] /
      [cad_eject] / [cad_concat] / [cad_singleton] / [cad_is_empty] /
      [cad_rev] / [cad_size] / [cad_to_list_base].
    - The operational variants: [cad_push_op] / [cad_inject_op] /
      [cad_pop_op] / [cad_eject_op] / [cad_concat_op].
    - The fully regularity-preserving variants: [cad_pop_op_full] /
      [cad_eject_op_full] / [cad_concat_op_full] /
      [cad_normalize].

    The extraction is independent of [KTDeque.Extract.Extraction.v]
    (which extracts the Section-4 [DequePtr/] development).  The two
    OCaml modules ship side-by-side in the [ktdeque] opam package so
    a client can pick whichever it needs:

    - [KTDeque]            -- non-catenable, WC O(1) per op.
    - [KTCatenableDeque]   -- catenable, abstract spec
                              (correctness only; cost spec is the
                              target of Phase 4 of
                              [kb/plan-catenable.md]).

    ## Cost note

    The extracted [cad_pop_op_full], [cad_eject_op_full], and
    [cad_concat_op_full] use [cad_normalize] (rebuild via
    [cad_from_list_op]), which is [O(n)] in the abstract sequence
    length.  The spec layer (this extraction) is for correctness;
    cost-bounded WC O(1) variants require the level-typed cascade
    spelled out in [kb/plan-catenable.md] under "Phase 4".

    ## Cross-references

    - [Cadeque6/Model.v]              -- types.
    - [Cadeque6/OpsAbstract.v]        -- abstract ops + sequence laws.
    - [Cadeque6/Repair.v]             -- operational + _full ops +
                                          full preservation theorems.
    - [Public/CadequeInterface.v]     -- the [CADEQUE] module type +
                                          [RegularCadeque] implementation
                                          we are extracting.
    - [kb/plan-catenable.md]          -- Phase 6 of the catenable plan.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Buffer6 Require Import SizedBuffer SmallMoves.
From KTDeque.Cadeque6 Require Import Model OpsAbstract Repair.

Set Extraction Output Directory "kt_catenable_extracted".

Extraction Language OCaml.

Extraction "kTCatenableDeque.ml"
  (* Buffer foundation. *)
  Buf6
  buf6_empty
  buf6_singleton
  buf6_push
  buf6_inject
  buf6_pop
  buf6_eject
  buf6_size
  buf6_to_list
  buf6_concat
  (* Cadeque types. *)
  Triple
  Cadeque
  Stored
  TripleKind
  cad_empty
  cad_singleton_only
  cad_to_list_base
  triple_kind
  (* Abstract operations + sequence semantics. *)
  cad_push
  cad_inject
  cad_pop
  cad_eject
  cad_concat
  cad_singleton
  cad_is_empty
  cad_rev
  cad_size
  cad_from_list
  cad_fold_left
  cad_fold_right
  (* Operational variants (partial regularity preservation). *)
  cad_push_op
  cad_inject_op
  cad_pop_op
  cad_eject_op
  cad_concat_op
  (* Full regularity-preserving variants (composed with cad_normalize). *)
  cad_normalize
  cad_from_list_op
  cad_pop_op_full
  cad_eject_op_full
  cad_concat_op_full.
