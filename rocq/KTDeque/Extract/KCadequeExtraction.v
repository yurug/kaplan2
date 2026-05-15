(** * Module: KTDeque.Extract.KCadequeExtraction — OCaml extraction
      of the Cadeque7 catenable cadeque.

    Produces [kCadeque.ml] with the public API:
      kcad_empty, kcad_singleton,
      kcad_push, kcad_inject, kcad_pop, kcad_eject, kcad_concat,
      kcad_to_list.

    This is the Phase 1-4 naive version (push/inject grow buffers
    without bound; pop/eject are O(n) via to_list-rebuild).  WC O(1)
    cascade machinery + structural pop/eject is deferred to later phases.
*)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque7  Require Import Model PushInject PopEject Concat.

Set Extraction Output Directory "kcadeque_extracted".

Extraction Language OCaml.

(** ** Note on WC O(1) at the buffer level

    [Buf6] is a Coq record (singleton inductive) and Coq's extraction
    aggressively collapses it to its underlying [list X], regardless
    of [Extract Inductive Buf6 => "KCadequeShim.buf6" ...] directives.
    Attempted overrides do not take effect — Rocq 9.1.1's extraction
    treats Buf6 as a transparent wrapper.

    Consequence: the OCaml extracted [buf6_inject] / [buf6_eject]
    remain O(n) per call (list-append / list-reverse), and the
    [kCadequeShim.ml] module is unused in the current pipeline.

    The Cadeque7 Coq code has been refactored to use [buf6_elems b]
    projection instead of [match b with mkBuf6 xs => ...] destructure
    — this is the prerequisite for a working type-override.  The
    next step (if a Coq extraction-override path is found) would be
    to make [Extract Inductive] actually take effect for record
    types in Rocq 9.x.

    Alternative path: rewrite Cadeque7's Coq Model.v using a
    level-indexed [Stored A : nat -> Type] mutual family with
    [KChain (Stored A l)] as the buffer type at each level —
    Viennot's certified approach.  Substantial Coq work (~1 day). *)

Extraction "kCadeque.ml"
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
  (* KCadeque types. *)
  KElem
  Stored
  KCadeque
  Packet
  Body
  Node
  RegularityTag
  kcad_empty
  kcad_singleton
  kcad_to_list
  (* Operations. *)
  kcad_push
  kcad_inject
  kcad_pop
  kcad_eject
  kcad_concat
  kcad_from_list.
