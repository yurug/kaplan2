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
