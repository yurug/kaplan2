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

(** ** Note on WC O(1)

    The current extraction keeps the default mapping
    [Buf6 X => 'a list], which makes [buf6_inject] and [buf6_eject]
    O(n) per op via [xs ++ [x]] / [List.rev xs].  This violates
    the project's WC O(1) requirement on those two ops at the
    buffer level.

    The right fix (Phase 5b proper) is to replace [Buf6] in
    Cadeque7's Coq types with [KChain] from
    [rocq/KTDeque/DequePtr/OpsKT.v] — the certified WC O(1) deque.
    That's a Coq-side rewrite of Model.v's type definitions, plus
    re-proofs of the seq lemmas.  Effort: ~3 hours of focused work.

    Tried-and-failed alternative: extraction override mapping
    [Buf6 X => KCadequeShim.buf6] (= kChain) breaks because the
    extracted Coq code uses [let mkBuf6 xs = b in ...] destructure
    patterns that don't translate cleanly when [buf6] isn't a
    variant.  Coq's [Extract Inductive] case-callback didn't take
    effect for the record-style destructure.  Logged at
    [kb/spec/kcadeque-design.md]. *)

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
