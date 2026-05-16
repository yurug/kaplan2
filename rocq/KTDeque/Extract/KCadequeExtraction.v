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

(** ** WC O(1) at the buffer level via [KCadequeShim].

    [Buf6] is a Coq record (singleton inductive).  By default Rocq's
    extraction collapses it to its underlying [list X] type, giving
    O(n) push/inject/eject.

    To achieve WC O(1), we override [Buf6] with an opaque OCaml type
    that wraps a certified [KTDeque.kChain].  Each buffer op is also
    overridden via [Extract Constant] to route through the shim's
    [kt2_*] family (proven WC O(1) in [DequePtr/OpsKTSeq.v]).

    Prerequisite: the Cadeque7 Coq code uses the [buf6_elems b]
    projection everywhere instead of [match b with mkBuf6 xs => ...]
    destructure — so the extracted OCaml uses functional projection
    rather than the singleton-collapsed pattern-match.

    The case-callback in [Extract Inductive] handles the residual
    destructures (if any): it projects via [KCadequeShim.buf6_elems]
    before applying the consumer. *)

(* Type override. *)
Extract Inductive Buf6 => "KCadequeShim.buf6"
  [ "KCadequeShim.mkBuf6" ]
  "(fun fmkbuf6 b -> fmkbuf6 (KCadequeShim.buf6_elems b))".

(* Op overrides — route through the shim's kt2_* WC O(1) family. *)
Extract Constant buf6_elems     => "KCadequeShim.buf6_elems".
Extract Constant buf6_to_list   => "KCadequeShim.buf6_to_list".
Extract Constant buf6_size      => "KCadequeShim.buf6_size".
Extract Constant buf6_empty     => "KCadequeShim.buf6_empty".
Extract Constant buf6_singleton => "KCadequeShim.buf6_singleton".
Extract Constant buf6_push      => "KCadequeShim.buf6_push".
Extract Constant buf6_inject    => "KCadequeShim.buf6_inject".
Extract Constant buf6_pop       => "KCadequeShim.buf6_pop".
Extract Constant buf6_eject     => "KCadequeShim.buf6_eject".

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
  kcad_to_list_fast
  (* Operations. *)
  kcad_push
  kcad_inject
  kcad_pop
  kcad_eject
  kcad_concat
  kcad_from_list.
