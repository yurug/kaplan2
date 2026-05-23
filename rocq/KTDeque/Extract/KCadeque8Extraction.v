(** * Module: KTDeque.Extract.KCadeque8Extraction — OCaml extraction
      of the Cadeque8 strict-WC O(1) catenable cadeque. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque8  Require Import Model Ops OpsFast.

Set Extraction Output Directory "kcadeque8_extracted".

Extraction Language OCaml.

(* Buf6 override — same shim as KCadequeExtraction.v. *)
Extract Inductive Buf6 => "KCadequeShim.buf6"
  [ "KCadequeShim.mkBuf6" ]
  "(fun fmkbuf6 b -> fmkbuf6 (KCadequeShim.buf6_elems b))".

Extract Constant buf6_elems     => "KCadequeShim.buf6_elems".
Extract Constant buf6_to_list   => "KCadequeShim.buf6_to_list".
Extract Constant buf6_size      => "KCadequeShim.buf6_size".
Extract Constant buf6_empty     => "KCadequeShim.buf6_empty".
Extract Constant buf6_singleton => "KCadequeShim.buf6_singleton".
Extract Constant buf6_push      => "KCadequeShim.buf6_push".
Extract Constant buf6_inject    => "KCadequeShim.buf6_inject".
Extract Constant buf6_pop       => "KCadequeShim.buf6_pop".
Extract Constant buf6_eject     => "KCadequeShim.buf6_eject".
Extract Constant buf6_is_empty  => "KCadequeShim.buf6_is_empty".

(* NB: [kcad8_push_inline] / [kcad8_inject_inline] in [Cadeque8/OpsFast.v]
   are defined as definitional aliases of the [_fast] variants, so
   the extracted versions are [let kcad8_push_inline = kcad8_push_fast].
   The faster, hand-fused implementations live in [KCadeque8Inline.ml]
   (a separate hand-written module that depends on [KCadeque8] for
   type definitions — making it an [Extract Constant] override here
   would create a module cycle).  Bench / consumer code should call
   [KCadeque8Inline.kcad8_push_inline] directly when the fused hot
   path is desired. *)

Extraction "kCadeque8.ml"
  Buf6
  buf6_empty buf6_singleton buf6_push buf6_inject buf6_pop buf6_eject
  buf6_size buf6_to_list buf6_elems
  KElem8 Stored8 KCadeque8
  kcad8_empty
  kcad8_singleton
  kcad8_to_list
  kcad8_push
  kcad8_inject
  kcad8_pop
  kcad8_eject
  kcad8_concat
  kcad8_from_list
  (* OpsFast — extraction-friendly variants (kt4-style flat sum types). *)
  pop_result8 eject_result8
  kcad8_push_fast
  kcad8_inject_fast
  kcad8_pop_fast
  kcad8_eject_fast
  kcad8_concat_fast
  (* Inline variants — see [KCadeque8Inline.ml] for the OCaml override. *)
  kcad8_push_inline
  kcad8_inject_inline.
