(** * Module: KTDeque.Extract.KCadeque9Extraction — OCaml extraction
      of the Cadeque9 paper-faithful KT99 §6 catenable cadeque. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Buffer6   Require Import SizedBuffer.
From KTDeque.Cadeque9  Require Import Model Ops OpsFast.

Set Extraction Output Directory "kcadeque9_extracted".

Extraction Language OCaml.

(* Buf6 override — same shim as Cadeque8 (KCadequeShim provides the
   buf6 backend backed by a certified KChain). *)
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

Extraction "kCadeque9.ml"
  Buf6
  buf6_empty buf6_singleton buf6_push buf6_inject buf6_pop buf6_eject
  buf6_size buf6_to_list buf6_elems
  KElem9 Stored9 KCadeque9
  kcad9_empty
  kcad9_singleton
  kcad9_to_list
  kcad9_push
  kcad9_inject
  kcad9_pop
  kcad9_eject
  kcad9_concat
  (* OpsFast — flat sum-typed variants. *)
  pop_result9 eject_result9
  kcad9_push_fast
  kcad9_inject_fast
  kcad9_pop_fast
  kcad9_eject_fast
  kcad9_concat_fast.
