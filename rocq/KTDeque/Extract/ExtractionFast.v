(** * Module: KTDeque.Extract.ExtractionFast — production catenable deque.

    Extracts the FAST §6 catenable deque (Catenable/OpsFast.v, equal to
    the frozen Ops.v family by the OpsFast [_eq] lemmas; keystone bundle
    in Catenable/FastKeystone.v) with the buffer type and the BufPrims
    primitives REMAPPED to the production buffer:

        Fastbuf = the proven §4 deque (kt4) + an O(1) size field
        (ocaml/extracted/fastbuf.ml).

    These [Extract Constant] directives are the ONLY trusted seam of
    the fast artifact: each maps a one-line list definition to the
    corresponding Fastbuf operation, whose sequence behaviour is the
    §4 deque keystone's theorem.  Everything above the seam (every op,
    every theorem) is the verified mirror. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

From KTDeque.Catenable Require Import Model BufPrims OpsFast.

Set Extraction Output Directory "kt_extracted".
Extraction Language OCaml.

Extract Constant buffer "'x" => "'x Fastbuf.t".
Extract Constant bempty => "Fastbuf.empty".
Extract Constant b1 => "Fastbuf.b1".
Extract Constant b2 => "Fastbuf.b2".
Extract Constant b3 => "Fastbuf.b3".
Extract Constant bpush => "Fastbuf.push".
Extract Constant binject => "Fastbuf.inject".
Extract Constant bpop => "Fastbuf.pop".
Extract Constant beject => "Fastbuf.eject".
Extract Constant bsize => "Fastbuf.size".
Extract Constant bis_empty => "Fastbuf.is_empty".
Extract Constant bapp => "Fastbuf.append".
Extract Constant bpop2 => "Fastbuf.pop2".
Extract Constant beject2 => "Fastbuf.eject2".
Extract Constant beject3 => "Fastbuf.eject3".
Extract Constant bfold_right => "Fastbuf.fold_right".
Extract Constant bfold_left => "Fastbuf.fold_left".

Extraction "kTCadequeFast.ml"
  cadeque
  cad_empty
  cad_push_f
  cad_inject_f
  cad_pop_f
  cad_eject_f
  cad_concat_f.
