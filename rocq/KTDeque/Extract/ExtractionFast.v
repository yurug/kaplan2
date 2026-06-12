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

From KTDeque.Catenable Require Import Model Color Ops BufPrims OpsFast OpsFused.

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

(* Verified Coq-level fusion (OpsFused.v) plus extraction-time inlining
   of the small helpers: the per-op call chain flattens into one
   function body in the emitted OCaml. *)
Extraction Inline
  upd_pkt tree_repair
  node_push_f node_inject_f node_pop_f node_eject_f
  node_color_f tree_of_f pkt_update_f root_and_child
  rebuild_childless_f.

Extraction "kTCadequeFast.ml"
  cadeque
  cad_empty
  cad_push_v2
  cad_inject_v2
  cad_pop_v2
  cad_eject_v2
  cad_concat_f.

(** ** The sized §4 chain (DequePtr/SizedChain.v) — the buffer storage.

    Extracted as its own self-contained module: Fastbuf (the seam
    implementation) is built directly on these ops, so the size field
    lives fused inside the chain's top constructor (no wrapper record)
    and push/inject return the chain bare (no result constructor). *)

From KTDeque.DequePtr Require Import SizedChain.
From KTDeque.Common Require Import Element.

(* Level erasure for the element trees (the recursive-slowdown pairing).
   The Rocq representation is a level-TAGGED sigma; the production
   representation (ocaml/extracted/erased_tree.ml) erases it: unboxed
   level-0 leaves (zero allocation per element) and level-carrying pair
   blocks (so [level] — consulted by the op code at every pairing
   site — stays O(1) and the WC O(1) bound is preserved).  The module
   implements the six proven ElementTree laws; folding it into the
   theorem-backed zone via conditional-naturality proofs is the
   recorded next phase. *)
Extract Constant ElementTree.t "'x" => "'x Erased_tree.t".
Extract Constant ElementTree.base => "Erased_tree.base".
Extract Constant ElementTree.level => "Erased_tree.level".
Extract Constant ElementTree.pair => "Erased_tree.pair".
Extract Constant ElementTree.unpair => "Erased_tree.unpair".
Extract Constant ElementTree.to_list => "Erased_tree.to_list".

Extraction "kTSizedChain.ml"
  SChain
  spop_result
  s_empty
  s_size
  s_to_list
  push_s
  inject_s
  pop_s
  eject_s.
