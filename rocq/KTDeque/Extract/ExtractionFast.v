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

(** ** The check-erased sized chain (DequePtr/ErasedOps.v).

    Replaces kTSizedChain as the buffer storage: the erased ops carry
    no runtime level discipline at all — pairing is an unchecked
    constructor, unpairing is blind field access.  [etree] extracts to
    a ZERO-BOX representation: a leaf IS its payload ([Obj.repr]), a
    pair is one two-field block, and the match function reads the
    fields blindly.  Soundness: the erased mirrors match [etree] only
    at the old unpair sites, and the naturality lemmas (ErasedOps.v)
    show those sites see pairs whenever the keystone-proven kt4 op
    succeeds — i.e. on every input reachable from regular chains.  The
    ELeaf arms exist in the Rocq code only on paths where the original
    operation failed. *)

From KTDeque.Common Require Import ErasedTree.
From KTDeque.DequePtr Require Import ErasedOps.

Extract Inductive etree => "Eraw.t"
  [ "Eraw.leaf" "Eraw.pair" ]
  "(fun _ fp t -> Eraw.case_pair fp t)".

Extraction "kTErasedChain.ml"
  GSChain
  gpop_result
  egs_empty
  egs_size
  epush_s
  einject_s
  epop_s
  eeject_s.

(** ** The fused-spine §6 cadeque (Catenable/FlatChain.v, FlatOps.v).

    The fourth verified pass: the dominant spine shape
    [CSingle (Pkt BHole (Node k p s)) rest] is one constructor
    ([FFlat]), so every push/inject and every green/red rebundle
    allocates ONE spine block where the previous artifact allocated
    three.  Keystone bundle: Catenable/FlatKeystone.v (via the [_x_er]
    erasure commutations). *)

From KTDeque.Catenable Require Import FlatChain FlatOps.

Extraction Inline
  fsingle fcell fdegen
  upd_flat_x upd_single_x
  node_push_x node_inject_x node_pop_x node_eject_x
  node_color_x fchain_has_node.

Extraction "kTFlatCadeque.ml"
  fchain
  fcad_empty
  cad_push_x
  cad_inject_x
  cad_pop_x
  cad_eject_x
  cad_concat_x.
