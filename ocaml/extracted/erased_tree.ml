(* Erased_tree — level-erased element trees for the production cadeque.

   OCaml side of the ElementTree remapping in
   rocq/KTDeque/Extract/ExtractionFast.v.  The Rocq model represents a
   §4 element as a level-TAGGED perfect tree, [{ l : nat & xpow A l }];
   extracted naively that is one [ExistT] box per element.  This module
   erases the representation:

     - a level-0 element IS the payload value, unboxed ([base] is
       [Obj.repr], zero allocation per push);
     - a level-(l+1) element is one tag-3 block [| level; left; right |]
       (the level rides in the block, so [level] — which the op code
       consults through [Nat.eq_dec] at every pairing site — stays O(1)
       and the worst-case O(1) bound is preserved).

   REPRESENTATION INVARIANT (what makes the tag test sound): this
   module is linked ONLY into the catenable-deque extraction
   (kTSizedChain.ml via Fastbuf), where buffer elements are always
   values of the extracted [stored] type — heap blocks with tag 0, 1
   or 2 (every [stored] constructor carries arguments).  Tag 3 is
   therefore free to mark pair nodes.  Do not reuse this module for
   element types that can be represented as tag-3 blocks.

   The six operations implement the laws proven of the Rocq
   [ElementTree] (to_list_base, to_list_pair, level_base, level_pair,
   unpair_base, unpair_pair) — the conditional-naturality proofs that
   would fold this module back into the theorem-backed zone are the
   recorded next phase (SESSION_STATE.md). *)

type 'a t = Obj.t

let pair_tag = 3

let is_pair (t : Obj.t) : bool = Obj.is_block t && Obj.tag t = pair_tag

let base (x : 'a) : 'a t = Obj.repr x

(* level-0 projection: callers (Fastbuf.pop/eject) only apply this to
   elements they pushed via [base] *)
let unbase (t : 'a t) : 'a = Obj.obj t

let level (t : 'a t) : int =
  if is_pair t then (Obj.obj (Obj.field t 0) : int) else 0

let pair (x : 'a t) (y : 'a t) : 'a t =
  let b = Obj.new_block pair_tag 3 in
  Obj.set_field b 0 (Obj.repr (level x + 1));
  Obj.set_field b 1 x;
  Obj.set_field b 2 y;
  b

let unpair (t : 'a t) : ('a t * 'a t) option =
  if is_pair t then Some (Obj.field t 1, Obj.field t 2) else None

(* front-to-back leaves: to_list (pair x y) = to_list x @ to_list y *)
let rec to_list_acc (t : 'a t) (acc : 'a list) : 'a list =
  if is_pair t then
    to_list_acc (Obj.field t 1) (to_list_acc (Obj.field t 2) acc)
  else (Obj.obj t : 'a) :: acc

let to_list (t : 'a t) : 'a list = to_list_acc t []
