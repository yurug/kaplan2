(* Eraw — the zero-box runtime representation of check-erased element
   trees (Common/ErasedTree.v, extracted via Extract Inductive in
   Extract/ExtractionFast.v).

     - [leaf x] IS x (no allocation, no tag);
     - [pair a b] is one two-field block;
     - [case_pair] is the BLIND match: it reads the two fields without
       discrimination.  The ErasedOps naturality lemmas show every
       Rocq-side [etree] match sits at an old unpair site that sees a
       pair whenever the keystone-proven kt4 operation succeeds, i.e.
       on every input reachable from a regular chain; the leaf
       continuation is therefore never invoked at runtime and is
       ignored here (its Rocq counterparts live only on failure paths).

   The phantom parameter keeps the extracted types well-formed. *)

type 'a t = Obj.t

let leaf : 'a -> 'a t = Obj.repr

let pair ((a, b) : 'a t * 'a t) : 'a t = Obj.repr (a, b)

let case_pair (fp : 'a t -> 'a t -> 'b) (t : 'a t) : 'b =
  fp (Obj.field t 0) (Obj.field t 1)

(* level-0 projection: only applied to elements inserted via [leaf] *)
let unleaf (t : 'a t) : 'a = Obj.obj t
