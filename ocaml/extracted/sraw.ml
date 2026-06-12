(* Sraw — zero-box carrier for the §6 stored cell ([fstored] in
   rocq/KTDeque/Catenable/FlatChain.v).

   Representation:
     ground a   = a                      (NO box: the cell IS the payload)
     small b    = block tag 0 [b]
     big p c q  = block tag 1 [p; c; q]

   The §6 operations inspect cells only through the two FlatChain
   wrappers, each blind:
     - cell_case_ground reads the cell AS the payload (level-0 cells
       are always ground under J's chain_leveled 0);
     - cell_case_struct dispatches on the block tag (child-level cells
       are never ground).
   Soundness of dropping the fallback arms is FlatKeystone.v: on fJ
   inputs the fallback continuations are unreachable.  This erases one
   heap block (2 words) PER STORED ELEMENT — measured 5.0 -> 3.0 live
   words/element on a 10^6 push-built cadeque. *)

type 'a t = Obj.t

type ('buf, 'chain) strct =
  | Small of 'buf
  | Big of 'buf * 'chain * 'buf

let ground : 'a -> 'b t = Obj.repr

let small (b : 'buf) : 'a t = Obj.repr (Small b)

let big ((p, c, q) : 'buf * 'chain * 'buf) : 'a t = Obj.repr (Big (p, c, q))

let case_struct ks kb (t : 'a t) =
  match (Obj.obj t : (Obj.t, Obj.t) strct) with
  | Small b -> ks (Obj.magic b)
  | Big (p, c, q) -> kb (Obj.magic p) (Obj.magic c) (Obj.magic q)
