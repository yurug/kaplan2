
val negb : bool -> bool



module Nat :
 sig
  val ltb : int -> int -> bool

  val min : int -> int -> int
 end

type 'x buffer = 'x Fastbuf.t

type kind =
| KOnly
| KLeft
| KRight

type gyor =
| CG
| CY
| CO
| CR

val bempty : 'a1 buffer

val b1 : 'a1 -> 'a1 buffer

val b2 : 'a1 -> 'a1 -> 'a1 buffer

val b3 : 'a1 -> 'a1 -> 'a1 -> 'a1 buffer

val bpush : 'a1 -> 'a1 buffer -> 'a1 buffer

val binject : 'a1 buffer -> 'a1 -> 'a1 buffer

val bpop : 'a1 buffer -> ('a1 * 'a1 buffer) option

val beject : 'a1 buffer -> ('a1 buffer * 'a1) option

val bsize : 'a1 buffer -> int

val bis_empty : 'a1 buffer -> bool

val bapp : 'a1 buffer -> 'a1 buffer -> 'a1 buffer

val bpop2 : 'a1 buffer -> (('a1 * 'a1) * 'a1 buffer) option

val beject2 : 'a1 buffer -> (('a1 buffer * 'a1) * 'a1) option

val beject3 : 'a1 buffer -> ((('a1 buffer * 'a1) * 'a1) * 'a1) option

val bfold_right : ('a1 -> 'a2 -> 'a2) -> 'a2 -> 'a1 buffer -> 'a2

val bfold_left : ('a2 -> 'a1 -> 'a2) -> 'a1 buffer -> 'a2 -> 'a2

type 'a fnode =
| FNode of kind * 'a Sraw.t buffer * 'a Sraw.t buffer
and 'a fbody =
| FHole
| FBSingle of 'a fnode * 'a fbody
| FBPairY of 'a fnode * 'a fbody * 'a fchain
| FBPairO of 'a fnode * 'a fchain * 'a fbody
and 'a fchain =
| FEmpty
| FFlat of kind * 'a Sraw.t buffer * 'a Sraw.t buffer * 'a fchain
| FSingle of 'a fbody * 'a fnode * 'a fchain
| FPair of 'a fchain * 'a fchain

val cell_case_ground : 'a1 Sraw.t -> ('a1 -> 'a2) -> 'a2 -> 'a2

val cell_case_struct :
  'a1 Sraw.t -> ('a1 Sraw.t buffer -> 'a2) -> ('a1 Sraw.t buffer -> 'a1
  fchain -> 'a1 Sraw.t buffer -> 'a2) -> 'a2 -> 'a2

val tree_of_x : 'a1 fnode -> 'a1 fchain -> 'a1 fchain

val root_and_child_x :
  'a1 fbody -> 'a1 fnode -> 'a1 fchain -> 'a1 fnode * 'a1 fchain

val push_chain_x : 'a1 Sraw.t -> 'a1 fchain -> 'a1 fchain

val inject_chain_x : 'a1 fchain -> 'a1 Sraw.t -> 'a1 fchain

val cad_push_x : 'a1 -> 'a1 fchain -> 'a1 fchain

val cad_inject_x : 'a1 fchain -> 'a1 -> 'a1 fchain

val degenerate_buf_x : 'a1 fchain -> 'a1 Sraw.t buffer option

val make_left_only_x :
  'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option

val make_left_x : 'a1 fchain -> 'a1 fchain option

val make_right_only_x :
  'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option

val make_right_x : 'a1 fchain -> 'a1 fchain option

val concat_small_left_x : 'a1 Sraw.t buffer -> 'a1 fchain -> 'a1 fchain option

val concat_small_right_x :
  'a1 fchain -> 'a1 Sraw.t buffer -> 'a1 fchain option

val cad_concat_x : 'a1 fchain -> 'a1 fchain -> 'a1 fchain option

val pop_raw_x : 'a1 fchain -> ('a1 Sraw.t * 'a1 fchain) option

val eject_raw_x : 'a1 fchain -> ('a1 fchain * 'a1 Sraw.t) option

val repair_front_x :
  kind -> 'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain
  -> 'a1 fchain option

val repair_back_x :
  kind -> 'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain
  -> 'a1 fchain option

val drain_both_x :
  'a1 fchain -> (('a1 Sraw.t * 'a1 Sraw.t option) * 'a1 fchain) option

val repair_both_x :
  'a1 fbody -> 'a1 Sraw.t buffer -> 'a1 Sraw.t buffer -> 'a1 fchain -> 'a1
  fchain option

val repair_packet_x :
  'a1 fbody -> 'a1 fnode -> 'a1 fchain -> 'a1 fchain option

val repair_pop_side_x : 'a1 fchain -> 'a1 fchain option

val repair_eject_side_x : 'a1 fchain -> 'a1 fchain option

val cad_pop_x : 'a1 fchain -> ('a1 * 'a1 fchain) option

val cad_eject_x : 'a1 fchain -> ('a1 fchain * 'a1) option

val fcad_empty : 'a1 fchain
