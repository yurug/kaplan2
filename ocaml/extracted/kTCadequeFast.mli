
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

type 'a stored =
| SGround of 'a
| SSmall of 'a stored buffer
| SBig of 'a stored buffer * 'a cchain * 'a stored buffer
and 'a cnode =
| Node of kind * 'a stored buffer * 'a stored buffer
and 'a cbody =
| BHole
| BSingle of 'a cnode * 'a cbody
| BPairY of 'a cnode * 'a cbody * 'a cchain
| BPairO of 'a cnode * 'a cchain * 'a cbody
and 'a cpacket =
| Pkt of 'a cbody * 'a cnode
and 'a cchain =
| CEmpty
| CSingle of 'a cpacket * 'a cchain
| CPair of 'a cchain * 'a cchain

type 'a cadeque = 'a cchain

val cad_empty : 'a1 cadeque

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

type gyor =
| CG
| CY
| CO
| CR

val chain_has_node : 'a1 cchain -> bool

val root_and_child : 'a1 cpacket -> 'a1 cchain -> 'a1 cnode * 'a1 cchain

val node_color_f : bool -> 'a1 cnode -> gyor

val tree_of_f : 'a1 cnode -> 'a1 cchain -> 'a1 cchain

val pkt_update_f :
  ('a1 cnode -> 'a1 cnode) -> 'a1 cpacket -> 'a1 cchain -> 'a1 cchain

val node_push_f : 'a1 stored -> 'a1 cnode -> 'a1 cnode

val node_inject_f : 'a1 cnode -> 'a1 stored -> 'a1 cnode

val push_chain_f : 'a1 stored -> 'a1 cchain -> 'a1 cchain

val inject_chain_f : 'a1 cchain -> 'a1 stored -> 'a1 cchain

val cad_push_f : 'a1 -> 'a1 cadeque -> 'a1 cadeque

val cad_inject_f : 'a1 cadeque -> 'a1 -> 'a1 cadeque

val degenerate_buf_f : 'a1 cchain -> 'a1 stored buffer option

val make_left_only_f :
  'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val make_left_f : 'a1 cchain -> 'a1 cchain option

val make_right_only_f :
  'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val make_right_f : 'a1 cchain -> 'a1 cchain option

val concat_small_left_f : 'a1 stored buffer -> 'a1 cchain -> 'a1 cchain option

val concat_small_right_f :
  'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val cad_concat_f : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque option

val node_pop_f : 'a1 cnode -> ('a1 stored * 'a1 cnode) option

val node_eject_f : 'a1 cnode -> ('a1 cnode * 'a1 stored) option

val rebuild_childless_f : 'a1 cnode -> 'a1 cchain

val pop_raw_f : 'a1 cchain -> ('a1 stored * 'a1 cchain) option

val eject_raw_f : 'a1 cchain -> ('a1 cchain * 'a1 stored) option

val repair_front_f :
  kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
  -> 'a1 cchain option

val repair_back_f :
  kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
  -> 'a1 cchain option

val drain_both_f :
  'a1 cchain -> (('a1 stored * 'a1 stored option) * 'a1 cchain) option

val repair_both_f :
  'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain -> 'a1
  cchain option

val repair_packet_f : 'a1 cpacket -> 'a1 cchain -> 'a1 cchain option

val repair_pop_side_f : 'a1 cchain -> 'a1 cchain option

val repair_eject_side_f : 'a1 cchain -> 'a1 cchain option

val cad_pop_f : 'a1 cadeque -> ('a1 * 'a1 cadeque) option

val cad_eject_f : 'a1 cadeque -> ('a1 cadeque * 'a1) option
