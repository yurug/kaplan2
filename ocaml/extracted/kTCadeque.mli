
val negb : bool -> bool

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

module Nat :
 sig
  val ltb : int -> int -> bool

  val min : int -> int -> int
 end

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

type 'x buffer = 'x list

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

val stored_seq : 'a1 stored -> 'a1 list

val cnode_seq : 'a1 cnode -> 'a1 list -> 'a1 list

val cbody_seq : 'a1 cbody -> 'a1 list -> 'a1 list

val cpacket_seq : 'a1 cpacket -> 'a1 list -> 'a1 list

val cchain_seq : 'a1 cchain -> 'a1 list

val cad_to_list : 'a1 cadeque -> 'a1 list

type gyor =
| CG
| CY
| CO
| CR

val node_color : bool -> 'a1 cnode -> gyor

val chain_has_node : 'a1 cchain -> bool

val node_push : 'a1 stored -> 'a1 cnode -> 'a1 cnode

val node_inject : 'a1 cnode -> 'a1 stored -> 'a1 cnode

val root_and_child : 'a1 cpacket -> 'a1 cchain -> 'a1 cnode * 'a1 cchain

val tree_of : 'a1 cnode -> 'a1 cchain -> 'a1 cchain

val pkt_update :
  ('a1 cnode -> 'a1 cnode) -> 'a1 cpacket -> 'a1 cchain -> 'a1 cchain

val push_chain : 'a1 stored -> 'a1 cchain -> 'a1 cchain

val inject_chain : 'a1 cchain -> 'a1 stored -> 'a1 cchain

val cad_push : 'a1 -> 'a1 cadeque -> 'a1 cadeque

val cad_inject : 'a1 cadeque -> 'a1 -> 'a1 cadeque

val buf_pop2 : 'a1 buffer -> (('a1 * 'a1) * 'a1 buffer) option

val buf_eject2 : 'a1 buffer -> (('a1 buffer * 'a1) * 'a1) option

val buf_eject3 : 'a1 buffer -> ((('a1 buffer * 'a1) * 'a1) * 'a1) option

val degenerate_buf : 'a1 cchain -> 'a1 stored buffer option

val make_left_only :
  'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val make_left : 'a1 cchain -> 'a1 cchain option

val make_right_only :
  'a1 stored buffer -> 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val make_right : 'a1 cchain -> 'a1 cchain option

val concat_small_left : 'a1 stored buffer -> 'a1 cchain -> 'a1 cchain option

val concat_small_right : 'a1 cchain -> 'a1 stored buffer -> 'a1 cchain option

val cad_concat : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque option

val node_pop : 'a1 cnode -> ('a1 stored * 'a1 cnode) option

val node_eject : 'a1 cnode -> ('a1 cnode * 'a1 stored) option

val rebuild_childless : 'a1 cnode -> 'a1 cchain

val pop_raw : 'a1 cchain -> ('a1 stored * 'a1 cchain) option

val eject_raw : 'a1 cchain -> ('a1 cchain * 'a1 stored) option

val repair_front :
  kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
  -> 'a1 cchain option

val repair_back :
  kind -> 'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain
  -> 'a1 cchain option

val drain_both :
  'a1 cchain -> (('a1 stored * 'a1 stored option) * 'a1 cchain) option

val repair_both :
  'a1 cbody -> 'a1 stored buffer -> 'a1 stored buffer -> 'a1 cchain -> 'a1
  cchain option

val repair_packet : 'a1 cpacket -> 'a1 cchain -> 'a1 cchain option

val repair_pop_side : 'a1 cchain -> 'a1 cchain option

val repair_eject_side : 'a1 cchain -> 'a1 cchain option

val cad_pop : 'a1 cadeque -> ('a1 * 'a1 cadeque) option

val cad_eject : 'a1 cadeque -> ('a1 cadeque * 'a1) option
