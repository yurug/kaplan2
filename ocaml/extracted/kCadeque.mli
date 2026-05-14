
val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

type 'x buf6 = 'x list
  (* singleton inductive, whose constructor was mkBuf6 *)

val buf6_to_list : 'a1 buf6 -> 'a1 list

val buf6_size : 'a1 buf6 -> int

val buf6_empty : 'a1 buf6

val buf6_singleton : 'a1 -> 'a1 buf6

val buf6_push : 'a1 -> 'a1 buf6 -> 'a1 buf6

val buf6_inject : 'a1 buf6 -> 'a1 -> 'a1 buf6

val buf6_pop : 'a1 buf6 -> ('a1 * 'a1 buf6) option

val buf6_eject : 'a1 buf6 -> ('a1 buf6 * 'a1) option

type regularityTag =
| RegG
| RegR

type 'x kElem =
| XBase of 'x
| XStored of 'x stored
and 'x stored =
| StoredSmall of 'x kElem buf6
| StoredBig of 'x kElem buf6 * 'x kCadeque * 'x kElem buf6
and 'x kCadeque =
| KEmpty
| KSingle of regularityTag * 'x packet * 'x kCadeque
| KPair of 'x kCadeque * 'x kCadeque
and 'x packet =
| Pkt of 'x body * 'x node
and 'x body =
| Hole
| BSingleY of 'x node * 'x body
| BPairY of 'x node * 'x body * 'x body
| BPairO of 'x node * 'x body * 'x body
and 'x node =
| NOnlyEnd of 'x kElem buf6
| NOnly of 'x kElem buf6 * 'x kElem buf6
| NLeft of 'x kElem buf6 * 'x kElem buf6
| NRight of 'x kElem buf6 * 'x kElem buf6

val kcad_empty : 'a1 kCadeque

val kcad_singleton : 'a1 -> 'a1 kCadeque

val kcad_to_list : 'a1 kCadeque -> 'a1 list

val push_node : 'a1 -> 'a1 node -> 'a1 node

val inject_node : 'a1 node -> 'a1 -> 'a1 node

val push_packet : 'a1 -> 'a1 packet -> 'a1 packet

val inject_packet : 'a1 packet -> 'a1 -> 'a1 packet

val kcad_push : 'a1 -> 'a1 kCadeque -> 'a1 kCadeque

val kcad_inject : 'a1 kCadeque -> 'a1 -> 'a1 kCadeque

val kcad_from_list : 'a1 list -> 'a1 kCadeque

val kcad_pop : 'a1 kCadeque -> ('a1 * 'a1 kCadeque) option

val kcad_eject : 'a1 kCadeque -> ('a1 kCadeque * 'a1) option

val kcad_concat : 'a1 kCadeque -> 'a1 kCadeque -> 'a1 kCadeque
