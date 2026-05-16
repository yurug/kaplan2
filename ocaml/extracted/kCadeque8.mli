
val app : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val buf6_elems : 'a1 KCadequeShim.buf6 -> 'a1 list

val buf6_to_list : 'a1 KCadequeShim.buf6 -> 'a1 list

val buf6_size : 'a1 KCadequeShim.buf6 -> int

val buf6_empty : 'a1 KCadequeShim.buf6

val buf6_singleton : 'a1 -> 'a1 KCadequeShim.buf6

val buf6_is_empty : 'a1 KCadequeShim.buf6 -> bool

val buf6_push : 'a1 -> 'a1 KCadequeShim.buf6 -> 'a1 KCadequeShim.buf6

val buf6_inject : 'a1 KCadequeShim.buf6 -> 'a1 -> 'a1 KCadequeShim.buf6

val buf6_pop : 'a1 KCadequeShim.buf6 -> ('a1 * 'a1 KCadequeShim.buf6) option

val buf6_eject : 'a1 KCadequeShim.buf6 -> ('a1 KCadequeShim.buf6 * 'a1) option

type 'x kElem8 =
| XBase8 of 'x
| XStored8 of 'x stored8
and 'x stored8 =
| StoredSmall8 of 'x kElem8 KCadequeShim.buf6
| StoredBig8 of 'x kElem8 KCadequeShim.buf6 * 'x kCadeque8
   * 'x kElem8 KCadequeShim.buf6
and 'x kCadeque8 =
| K8Empty
| K8Simple of 'x kElem8 KCadequeShim.buf6
| K8Triple of 'x kElem8 KCadequeShim.buf6 * 'x stored8 KCadequeShim.buf6
   * 'x kElem8 KCadequeShim.buf6

val kcad8_empty : 'a1 kCadeque8

val kcad8_singleton : 'a1 -> 'a1 kCadeque8

val kcad8_to_list : 'a1 kCadeque8 -> 'a1 list

val kcad8_push : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8

val kcad8_inject : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8

val unfold_stored :
  'a1 stored8 -> ('a1 kElem8 KCadequeShim.buf6 * 'a1 kCadeque8) * 'a1 kElem8
  KCadequeShim.buf6

val reassemble_after_pop_unfold :
  'a1 kElem8 KCadequeShim.buf6 -> 'a1 kCadeque8 -> 'a1 kElem8
  KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8
  KCadequeShim.buf6 -> 'a1 kCadeque8

val reassemble_after_eject_unfold :
  'a1 kElem8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
  kCadeque8 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6
  -> 'a1 kCadeque8

val kcad8_from_list : 'a1 list -> 'a1 kCadeque8

val rebalance_after_h_empty :
  'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
  kCadeque8

val kcad8_pop_struct : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option

val kcad8_eject_struct : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option

val kcad8_pop : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option

val kcad8_eject : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option

val kcad8_concat : 'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8
