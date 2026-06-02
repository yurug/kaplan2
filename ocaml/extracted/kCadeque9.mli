
val app : 'a1 list -> 'a1 list -> 'a1 list

val leb : int -> int -> bool

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

type 'x kElem9 =
| XBase9 of 'x
| XStored9 of 'x stored9
and 'x stored9 =
| StoredSmall9 of 'x kElem9 KCadequeShim.buf6
| StoredBig9 of 'x kElem9 KCadequeShim.buf6 * 'x stored9 KCadequeShim.buf6
   * 'x kElem9 KCadequeShim.buf6
| StoredMiddle9 of 'x stored9 KCadequeShim.buf6

type 'x kCadeque9 =
| K9Empty
| K9Simple of 'x kElem9 KCadequeShim.buf6
| K9Triple of 'x kElem9 KCadequeShim.buf6 * 'x stored9 KCadequeShim.buf6
   * 'x kElem9 KCadequeShim.buf6

val kcad9_empty : 'a1 kCadeque9

val kcad9_singleton : 'a1 -> 'a1 kCadeque9

val kelem9_to_list : 'a1 kElem9 -> 'a1 list

val stored9_to_list : 'a1 stored9 -> 'a1 list

val kcad9_to_list : 'a1 kCadeque9 -> 'a1 list

val stored9_middle : 'a1 stored9 KCadequeShim.buf6 -> 'a1 stored9

val kcad9_push : 'a1 -> 'a1 kCadeque9 -> 'a1 kCadeque9

val kcad9_inject : 'a1 kCadeque9 -> 'a1 -> 'a1 kCadeque9

val refill_h_K9Triple :
  'a1 kElem9 KCadequeShim.buf6 -> 'a1 stored9 KCadequeShim.buf6 -> 'a1 kElem9
  KCadequeShim.buf6 -> 'a1 kCadeque9

val refill_t_K9Triple :
  'a1 kElem9 KCadequeShim.buf6 -> 'a1 stored9 KCadequeShim.buf6 -> 'a1 kElem9
  KCadequeShim.buf6 -> 'a1 kCadeque9

val kcad9_pop : 'a1 kCadeque9 -> ('a1 * 'a1 kCadeque9) option

val kcad9_eject : 'a1 kCadeque9 -> ('a1 kCadeque9 * 'a1) option

val kcad9_concat : 'a1 kCadeque9 -> 'a1 kCadeque9 -> 'a1 kCadeque9

type 'x pop_result9 =
| PopFail9
| PopOk9 of 'x * 'x kCadeque9

type 'x eject_result9 =
| EjectFail9
| EjectOk9 of 'x kCadeque9 * 'x

val pop_result9_of_option : ('a1 * 'a1 kCadeque9) option -> 'a1 pop_result9

val eject_result9_of_option :
  ('a1 kCadeque9 * 'a1) option -> 'a1 eject_result9

val kcad9_push_fast : 'a1 -> 'a1 kCadeque9 -> 'a1 kCadeque9

val kcad9_inject_fast : 'a1 kCadeque9 -> 'a1 -> 'a1 kCadeque9

val kcad9_concat_fast : 'a1 kCadeque9 -> 'a1 kCadeque9 -> 'a1 kCadeque9

val kcad9_pop_fast : 'a1 kCadeque9 -> 'a1 pop_result9

val kcad9_eject_fast : 'a1 kCadeque9 -> 'a1 eject_result9
