
val negb : bool -> bool

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

val kcad8_simple_or_empty : 'a1 kElem8 KCadequeShim.buf6 -> 'a1 kCadeque8

val stored_sub_left_safe : 'a1 stored8 -> bool

val stored_sub_right_safe : 'a1 stored8 -> bool

val rebalance_after_h_empty :
  'a1 stored8 KCadequeShim.buf6 -> 'a1 kElem8 KCadequeShim.buf6 -> 'a1
  kCadeque8 option

val kcad8_pop_struct : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option

val rebalance_after_t_empty :
  'a1 kElem8 KCadequeShim.buf6 -> 'a1 stored8 KCadequeShim.buf6 -> 'a1
  kCadeque8 option

val kcad8_eject_struct : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option

val kcad8_pop : 'a1 kCadeque8 -> ('a1 * 'a1 kCadeque8) option

val kcad8_eject : 'a1 kCadeque8 -> ('a1 kCadeque8 * 'a1) option

val kcad8_concat : 'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8

type 'x pop_result8 =
| PopFail8
| PopOk8 of 'x * 'x kCadeque8

type 'x eject_result8 =
| EjectFail8
| EjectOk8 of 'x kCadeque8 * 'x

val kcad8_push_fast : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8

val kcad8_inject_fast : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8

val kcad8_pop_struct_fast : 'a1 kCadeque8 -> 'a1 pop_result8

val kcad8_pop_fast : 'a1 kCadeque8 -> 'a1 pop_result8

val kcad8_eject_struct_fast : 'a1 kCadeque8 -> 'a1 eject_result8

val kcad8_eject_fast : 'a1 kCadeque8 -> 'a1 eject_result8

val kcad8_concat_fast : 'a1 kCadeque8 -> 'a1 kCadeque8 -> 'a1 kCadeque8

(** Hand-fused hot path — semantically equal to {!kcad8_push_fast} but
    bypasses the [KCadequeShim.buf6_push] cross-module hop.  See the
    Rocq side [Cadeque8/OpsFast.v:kcad8_push_inline] (defined as
    [kcad8_push_inline := kcad8_push_fast]).  All correctness lemmas
    (sequence preservation, regularity preservation) transfer to the
    inline variant by reflexivity at the Rocq level. *)
val kcad8_push_inline : 'a1 -> 'a1 kCadeque8 -> 'a1 kCadeque8

(** Hand-fused hot path — semantically equal to {!kcad8_inject_fast}. *)
val kcad8_inject_inline : 'a1 kCadeque8 -> 'a1 -> 'a1 kCadeque8
