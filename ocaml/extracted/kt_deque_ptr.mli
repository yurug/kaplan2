
type __ = Obj.t

val app : 'a1 list -> 'a1 list -> 'a1 list

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2



module Nat :
 sig
 end

type 'a xpow = __

val xflat : int -> 'a1 xpow -> 'a1 list

module ElementTree :
 sig
  type 'a t = (int, 'a xpow) sigT

  val to_list : 'a1 t -> 'a1 list

  val level : 'a1 t -> int

  val base : 'a1 -> 'a1 t

  val pair : 'a1 t -> 'a1 t -> 'a1 t

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
 end

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

val buf5_size : 'a1 buf5 -> int

val buf5_seq : ('a1 -> 'a2 list) -> 'a1 buf5 -> 'a2 list

val buf5_push_naive : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val buf5_inject_naive : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val buf5_pop_naive : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val buf5_eject_naive : 'a1 buf5 -> ('a1 buf5 * 'a1) option

module E :
 sig
  type 'a t = (int, 'a xpow) sigT

  val to_list : 'a1 t -> 'a1 list

  val level : 'a1 t -> int

  val base : 'a1 -> 'a1 t

  val pair : 'a1 t -> 'a1 t -> 'a1 t

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
 end

type 'a packet =
| Hole
| PNode of 'a E.t buf5 * 'a packet * 'a E.t buf5

type 'a chain =
| Ending of 'a E.t buf5
| ChainCons of 'a packet * 'a chain

val buf_seq_E : 'a1 E.t buf5 -> 'a1 list

val packet_seq : 'a1 packet -> 'a1 list -> 'a1 list

val chain_seq : 'a1 chain -> 'a1 list

val chain_to_list : 'a1 chain -> 'a1 list

val empty_chain : 'a1 chain

val push_chain : 'a1 E.t -> 'a1 chain -> 'a1 chain option

val inject_chain : 'a1 chain -> 'a1 E.t -> 'a1 chain option

val pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option

val make_red_push_chain : 'a1 chain -> 'a1 chain option

val make_red_inject_chain : 'a1 chain -> 'a1 chain option

val push_chain_full : 'a1 E.t -> 'a1 chain -> 'a1 chain option

val inject_chain_full : 'a1 chain -> 'a1 E.t -> 'a1 chain option

val push_chain_rec : 'a1 E.t -> 'a1 chain -> 'a1 chain option

val inject_chain_rec : 'a1 chain -> 'a1 E.t -> 'a1 chain option

val pop_chain_rec : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val eject_chain_rec : 'a1 chain -> ('a1 chain * 'a1 E.t) option

val make_green_pop_chain : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val make_green_eject_chain : 'a1 chain -> ('a1 chain * 'a1 E.t) option

val pop_chain_full : 'a1 chain -> ('a1 E.t * 'a1 chain) option

val eject_chain_full : 'a1 chain -> ('a1 chain * 'a1 E.t) option

type color =
| Green
| Yellow
| Red

val buf_color : 'a1 buf5 -> color

val color_meet : color -> color -> color

module Coq_E :
 sig
  type 'a t = (int, 'a xpow) sigT

  val to_list : 'a1 t -> 'a1 list

  val level : 'a1 t -> int

  val base : 'a1 -> 'a1 t

  val pair : 'a1 t -> 'a1 t -> 'a1 t

  val unpair : 'a1 t -> ('a1 t * 'a1 t) option
 end

val green_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val green_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val yellow_push : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val yellow_inject : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val green_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val green_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option

val yellow_pop : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val yellow_eject : 'a1 buf5 -> ('a1 buf5 * 'a1) option

val prefix23 : 'a1 option -> ('a1 * 'a1) -> 'a1 buf5

val suffix23 : ('a1 * 'a1) -> 'a1 option -> 'a1 buf5

val suffix12 : 'a1 -> 'a1 option -> 'a1 buf5

type 'x bdecomp_pre =
| BD_pre_underflow of 'x option
| BD_pre_ok of 'x buf5
| BD_pre_overflow of 'x buf5 * 'x * 'x

type 'x bdecomp_suf =
| BD_suf_underflow of 'x option
| BD_suf_ok of 'x buf5
| BD_suf_overflow of 'x buf5 * 'x * 'x

val prefix_decompose : 'a1 buf5 -> 'a1 bdecomp_pre

val suffix_decompose : 'a1 buf5 -> 'a1 bdecomp_suf

type 'x bsandwich =
| BS_alone of 'x option
| BS_sandwich of 'x * 'x buf5 * 'x

val buffer_unsandwich : 'a1 buf5 -> 'a1 bsandwich

val prefix_rot : 'a1 -> 'a1 buf5 -> 'a1 buf5 * 'a1

val suffix_rot : 'a1 buf5 -> 'a1 -> 'a1 * 'a1 buf5

val buffer_halve : 'a1 buf5 -> 'a1 option * ('a1 * 'a1) buf5

val green_prefix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val green_suffix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val prefix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val suffix_concat :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> ('a1 Coq_E.t buf5 * 'a1 Coq_E.t
  buf5) option

val buffer_push_chain : 'a1 Coq_E.t -> 'a1 Coq_E.t buf5 -> 'a1 chain

val buffer_inject_chain : 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t -> 'a1 chain

val pair_one : ('a1 Coq_E.t * 'a1 Coq_E.t) -> 'a1 Coq_E.t option

val pair_each_buf :
  ('a1 Coq_E.t * 'a1 Coq_E.t) buf5 -> 'a1 Coq_E.t buf5 option

val mk_ending_from_options :
  'a1 Coq_E.t option -> ('a1 Coq_E.t * 'a1 Coq_E.t) option -> 'a1 Coq_E.t
  option -> 'a1 chain

val make_small :
  'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 Coq_E.t buf5 -> 'a1 chain option

val green_of_red : 'a1 chain -> 'a1 chain option

val pkt_outer_color : 'a1 packet -> color

val ensure_green : 'a1 chain -> 'a1 chain option

val make_yellow :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
  chain option

val make_red :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 chain -> 'a1
  chain option

val push_kt : 'a1 Coq_E.t -> 'a1 chain -> 'a1 chain option

val inject_kt : 'a1 chain -> 'a1 Coq_E.t -> 'a1 chain option

val pop_kt : 'a1 chain -> ('a1 Coq_E.t * 'a1 chain) option

val eject_kt : 'a1 chain -> ('a1 chain * 'a1 Coq_E.t) option

type 'a kChain =
| KEnding of 'a Coq_E.t buf5
| KCons of color * 'a packet * 'a kChain

val empty_kchain : 'a1 kChain

val chain_to_kchain_g : 'a1 chain -> 'a1 kChain

val kchain_to_chain : 'a1 kChain -> 'a1 chain

val kchain_to_list : 'a1 kChain -> 'a1 list

val green_of_red_k : 'a1 kChain -> 'a1 kChain option

val ensure_green_k : 'a1 kChain -> 'a1 kChain option

val make_yellow_k :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option

val make_red_k :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option

val push_kt2 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option

val inject_kt2 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option

val pop_kt2 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option

val eject_kt2 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option

val yellow_wrap :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  kChain option

val push_kt3 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 kChain option

val inject_kt3 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 kChain option

val pop_kt3 : 'a1 kChain -> ('a1 Coq_E.t * 'a1 kChain) option

val eject_kt3 : 'a1 kChain -> ('a1 kChain * 'a1 Coq_E.t) option

type 'a push_result =
| PushFail
| PushOk of 'a kChain

type 'a pop_result =
| PopFail
| PopOk of 'a Coq_E.t * 'a kChain

val yellow_wrap_pr :
  'a1 Coq_E.t buf5 -> 'a1 packet -> 'a1 Coq_E.t buf5 -> 'a1 kChain -> 'a1
  push_result

val push_kt4 : 'a1 Coq_E.t -> 'a1 kChain -> 'a1 push_result

val inject_kt4 : 'a1 kChain -> 'a1 Coq_E.t -> 'a1 push_result

val pop_kt4 : 'a1 kChain -> 'a1 pop_result

val eject_kt4 : 'a1 kChain -> 'a1 pop_result
