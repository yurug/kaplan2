
val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

module Nat :
 sig
  val pred : int -> int
 end

type 'x buf5 =
| B0
| B1 of 'x
| B2 of 'x * 'x
| B3 of 'x * 'x * 'x
| B4 of 'x * 'x * 'x * 'x
| B5 of 'x * 'x * 'x * 'x * 'x

val buf5_push_naive : 'a1 -> 'a1 buf5 -> 'a1 buf5 option

val buf5_inject_naive : 'a1 buf5 -> 'a1 -> 'a1 buf5 option

val buf5_pop_naive : 'a1 buf5 -> ('a1 * 'a1 buf5) option

val buf5_eject_naive : 'a1 buf5 -> ('a1 buf5 * 'a1) option

type color =
| Green
| Yellow
| Red

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

type 'x gPacket =
| GHole
| GPNode of 'x buf5 * 'x gPacket * 'x buf5

type 'x gChain =
| GEnding of 'x buf5
| GChainCons of 'x gPacket * 'x gChain

type 'x gKChain =
| GKEnding of 'x buf5
| GKCons of color * 'x gPacket * 'x gKChain

type 'x gSChain =
| GSEnding of int * 'x buf5
| GSCons of int * color * 'x gPacket * 'x gKChain

type 'x gpop_result =
| GPopFail
| GPopOk of 'x * 'x gSChain

val buf5_map : ('a1 -> 'a2) -> 'a1 buf5 -> 'a2 buf5

val green_prefix_concat_e :
  'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
  option

val green_suffix_concat_e :
  'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
  option

val prefix_concat_e :
  'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
  option

val suffix_concat_e :
  'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> ('a1 Eraw.t buf5 * 'a1 Eraw.t buf5)
  option

val gpair_one : ('a1 Eraw.t * 'a1 Eraw.t) -> 'a1 Eraw.t

val gpair_each : ('a1 Eraw.t * 'a1 Eraw.t) buf5 -> 'a1 Eraw.t buf5

val gbuffer_push_chain : 'a1 -> 'a1 buf5 -> 'a1 gChain

val gbuffer_inject_chain : 'a1 buf5 -> 'a1 -> 'a1 gChain

val gmk_ending_from_options :
  'a1 option -> ('a1 * 'a1) option -> 'a1 option -> 'a1 gChain

val make_small_e :
  'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t gChain
  option

val gchain_to_gkchain_g : 'a1 gChain -> 'a1 gKChain

val green_of_red_k_e : 'a1 Eraw.t gKChain -> 'a1 Eraw.t gKChain option

val gs_of : int -> 'a1 gKChain -> 'a1 gSChain

val eyellow_wrap :
  'a1 Eraw.t gSChain -> int -> 'a1 Eraw.t buf5 -> 'a1 Eraw.t gPacket -> 'a1
  Eraw.t buf5 -> 'a1 Eraw.t gKChain -> 'a1 Eraw.t gSChain

val epush_s : 'a1 Eraw.t -> 'a1 Eraw.t gSChain -> 'a1 Eraw.t gSChain

val einject_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t -> 'a1 Eraw.t gSChain

val epop_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t gpop_result

val eeject_s : 'a1 Eraw.t gSChain -> 'a1 Eraw.t gpop_result

val egs_empty : 'a1 Eraw.t gSChain

val egs_size : 'a1 gSChain -> int
