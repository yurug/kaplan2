(** {1 KTCatenableDeque — verified persistent catenable deque (KT99 §6)}

    A purely functional catenable deque: in addition to the standard
    [push] / [pop] / [inject] / [eject], this module provides
    [concat] which joins two deques into one.  [concat] is the
    headline operation of Kaplan & Tarjan's JACM 1999 paper §6.

    This module is the OCaml extraction of the Rocq formalisation
    in [rocq/KTDeque/Cadeque6/].  The extraction includes:

    - [cad_push] / [cad_inject] / [cad_pop] / [cad_eject] /
      [cad_concat]: the abstract operations.  Sequence semantics
      proven correct in [Cadeque6/OpsAbstract.v].
    - [cad_*_op]: operational variants with partial regularity
      preservation (push and inject are fully regularity-preserving;
      pop, eject, concat are partial).
    - [cad_*_op_full] + [cad_normalize]: fully regularity-preserving
      variants.  These compose [cad_*_op] with [cad_normalize]
      (rebuild via [cad_from_list_op], which is itself a fold over
      [cad_push_op]).  All five public operations preserve
      [regular_cad] -- this is the Phase 1 deliverable of
      [kb/plan-catenable.md].

    {2 Cost note}

    The extracted [cad_pop_op_full], [cad_eject_op_full], and
    [cad_concat_op_full] use [cad_normalize], which is [O(n)] in
    the abstract sequence length.  This is the {b correctness} spec.
    The KT99 worst-case [O(1)] catenation is the target of Phase 4
    of [kb/plan-catenable.md] and requires a level-typed cascade
    that refines this module.

    {2 Cross-references}

    - {{:https://github.com/yurug/kaplan2/blob/main/kb/spec/why-catenable.md}kb/spec/why-catenable.md}
      -- intuition for catenable deques.
    - {{:https://github.com/yurug/kaplan2/blob/main/rocq/KTDeque/Cadeque6/OpsAbstract.v}rocq/KTDeque/Cadeque6/OpsAbstract.v}
      -- abstract operations and sequence laws.
    - {{:https://github.com/yurug/kaplan2/blob/main/rocq/KTDeque/Cadeque6/Repair.v}rocq/KTDeque/Cadeque6/Repair.v}
      -- operational + _full variants and full preservation theorems.
    - {{:https://github.com/yurug/kaplan2/blob/main/rocq/KTDeque/Public/CadequeInterface.v}rocq/KTDeque/Public/CadequeInterface.v}
      -- the [CADEQUE] module type and the [RegularCadeque] implementation
      we are extracting here.
    - {{:https://github.com/yurug/kaplan2/blob/main/kb/plan-catenable.md}kb/plan-catenable.md}
      -- the eight-phase catenable plan.

    {2 A note for re-extraction}

    This [.mli] file is the verbatim Coq extraction output (modulo
    this prelude).  When regenerating, run [dune build
    rocq/KTDeque/Extract] from the repo root and copy
    [_build/default/kt_catenable_extracted/kTCatenableDeque.{ml,mli}]
    to this directory, preserving this header.
*)


val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

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

val buf6_concat : 'a1 buf6 -> 'a1 buf6 -> 'a1 buf6

type tripleKind =
| KOnly
| KLeft
| KRight

type 'x triple =
| TOnly of 'x buf6 * 'x cadeque * 'x buf6
| TLeft of 'x buf6 * 'x cadeque * 'x buf6
| TRight of 'x buf6 * 'x cadeque * 'x buf6
and 'x cadeque =
| CEmpty
| CSingle of 'x triple
| CDouble of 'x triple * 'x triple

val triple_kind : 'a1 triple -> tripleKind

type 'x stored =
| StoredSmall of 'x buf6
| StoredBig of 'x buf6 * 'x cadeque * 'x buf6

val cad_empty : 'a1 cadeque

val cad_singleton_only : 'a1 buf6 -> 'a1 cadeque

val flat_concat : ('a2 -> 'a1 list) -> 'a2 list -> 'a1 list

val buf6_flatten : ('a2 -> 'a1 list) -> 'a2 buf6 -> 'a1 list

val triple_to_list : ('a2 -> 'a1 list) -> 'a2 triple -> 'a1 list

val cad_to_list : ('a2 -> 'a1 list) -> 'a2 cadeque -> 'a1 list

val cad_to_list_base : 'a1 cadeque -> 'a1 list

val triple_push_prefix : 'a1 -> 'a1 triple -> 'a1 triple

val triple_inject_suffix : 'a1 triple -> 'a1 -> 'a1 triple

val triple_pop_prefix : 'a1 triple -> ('a1 * 'a1 triple) option

val triple_eject_suffix : 'a1 triple -> ('a1 triple * 'a1) option

val cad_push : 'a1 -> 'a1 cadeque -> 'a1 cadeque

val cad_inject : 'a1 cadeque -> 'a1 -> 'a1 cadeque

val cad_pop : 'a1 cadeque -> ('a1 * 'a1 cadeque) option

val cad_eject : 'a1 cadeque -> ('a1 cadeque * 'a1) option

val cad_from_list : 'a1 list -> 'a1 cadeque

val cad_concat : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque

val cad_size : 'a1 cadeque -> int

val cad_singleton : 'a1 -> 'a1 cadeque

val cad_is_empty : 'a1 cadeque -> bool

val cad_rev : 'a1 cadeque -> 'a1 cadeque

val cad_fold_left : ('a2 -> 'a1 -> 'a2) -> 'a2 -> 'a1 cadeque -> 'a2

val cad_fold_right : ('a1 -> 'a2 -> 'a2) -> 'a1 cadeque -> 'a2 -> 'a2

val normalize_only_empty_child : 'a1 buf6 -> 'a1 buf6 -> 'a1 cadeque

val cad_push_op : 'a1 -> 'a1 cadeque -> 'a1 cadeque

val cad_inject_op : 'a1 cadeque -> 'a1 -> 'a1 cadeque

val cad_pop_op : 'a1 cadeque -> ('a1 * 'a1 cadeque) option

val cad_eject_op : 'a1 cadeque -> ('a1 cadeque * 'a1) option

val cad_concat_op : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque

val cad_from_list_op : 'a1 list -> 'a1 cadeque

val cad_normalize : 'a1 cadeque -> 'a1 cadeque

val cad_pop_op_full : 'a1 cadeque -> ('a1 * 'a1 cadeque) option

val cad_eject_op_full : 'a1 cadeque -> ('a1 cadeque * 'a1) option

val cad_concat_op_full : 'a1 cadeque -> 'a1 cadeque -> 'a1 cadeque
