(** kCadeque8Inline — hand-tuned hot-path push/inject for Cadeque8.

    ## Why this module exists

    [KCadeque8.kcad8_push_fast x k] currently performs *two* cross-
    module function calls per push in the steady-state branch:

      kcad8_push_fast x (K8Simple b)
        → KCadequeShim.buf6_push (XBase8 x) b
          → KTDeque.push_kt4 (ExistT (0, ...)) c

    The OCaml native compiler (without flambda) does *not* inline
    across module boundaries.  Each cross-module hop costs ~2-3 ns
    of dispatch overhead — small per call, but a measurable
    fraction of the residual ~30 ns gap to Viennot's hand-written
    catenable deque.

    This module collapses the chain into a single function defined
    in *one* compilation unit.  The result is one cross-module hop
    per push (only [KTDeque.push_kt4]), with the [XBase8] / [ExistT]
    / [Plain]/[Spilled] wrapping all done intra-module so [ocamlopt]
    can inline [push_chain] and the Plain/Spilled scrutinee.

    ## Semantics

    These operations are sequence-equivalent to the corresponding
    [KCadeque8.kcad8_*_fast] operations.  See the Rocq side
    [rocq/KTDeque/Cadeque8/OpsFast.v] which defines

        Definition kcad8_push_inline   := kcad8_push_fast.
        Definition kcad8_inject_inline := kcad8_inject_fast.

    along with the lemmas [kcad8_push_inline_seq],
    [kcad8_inject_inline_seq], [kcad8_push_inline_wf_strong], and
    [kcad8_inject_inline_wf_strong] (all transferred by reflexivity
    from the [_fast] proofs).  This OCaml file is the trusted
    hand-fused realisation of those Rocq definitions; the Rocq
    extraction emits [KCadeque8.kcad8_push_inline = kcad8_push_fast]
    (a thin alias), and consumers wanting the fused hot path call
    into this module directly to avoid a [KCadequeShim] module
    cycle that an [Extract Constant] override would introduce.

    ## Safety

    The only [Obj.magic] use is for the [Coq_E.t] payload wrapping
    (level 0 = base value), exactly the same pattern as
    [KTDeque.Coq_E.base] in the extracted code.  All structural
    pattern matches operate on declared types. *)

(* Lifted from KCadequeShim — inlined chain push/inject so that the
   hot path is a single intra-module function definition. *)
let push_chain
  : 'k. 'k KTDeque.Coq_E.t -> 'k KTDeque.kChain -> 'k KTDeque.kChain
  = fun elt c ->
  match KTDeque.push_kt4 elt c with
  | KTDeque.PushOk c'  -> c'
  | KTDeque.PushFail   -> failwith "KCadeque8Inline.push_chain: kt4 invariant"

let inject_chain
  : 'k. 'k KTDeque.kChain -> 'k KTDeque.Coq_E.t -> 'k KTDeque.kChain
  = fun c elt ->
  match KTDeque.inject_kt4 c elt with
  | KTDeque.PushOk c'  -> c'
  | KTDeque.PushFail   -> failwith "KCadeque8Inline.inject_chain: kt4 invariant"

(** [kcad8_push_inline x k] — semantically [KCadeque8.kcad8_push_fast x k]. *)
let kcad8_push_inline
  (x : 'a) (k : 'a KCadeque8.kCadeque8) : 'a KCadeque8.kCadeque8 =
  let elt : 'a KCadeque8.kElem8 KTDeque.Coq_E.t =
    KTDeque.ExistT (0, Obj.magic (KCadeque8.XBase8 x))
  in
  match k with
  | KCadeque8.K8Empty ->
      KCadeque8.K8Simple
        (KCadequeShim.Plain (push_chain elt KCadequeShim.empty_chain))
  | KCadeque8.K8Simple b ->
      (match b with
       | KCadequeShim.Plain c ->
           KCadeque8.K8Simple (KCadequeShim.Plain (push_chain elt c))
       | KCadequeShim.Spilled (c, f, ba) ->
           KCadeque8.K8Simple
             (KCadequeShim.Spilled (push_chain elt c, f, ba)))
  | KCadeque8.K8Triple (h, m, t) ->
      (match h with
       | KCadequeShim.Plain c ->
           KCadeque8.K8Triple
             (KCadequeShim.Plain (push_chain elt c), m, t)
       | KCadequeShim.Spilled (c, f, ba) ->
           KCadeque8.K8Triple
             (KCadequeShim.Spilled (push_chain elt c, f, ba), m, t))

(** [kcad8_inject_inline k x] — semantically [KCadeque8.kcad8_inject_fast k x]. *)
let kcad8_inject_inline
  (k : 'a KCadeque8.kCadeque8) (x : 'a) : 'a KCadeque8.kCadeque8 =
  let elt : 'a KCadeque8.kElem8 KTDeque.Coq_E.t =
    KTDeque.ExistT (0, Obj.magic (KCadeque8.XBase8 x))
  in
  match k with
  | KCadeque8.K8Empty ->
      KCadeque8.K8Simple
        (KCadequeShim.Plain (inject_chain KCadequeShim.empty_chain elt))
  | KCadeque8.K8Simple b ->
      (match b with
       | KCadequeShim.Plain c ->
           KCadeque8.K8Simple (KCadequeShim.Plain (inject_chain c elt))
       | KCadequeShim.Spilled (c, f, ba) ->
           KCadeque8.K8Simple
             (KCadequeShim.Spilled (inject_chain c elt, f, ba)))
  | KCadeque8.K8Triple (h, m, t) ->
      (match t with
       | KCadequeShim.Plain c ->
           KCadeque8.K8Triple
             (h, m, KCadequeShim.Plain (inject_chain c elt))
       | KCadequeShim.Spilled (c, f, ba) ->
           KCadeque8.K8Triple
             (h, m, KCadequeShim.Spilled (inject_chain c elt, f, ba)))

(* -------------------------------------------------------------------------- *
 * Pop / eject inline — bypass [buf6_pop] (which allocates an [option]) and
 * the [Coq_E.to_list] singleton list (which allocates a cons cell per call).
 *
 * Strategy: for the [K8Simple (Plain c)] and [K8Triple (Plain h, m, t)] hot
 * paths, where the boundary element is a level-0 [XBase8] (true in steady
 * state by the maintained invariant), we destructure the [Coq_E.t] [ExistT]
 * directly and read the payload via [Obj.magic].  Any case that wouldn't be
 * handled by this fast path (a [Spilled] buffer, a deeper-level [Coq_E.t],
 * an [XStored8], an empty [h] that needs rebalance, ...) falls back to the
 * fully-general [KCadeque8.kcad8_pop_fast].
 *)

(** [chain_is_empty c] — [true] iff [c] is the empty chain.  In a well-formed
    [kChain] this is exactly [KEnding B0]; [pop_kt4] returns [PopFail] on this
    and only this canonical empty state, so we match it directly to avoid a
    second [pop_kt4] call. *)
let chain_is_empty : 'a. 'a KTDeque.kChain -> bool = function
  | KTDeque.KEnding KTDeque.B0 -> true
  | _ -> false

(** [kcad8_pop_inline k] — semantically [KCadeque8.kcad8_pop_fast k]. *)
let kcad8_pop_inline
  (k : 'a KCadeque8.kCadeque8) : 'a KCadeque8.pop_result8 =
  match k with
  | KCadeque8.K8Empty -> KCadeque8.PopFail8
  | KCadeque8.K8Simple (KCadequeShim.Plain c) ->
      (match KTDeque.pop_kt4 c with
       | KTDeque.PopFail -> KCadeque8.PopFail8
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), c') when lvl = 0 ->
           let elem : 'a KCadeque8.kElem8 = Obj.magic payload in
           (match elem with
            | KCadeque8.XBase8 x ->
                let rest =
                  if chain_is_empty c'
                  then KCadeque8.K8Empty
                  else KCadeque8.K8Simple (KCadequeShim.Plain c')
                in
                KCadeque8.PopOk8 (x, rest)
            | KCadeque8.XStored8 _ -> KCadeque8.kcad8_pop_fast k)
       | KTDeque.PopOk _ -> KCadeque8.kcad8_pop_fast k)
  | KCadeque8.K8Triple (KCadequeShim.Plain h, m, t) ->
      (match KTDeque.pop_kt4 h with
       | KTDeque.PopFail -> KCadeque8.kcad8_pop_fast k  (* needs rebalance *)
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), h') when lvl = 0 ->
           let elem : 'a KCadeque8.kElem8 = Obj.magic payload in
           (match elem with
            | KCadeque8.XBase8 x ->
                if chain_is_empty h'
                then KCadeque8.kcad8_pop_fast k  (* h emptied, rebalance *)
                else KCadeque8.PopOk8
                       (x, KCadeque8.K8Triple
                             (KCadequeShim.Plain h', m, t))
            | KCadeque8.XStored8 _ -> KCadeque8.kcad8_pop_fast k)
       | KTDeque.PopOk _ -> KCadeque8.kcad8_pop_fast k)
  | _ -> KCadeque8.kcad8_pop_fast k

(** [kcad8_eject_inline k] — semantically [KCadeque8.kcad8_eject_fast k]. *)
let kcad8_eject_inline
  (k : 'a KCadeque8.kCadeque8) : 'a KCadeque8.eject_result8 =
  match k with
  | KCadeque8.K8Empty -> KCadeque8.EjectFail8
  | KCadeque8.K8Simple (KCadequeShim.Plain c) ->
      (match KTDeque.eject_kt4 c with
       | KTDeque.PopFail -> KCadeque8.EjectFail8
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), c') when lvl = 0 ->
           let elem : 'a KCadeque8.kElem8 = Obj.magic payload in
           (match elem with
            | KCadeque8.XBase8 x ->
                let rest =
                  if chain_is_empty c'
                  then KCadeque8.K8Empty
                  else KCadeque8.K8Simple (KCadequeShim.Plain c')
                in
                KCadeque8.EjectOk8 (rest, x)
            | KCadeque8.XStored8 _ -> KCadeque8.kcad8_eject_fast k)
       | KTDeque.PopOk _ -> KCadeque8.kcad8_eject_fast k)
  | KCadeque8.K8Triple (h, m, KCadequeShim.Plain t) ->
      (match KTDeque.eject_kt4 t with
       | KTDeque.PopFail -> KCadeque8.kcad8_eject_fast k
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), t') when lvl = 0 ->
           let elem : 'a KCadeque8.kElem8 = Obj.magic payload in
           (match elem with
            | KCadeque8.XBase8 x ->
                if chain_is_empty t'
                then KCadeque8.kcad8_eject_fast k
                else KCadeque8.EjectOk8
                       (KCadeque8.K8Triple
                          (h, m, KCadequeShim.Plain t'), x)
            | KCadeque8.XStored8 _ -> KCadeque8.kcad8_eject_fast k)
       | KTDeque.PopOk _ -> KCadeque8.kcad8_eject_fast k)
  | _ -> KCadeque8.kcad8_eject_fast k
