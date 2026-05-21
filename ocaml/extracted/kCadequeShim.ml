(** kCadequeShim — Buf6 ops routed through certified WC O(1) KChain.

    Buf6 is overridden via [Extract Inductive Buf6 => ...] in
    [KCadeque8Extraction.v].  This file provides the OCaml side.

    ## Compact two-constructor representation

    Common case: [buf6] is just a [kChain] (no spill).  We use a
    flat 2-constructor sum so the common case fits in 2 words
    (tag + chain pointer) instead of 4 (3-field record).

    Rare case: [pop_kt4] surfaces a level-[l > 0] element holding
    [2^l] base values; we return one and stash the rest in a small
    spill list — at most one such spill in flight per side under
    the maintained invariant.

    Every actual deque insertion still goes through [push_kt4] /
    [inject_kt4]; the spill lists never *hold* user state, only
    the transient overflow from a single cascade surfacing.

    The kt4-family (no-option result types) is used throughout —
    saves one heap allocation per buf6 op compared to the option-
    returning kt2 family.

    ## Closure-free hot path

    The push/inject body avoids a local [let push_chain = ...]
    closure that would capture [x] and allocate ~3 words per call.
    The match-on-buf6 is split into two arms that each inline the
    [push_kt4] call directly, so [x] stays on the stack.

    ## Inlined level-0 [ExistT] wrap

    [KTDeque.Coq_E.base x] is just [ExistT (0, Obj.magic x)] but
    crosses a module boundary (no flambda → no cross-module
    inlining).  We allocate the [ExistT] inline at the buf6 op
    site so the only cross-module call per push/inject is the
    single [push_kt4]/[inject_kt4] dispatch. *)

type 'a buf6 =
  | Plain   of 'a KTDeque.kChain
    (** the common case: no spill state *)
  | Spilled of 'a KTDeque.kChain * 'a list * 'a list
    (** [Spilled (chain, front_spill, back_spill)]:
        front_spill drained left-first; back_spill drained
        in reverse (newer-injected appears last). *)

let empty_chain = KTDeque.empty_kchain

let buf6_empty : 'a buf6 = Plain empty_chain

(** [chain_of b] and [front_of b] / [back_of b] — accessors used
    in the rest of the shim.  Only [chain_of] is on the hot path;
    the spill accessors are only consulted in the rare branch. *)
let chain_of : 'a buf6 -> 'a KTDeque.kChain = function
  | Plain c              -> c
  | Spilled (c, _, _)    -> c

let mkBuf6 (xs : 'a list) : 'a buf6 =
  Plain
    (List.fold_left (fun c x ->
       match KTDeque.inject_kt4 c (KTDeque.Coq_E.base x) with
       | KTDeque.PushOk c' -> c'
       | KTDeque.PushFail  -> failwith "mkBuf6: kt4 invariant"
     ) empty_chain xs)

(** Project to a list (the abstract semantic). *)
let buf6_elems (b : 'a buf6) : 'a list =
  match b with
  | Plain c                     -> KTDeque.kchain_to_list c
  | Spilled (c, front, back)    ->
      front @ KTDeque.kchain_to_list c @ List.rev back

let buf6_to_list = buf6_elems
let buf6_size b = List.length (buf6_elems b)

(** O(1) emptiness check. *)
let buf6_is_empty (b : 'a buf6) : bool =
  match b with
  | Plain c ->
      (match KTDeque.pop_kt4 c with
       | KTDeque.PopFail   -> true
       | KTDeque.PopOk _   -> false)
  | Spilled (c, front, back) ->
      (match front, back with
       | _ :: _, _   -> false
       | _, _ :: _   -> false
       | [], []      ->
           (match KTDeque.pop_kt4 c with
            | KTDeque.PopFail -> true
            | KTDeque.PopOk _ -> false))

(* ============================================================== *
 * push / inject — always go through kt4.  Hot path is Plain.     *
 * No local closures: the [push_kt4] / [inject_kt4] call site is  *
 * inlined into each arm so [x] stays on the stack.               *)

let buf6_singleton (x : 'a) : 'a buf6 =
  match KTDeque.push_kt4 (KTDeque.Coq_E.base x) empty_chain with
  | KTDeque.PushOk c -> Plain c
  | KTDeque.PushFail -> failwith "buf6_singleton"

let buf6_push (x : 'a) (b : 'a buf6) : 'a buf6 =
  let elt : 'a KTDeque.Coq_E.t = KTDeque.ExistT (0, (Obj.magic x : 'a KTDeque.xpow)) in
  match b with
  | Plain c ->
      (match KTDeque.push_kt4 elt c with
       | KTDeque.PushOk c'  -> Plain c'
       | KTDeque.PushFail   -> failwith "buf6_push: kt4 invariant")
  | Spilled (c, front, back) ->
      (match KTDeque.push_kt4 elt c with
       | KTDeque.PushOk c'  -> Spilled (c', front, back)
       | KTDeque.PushFail   -> failwith "buf6_push: kt4 invariant")

let buf6_inject (b : 'a buf6) (x : 'a) : 'a buf6 =
  let elt : 'a KTDeque.Coq_E.t = KTDeque.ExistT (0, (Obj.magic x : 'a KTDeque.xpow)) in
  match b with
  | Plain c ->
      (match KTDeque.inject_kt4 c elt with
       | KTDeque.PushOk c'  -> Plain c'
       | KTDeque.PushFail   -> failwith "buf6_inject: kt4 invariant")
  | Spilled (c, front, back) ->
      (match KTDeque.inject_kt4 c elt with
       | KTDeque.PushOk c'  -> Spilled (c', front, back)
       | KTDeque.PushFail   -> failwith "buf6_inject: kt4 invariant")

(* ============================================================== *
 * pop / eject — kt4 + spill management.  Plain is the hot path.  *)

let buf6_pop (b : 'a buf6) : ('a * 'a buf6) option =
  match b with
  | Plain c ->
      (match KTDeque.pop_kt4 c with
       | KTDeque.PopOk (e, c') ->
           (match KTDeque.Coq_E.to_list e with
            | []       -> failwith "buf6_pop: empty element"
            | [x]      -> Some (x, Plain c')   (* common case *)
            | x :: rs  -> Some (x, Spilled (c', rs, [])))
       | KTDeque.PopFail -> None)
  | Spilled (c, front, back) ->
      (match front with
       | x :: rest ->
           Some (x, (match rest, back with
                     | [], []  -> Plain c
                     | _, _    -> Spilled (c, rest, back)))
       | [] ->
           (match KTDeque.pop_kt4 c with
            | KTDeque.PopOk (e, c') ->
                (match KTDeque.Coq_E.to_list e with
                 | []       -> failwith "buf6_pop: empty element"
                 | [x]      -> Some (x, (match back with
                                         | [] -> Plain c'
                                         | _  -> Spilled (c', [], back)))
                 | x :: rs  -> Some (x, Spilled (c', rs, back)))
            | KTDeque.PopFail ->
                (match List.rev back with
                 | []      -> None
                 | x :: rs ->
                     Some (x, (match rs with
                               | [] -> Plain empty_chain
                               | _  -> Spilled (empty_chain, rs, []))))))

let buf6_eject (b : 'a buf6) : ('a buf6 * 'a) option =
  match b with
  | Plain c ->
      (match KTDeque.eject_kt4 c with
       | KTDeque.PopOk (e, c') ->
           (match List.rev (KTDeque.Coq_E.to_list e) with
            | []       -> failwith "buf6_eject: empty element"
            | [x]      -> Some (Plain c', x)
            | x :: rs  -> Some (Spilled (c', [], rs), x))
       | KTDeque.PopFail -> None)
  | Spilled (c, front, back) ->
      (match back with
       | x :: rest ->
           Some ((match front, rest with
                  | [], []  -> Plain c
                  | _, _    -> Spilled (c, front, rest)), x)
       | [] ->
           (match KTDeque.eject_kt4 c with
            | KTDeque.PopOk (e, c') ->
                (match List.rev (KTDeque.Coq_E.to_list e) with
                 | []       -> failwith "buf6_eject: empty element"
                 | [x]      -> Some ((match front with
                                       | [] -> Plain c'
                                       | _  -> Spilled (c', front, [])), x)
                 | x :: rs  -> Some (Spilled (c', front, rs), x))
            | KTDeque.PopFail ->
                (match List.rev front with
                 | []      -> None
                 | x :: rs ->
                     Some ((match rs with
                            | [] -> Plain empty_chain
                            | _  -> Spilled (empty_chain, [], rs)), x))))
