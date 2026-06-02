(** kCadequeShim — Buf6 ops routed through certified WC O(1) KChain.

    Buf6 is overridden via [Extract Inductive Buf6 => ...] in
    [KCadeque8Extraction.v].  This file provides the OCaml side.

    ## Compact two-constructor representation

    Common case: [buf6] is a cached logical length plus a [kChain]
    (no spill).  The cached length is required because catenable
    operations inspect [buf6_size] on hot paths; deriving it from
    [buf6_elems] would traverse the whole buffer.

    Rare case: [pop_kt4] surfaces a level-[l > 0] element holding
    [2^l] base values; we return one and keep the rest as a small
    forest of element subtrees.  Draining that spill peels one base
    value at a time instead of flattening the whole surfaced element
    in one operation.

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
  | Plain   of int * 'a KTDeque.kChain
    (** the common case: no spill state *)
  | Spilled of int * 'a KTDeque.kChain * 'a KTDeque.Coq_E.t list
       * 'a KTDeque.Coq_E.t list
    (** [Spilled (len, chain, front_spill, back_spill)]:
        [len] is the logical number of values represented by all parts.
        front_spill is a front-to-back forest; back_spill is a
        back-to-front forest. *)

let empty_chain = KTDeque.empty_kchain

let buf6_empty : 'a buf6 = Plain (0, empty_chain)

(** [chain_of b] and [front_of b] / [back_of b] — accessors used
    in the rest of the shim.  Only [chain_of] is on the hot path;
    the spill accessors are only consulted in the rare branch. *)
let chain_of : 'a buf6 -> 'a KTDeque.kChain = function
  | Plain (_, c)              -> c
  | Spilled (_, c, _, _)      -> c

let mkBuf6 (xs : 'a list) : 'a buf6 =
  Plain
    (List.length xs,
     List.fold_left (fun c x ->
       match KTDeque.inject_kt4 c (KTDeque.Coq_E.base x) with
       | KTDeque.PushOk c' -> c'
       | KTDeque.PushFail  -> failwith "mkBuf6: kt4 invariant"
     ) empty_chain xs)

let base_of_level0 = function
  | KTDeque.ExistT (0, p) -> (Obj.magic p : 'a)
  | _ -> failwith "KCadequeShim: expected level-0 element"

let unpair_exn e =
  match KTDeque.Coq_E.unpair e with
  | Some (l, r) -> (l, r)
  | None -> failwith "KCadequeShim: malformed positive-level element"

let rec pop_front_tree e =
  match e with
  | KTDeque.ExistT (0, _) -> (base_of_level0 e, [])
  | _ ->
      let left, right = unpair_exn e in
      let x, rest = pop_front_tree left in
      (x, rest @ [right])

let rec pop_back_tree e =
  match e with
  | KTDeque.ExistT (0, _) -> (base_of_level0 e, [])
  | _ ->
      let left, right = unpair_exn e in
      let x, rest = pop_back_tree right in
      (x, rest @ [left])

let rec pop_front_forest = function
  | [] -> None
  | e :: es ->
      let x, rest = pop_front_tree e in
      Some (x, rest @ es)

let rec pop_back_forest = function
  | [] -> None
  | e :: es ->
      let x, rest = pop_back_tree e in
      Some (x, rest @ es)

let rec pop_front_from_back_forest = function
  | [] -> None
  | [e] ->
      let x, rest = pop_front_tree e in
      Some (x, rest)
  | e :: es ->
      (match pop_front_from_back_forest es with
       | None -> None
       | Some (x, rest) -> Some (x, e :: rest))

let rec pop_back_from_front_forest = function
  | [] -> None
  | [e] ->
      let x, rest = pop_back_tree e in
      Some (x, rest)
  | e :: es ->
      (match pop_back_from_front_forest es with
       | None -> None
       | Some (x, rest) -> Some (x, e :: rest))

let buf6_of_parts len c front back =
  match front, back with
  | [], [] -> Plain (len, c)
  | _ -> Spilled (len, c, front, back)

let rec forest_to_list = function
  | [] -> []
  | tree :: rest -> KTDeque.Coq_E.to_list tree @ forest_to_list rest

(** Project to a list (the abstract semantic). *)
let buf6_elems (b : 'a buf6) : 'a list =
  match b with
  | Plain (_, c)                     -> KTDeque.kchain_to_list c
  | Spilled (_, c, front, back)      ->
      forest_to_list front @ KTDeque.kchain_to_list c
      @ List.rev (forest_to_list back)

let buf6_to_list = buf6_elems
let buf6_size = function
  | Plain (len, _) -> len
  | Spilled (len, _, _, _) -> len

(** O(1) emptiness check. *)
let buf6_is_empty (b : 'a buf6) : bool =
  buf6_size b = 0

(* ============================================================== *
 * push / inject — always go through kt4.  Hot path is Plain.     *
 * No local closures: the [push_kt4] / [inject_kt4] call site is  *
 * inlined into each arm so [x] stays on the stack.               *)

let buf6_singleton (x : 'a) : 'a buf6 =
  match KTDeque.push_kt4 (KTDeque.Coq_E.base x) empty_chain with
  | KTDeque.PushOk c -> Plain (1, c)
  | KTDeque.PushFail -> failwith "buf6_singleton"

let buf6_push (x : 'a) (b : 'a buf6) : 'a buf6 =
  let elt : 'a KTDeque.Coq_E.t = KTDeque.ExistT (0, (Obj.magic x : 'a KTDeque.xpow)) in
  match b with
  | Plain (len, c) ->
      (match KTDeque.push_kt4 elt c with
       | KTDeque.PushOk c'  -> Plain (len + 1, c')
       | KTDeque.PushFail   -> failwith "buf6_push: kt4 invariant")
  | Spilled (len, c, front, back) ->
      (match KTDeque.push_kt4 elt c with
       | KTDeque.PushOk c'  -> Spilled (len + 1, c', front, back)
       | KTDeque.PushFail   -> failwith "buf6_push: kt4 invariant")

let buf6_inject (b : 'a buf6) (x : 'a) : 'a buf6 =
  let elt : 'a KTDeque.Coq_E.t = KTDeque.ExistT (0, (Obj.magic x : 'a KTDeque.xpow)) in
  match b with
  | Plain (len, c) ->
      (match KTDeque.inject_kt4 c elt with
       | KTDeque.PushOk c'  -> Plain (len + 1, c')
       | KTDeque.PushFail   -> failwith "buf6_inject: kt4 invariant")
  | Spilled (len, c, front, back) ->
      (match KTDeque.inject_kt4 c elt with
       | KTDeque.PushOk c'  -> Spilled (len + 1, c', front, back)
       | KTDeque.PushFail   -> failwith "buf6_inject: kt4 invariant")

(* ============================================================== *
 * pop / eject — kt4 + spill management.  Plain is the hot path.  *)

let buf6_pop (b : 'a buf6) : ('a * 'a buf6) option =
  match b with
  | Plain (len, c) ->
      (match KTDeque.pop_kt4 c with
       | KTDeque.PopOk (e, c') ->
           let len' = len - 1 in
           let x, front = pop_front_tree e in
           Some (x, buf6_of_parts len' c' front [])
       | KTDeque.PopFail -> None)
  | Spilled (len, c, front, back) ->
      (match pop_front_forest front with
       | Some (x, rest) ->
           let len' = len - 1 in
           Some (x, buf6_of_parts len' c rest back)
       | None ->
           (match KTDeque.pop_kt4 c with
            | KTDeque.PopOk (e, c') ->
                let len' = len - 1 in
                let x, front' = pop_front_tree e in
                Some (x, buf6_of_parts len' c' front' back)
            | KTDeque.PopFail ->
                (match pop_front_from_back_forest back with
                 | None -> None
                 | Some (x, front') ->
                     let len' = len - 1 in
                     Some (x, buf6_of_parts len' empty_chain front' []))))

let buf6_eject (b : 'a buf6) : ('a buf6 * 'a) option =
  match b with
  | Plain (len, c) ->
      (match KTDeque.eject_kt4 c with
       | KTDeque.PopOk (e, c') ->
           let len' = len - 1 in
           let x, back = pop_back_tree e in
           Some (buf6_of_parts len' c' [] back, x)
       | KTDeque.PopFail -> None)
  | Spilled (len, c, front, back) ->
      (match pop_back_forest back with
       | Some (x, rest) ->
           let len' = len - 1 in
           Some (buf6_of_parts len' c front rest, x)
       | None ->
           (match KTDeque.eject_kt4 c with
            | KTDeque.PopOk (e, c') ->
                let len' = len - 1 in
                let x, back' = pop_back_tree e in
                Some (buf6_of_parts len' c' front back', x)
            | KTDeque.PopFail ->
                (match pop_back_from_front_forest front with
                 | None -> None
                 | Some (x, back') ->
                     let len' = len - 1 in
                     Some (buf6_of_parts len' empty_chain [] back', x))))
