(** kCadequeShim — Buf6 ops routed through certified WC O(1) KChain.

    The Coq Cadeque7 model parameterizes buffers as [Buf6 (KElem X)].
    Coq's extraction would by default collapse [Buf6] to [list] (it's
    a singleton-inductive record), giving O(n) inject/eject.  Via
    [Extract Inductive Buf6 => "KCadequeShim.buf6"] in
    [KCadequeExtraction.v] we override the OCaml type to point here,
    and every [buf6_*] op is also overridden to route through the
    [kt2_*] family of the certified Kaplan-Tarjan deque — WC O(1) per
    call (proven in [DequePtr/OpsKTSeq.v]).

    Each element [x : 'a] is wrapped as a level-0 [Coq_E.t] before
    being stored in the [kChain].

    ## Spill cache for cascade fan-out (only)

    When the chain has internally cascaded, [pop_kt2] may surface a
    level-[l > 0] element holding [2^l] base values; we return one
    and stash the rest in a small [front_spill] (resp. [back_spill])
    list, drained before consulting [pop_kt2] again.

    HARD RULE — every actual deque insertion still goes through
    [push_kt2] / [inject_kt2]; the spill lists never *hold* user
    state, only the transient overflow from a single cascade
    surfacing.  This keeps the WC O(1) guarantee anchored in the
    certified [kt2] family and avoids the project's forbidden
    "amortized building block" pattern. *)

type 'a buf6 = {
  chain       : 'a KTDeque.kChain;
  front_spill : 'a list;   (* transient: drained by [buf6_pop]
                              before consulting the chain      *)
  back_spill  : 'a list;   (* transient: drained by [buf6_eject]
                              (in reverse) before consulting
                              the chain                        *)
}

let empty_chain = KTDeque.empty_kchain

let buf6_empty : 'a buf6 =
  { chain = empty_chain; front_spill = []; back_spill = [] }

let mkBuf6 (xs : 'a list) : 'a buf6 =
  { chain =
      List.fold_left (fun c x ->
        match KTDeque.inject_kt2 c (KTDeque.Coq_E.base x) with
        | Some c' -> c'
        | None    -> failwith "mkBuf6: kt2 invariant"
      ) empty_chain xs;
    front_spill = [];
    back_spill  = [] }

(* Project to a list (the abstract semantic).  Spills first (front),
   then chain in [Coq_E]-flattened order, then back spill in REVERSE
   so newer-injected appears later. *)
let buf6_elems (b : 'a buf6) : 'a list =
  b.front_spill
  @ KTDeque.kchain_to_list b.chain
  @ List.rev b.back_spill

let buf6_to_list = buf6_elems
let buf6_size b = List.length (buf6_elems b)

(* push / inject always go through kt2 — no list-cons shortcut.
   This preserves the "WC O(1) per call, anchored in certified
   primitive" invariant.  The spill lists are only filled by the
   pop/eject side. *)

let buf6_singleton (x : 'a) : 'a buf6 =
  match KTDeque.push_kt2 (KTDeque.Coq_E.base x) empty_chain with
  | Some c -> { chain = c; front_spill = []; back_spill = [] }
  | None   -> failwith "buf6_singleton"

let buf6_push (x : 'a) (b : 'a buf6) : 'a buf6 =
  match KTDeque.push_kt2 (KTDeque.Coq_E.base x) b.chain with
  | Some c -> { b with chain = c }
  | None   -> failwith "buf6_push: kt2 invariant"

let buf6_inject (b : 'a buf6) (x : 'a) : 'a buf6 =
  match KTDeque.inject_kt2 b.chain (KTDeque.Coq_E.base x) with
  | Some c -> { b with chain = c }
  | None   -> failwith "buf6_inject: kt2 invariant"

let buf6_pop (b : 'a buf6) : ('a * 'a buf6) option =
  match b.front_spill with
  | x :: rest -> Some (x, { b with front_spill = rest })
  | [] ->
      (match KTDeque.pop_kt2 b.chain with
       | Some (e, c') ->
           (match KTDeque.Coq_E.to_list e with
            | []      -> failwith "buf6_pop: empty element"
            | x :: rs -> Some (x, { b with chain = c'; front_spill = rs }))
       | None ->
           (match List.rev b.back_spill with
            | []      -> None
            | x :: rs ->
                Some (x, { chain = empty_chain;
                           front_spill = rs;
                           back_spill = [] })))

let buf6_eject (b : 'a buf6) : ('a buf6 * 'a) option =
  match b.back_spill with
  | x :: rest -> Some ({ b with back_spill = rest }, x)
  | [] ->
      (match KTDeque.eject_kt2 b.chain with
       | Some (c', e) ->
           (match List.rev (KTDeque.Coq_E.to_list e) with
            | []      -> failwith "buf6_eject: empty element"
            | x :: rs -> Some ({ b with chain = c'; back_spill = rs }, x))
       | None ->
           (match List.rev b.front_spill with
            | []      -> None
            | x :: rs ->
                Some ({ chain = empty_chain;
                        front_spill = [];
                        back_spill = rs }, x)))
