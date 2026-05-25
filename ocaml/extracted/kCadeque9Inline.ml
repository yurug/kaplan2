(** kCadeque9Inline — hand-fused OCaml hot paths for Cadeque9.

    Mirrors [KCadeque8Inline.ml]'s approach: collapse the
    cross-module chain (Cadeque9 → KCadequeShim → KTDeque) into
    a single function defined intra-module, so ocamlopt can inline
    the helper calls and the constructor matches.

    Semantically equivalent to [KCadeque9.kcad9_*_fast], which are
    in turn definitionally equal to [KCadeque9.kcad9_*] (proven in
    [rocq/KTDeque/Cadeque9/OpsFast.v]).

    Performance target: match or beat [KCadeque8Inline] on the
    push/pop/inject/eject hot paths, with the added benefit of
    structural WC O(1) on (T+T) concat (the bug Cadeque8 still
    has).  Concat is NOT inlined — it relies on buf6_concat for
    the (T+T) case anyway.

    Safety: the only [Obj.magic] use is for the [Coq_E.t] payload
    wrapping (level 0 = base value).  Sound under the maintained
    invariant that all boundary buffers hold only [XBase9 _]. *)

(* Inlined chain primitives. *)
let push_chain
  : 'k. 'k KTDeque.Coq_E.t -> 'k KTDeque.kChain -> 'k KTDeque.kChain
  = fun elt c ->
  match KTDeque.push_kt4 elt c with
  | KTDeque.PushOk c'  -> c'
  | KTDeque.PushFail   -> failwith "KCadeque9Inline.push_chain: kt4 invariant"

let inject_chain
  : 'k. 'k KTDeque.kChain -> 'k KTDeque.Coq_E.t -> 'k KTDeque.kChain
  = fun c elt ->
  match KTDeque.inject_kt4 c elt with
  | KTDeque.PushOk c'  -> c'
  | KTDeque.PushFail   -> failwith "KCadeque9Inline.inject_chain: kt4 invariant"

let chain_is_empty : 'a. 'a KTDeque.kChain -> bool = function
  | KTDeque.KEnding KTDeque.B0 -> true
  | _ -> false

(* -------------------------------------------------------------------------- *
 * Push / inject — same idea as Cadeque8 inline: inline the ExistT wrap and
 * the chain push call site so the compiler can shrink the dispatch.
 *)

let kcad9_push_inline
  (x : 'a) (k : 'a KCadeque9.kCadeque9) : 'a KCadeque9.kCadeque9 =
  let elt : 'a KCadeque9.kElem9 KTDeque.Coq_E.t =
    KTDeque.ExistT (0, Obj.magic (KCadeque9.XBase9 x))
  in
  match k with
  | KCadeque9.K9Empty ->
      KCadeque9.K9Simple
        (KCadequeShim.Plain (1, push_chain elt KCadequeShim.empty_chain))
  | KCadeque9.K9Simple b ->
      (match b with
       | KCadequeShim.Plain (len, c) ->
           KCadeque9.K9Simple (KCadequeShim.Plain (len + 1, push_chain elt c))
       | KCadequeShim.Spilled (len, c, f, ba) ->
           KCadeque9.K9Simple
             (KCadequeShim.Spilled (len + 1, push_chain elt c, f, ba)))
  | KCadeque9.K9Triple (h, m, t) ->
      (match h with
       | KCadequeShim.Plain (len, c) ->
           KCadeque9.K9Triple
             (KCadequeShim.Plain (len + 1, push_chain elt c), m, t)
       | KCadequeShim.Spilled (len, c, f, ba) ->
           KCadeque9.K9Triple
             (KCadequeShim.Spilled (len + 1, push_chain elt c, f, ba), m, t))

let kcad9_inject_inline
  (k : 'a KCadeque9.kCadeque9) (x : 'a) : 'a KCadeque9.kCadeque9 =
  let elt : 'a KCadeque9.kElem9 KTDeque.Coq_E.t =
    KTDeque.ExistT (0, Obj.magic (KCadeque9.XBase9 x))
  in
  match k with
  | KCadeque9.K9Empty ->
      KCadeque9.K9Simple
        (KCadequeShim.Plain (1, inject_chain KCadequeShim.empty_chain elt))
  | KCadeque9.K9Simple b ->
      (match b with
       | KCadequeShim.Plain (len, c) ->
           KCadeque9.K9Simple (KCadequeShim.Plain (len + 1, inject_chain c elt))
       | KCadequeShim.Spilled (len, c, f, ba) ->
           KCadeque9.K9Simple
             (KCadequeShim.Spilled (len + 1, inject_chain c elt, f, ba)))
  | KCadeque9.K9Triple (h, m, t) ->
      (match t with
       | KCadequeShim.Plain (len, c) ->
           KCadeque9.K9Triple
             (h, m, KCadequeShim.Plain (len + 1, inject_chain c elt))
       | KCadequeShim.Spilled (len, c, f, ba) ->
           KCadeque9.K9Triple
             (h, m, KCadequeShim.Spilled (len + 1, inject_chain c elt, f, ba)))

(* -------------------------------------------------------------------------- *
 * Pop / eject inline — bypass [buf6_pop] (option-box) and [Coq_E.to_list]
 * (singleton list).  Steady-state path: K9Simple (Plain c) or K9Triple
 * (Plain h, m, t) with size ≥ 6 (no refill).  Anything else falls back to
 * [KCadeque9.kcad9_pop_fast] (which is the certified general path).
 *)

let kcad9_pop_inline
  (k : 'a KCadeque9.kCadeque9) : 'a KCadeque9.pop_result9 =
  match k with
  | KCadeque9.K9Empty -> KCadeque9.PopFail9
  | KCadeque9.K9Simple (KCadequeShim.Plain (len, c)) ->
      (match KTDeque.pop_kt4 c with
       | KTDeque.PopFail -> KCadeque9.PopFail9
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), c') when lvl = 0 ->
           let elem : 'a KCadeque9.kElem9 = Obj.magic payload in
           (match elem with
            | KCadeque9.XBase9 x ->
                let rest =
                  if len <= 1
                  then KCadeque9.K9Empty
                  else KCadeque9.K9Simple (KCadequeShim.Plain (len - 1, c'))
                in
                KCadeque9.PopOk9 (x, rest)
            | KCadeque9.XStored9 _ -> KCadeque9.kcad9_pop_fast k)
       | KTDeque.PopOk _ -> KCadeque9.kcad9_pop_fast k)
  | KCadeque9.K9Triple (KCadequeShim.Plain (len, h), m, t) ->
      (* Hot path: |h| >= 6 means the post-pop head still satisfies
         the Cadeque9 boundary invariant.  If |h| <= 5, the certified
         path performs the required refill. *)
      (match KTDeque.pop_kt4 h with
       | KTDeque.PopFail -> KCadeque9.kcad9_pop_fast k
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), h') when lvl = 0 ->
           let elem : 'a KCadeque9.kElem9 = Obj.magic payload in
           (match elem with
            | KCadeque9.XBase9 x ->
                if len <= 5 || chain_is_empty h' then
                  KCadeque9.kcad9_pop_fast k
                else
                  KCadeque9.PopOk9
                    (x, KCadeque9.K9Triple
                          (KCadequeShim.Plain (len - 1, h'), m, t))
            | KCadeque9.XStored9 _ -> KCadeque9.kcad9_pop_fast k)
       | KTDeque.PopOk _ -> KCadeque9.kcad9_pop_fast k)
  | _ -> KCadeque9.kcad9_pop_fast k

let kcad9_eject_inline
  (k : 'a KCadeque9.kCadeque9) : 'a KCadeque9.eject_result9 =
  match k with
  | KCadeque9.K9Empty -> KCadeque9.EjectFail9
  | KCadeque9.K9Simple (KCadequeShim.Plain (len, c)) ->
      (match KTDeque.eject_kt4 c with
       | KTDeque.PopFail -> KCadeque9.EjectFail9
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), c') when lvl = 0 ->
           let elem : 'a KCadeque9.kElem9 = Obj.magic payload in
           (match elem with
            | KCadeque9.XBase9 x ->
                let rest =
                  if len <= 1
                  then KCadeque9.K9Empty
                  else KCadeque9.K9Simple (KCadequeShim.Plain (len - 1, c'))
                in
                KCadeque9.EjectOk9 (rest, x)
            | KCadeque9.XStored9 _ -> KCadeque9.kcad9_eject_fast k)
       | KTDeque.PopOk _ -> KCadeque9.kcad9_eject_fast k)
  | KCadeque9.K9Triple (h, m, KCadequeShim.Plain (len, t)) ->
      (match KTDeque.eject_kt4 t with
       | KTDeque.PopFail -> KCadeque9.kcad9_eject_fast k
       | KTDeque.PopOk (KTDeque.ExistT (lvl, payload), t') when lvl = 0 ->
           let elem : 'a KCadeque9.kElem9 = Obj.magic payload in
           (match elem with
            | KCadeque9.XBase9 x ->
                if len <= 5 || chain_is_empty t' then
                  KCadeque9.kcad9_eject_fast k
                else
                  KCadeque9.EjectOk9
                    (KCadeque9.K9Triple
                       (h, m, KCadequeShim.Plain (len - 1, t')), x)
            | KCadeque9.XStored9 _ -> KCadeque9.kcad9_eject_fast k)
       | KTDeque.PopOk _ -> KCadeque9.kcad9_eject_fast k)
  | _ -> KCadeque9.kcad9_eject_fast k
