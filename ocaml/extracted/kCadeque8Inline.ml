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
