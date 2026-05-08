(** Hand-written OCaml Deque4: amortised O(log n) persistent deque.

    ## Role in the project

    This is *not* the production deque.  It is the **amortised
    contrast** that lets benchmarks demonstrate the value of the
    KT99 worst-case O(1) discipline used in the production code
    ([ocaml/extracted/kTDeque.ml] / [c/src/ktdeque_dequeptr.c]).

    Specifically:

    - In the bench harness's scaling sweep
      ({{:https://github.com/yurug/kaplan2/blob/main/bench/sweep.sh}bench/sweep.sh}),
      D4 looks competitive with the WC-O(1) KT and Viennot impls on
      most ops, sometimes even faster — because amortisation works
      in its favour for sequential build workloads.

    - In the bench harness's persistent-fork microbench
      ({{:https://github.com/yurug/kaplan2/blob/main/bench/adversarial.sh}bench/adversarial.sh}),
      D4 shows the linear-in-cascade-depth growth that the WC-O(1)
      bound is designed to avoid, while KT, Viennot, and our C
      runtime stay flat at ~25-30 ns/op across six orders of
      magnitude of N.  At depth 18 (size ≈ 2.6M), KT pays 25 ns/op
      while D4 pays ~190 ns/op.

    The contrast is *the operational evidence* of the WC-O(1) story
    discussed in §1 of
    {{:https://github.com/yurug/kaplan2/blob/main/kb/spec/why-bounded-cascade.md}why-bounded-cascade.md}:
    amortised analyses don't survive forking; WC O(1) does.

    ## What it actually is

    A Section-4 non-catenable deque.  Mirrors the cell layout from
    the older Rocq Deque4 development (superseded by the packets-
    and-chains DequePtr formalisation; both live in the project
    monorepo):

    - each cell holds a prefix buffer, optional child, suffix buffer;
    - element type changes per level (level [l]: [α^(2^l)]).

    Overflow on a top buffer triggers a recursive *spill*: eject 2
    elements from the back of the buffer, pair them, push the pair
    onto the child level (creating a child if absent).  This yields
    O(log n) worst-case per operation and amortised O(1) — exactly
    the cost profile we want to contrast against.

    Persistence is automatic: every operation returns a new chain
    sharing structurally with the old one.  Cells are immutable
    records; the GC handles deallocation.

    Cross-references (all in the project monorepo at
    https://github.com/yurug/kaplan2 ):
    - bench/adversarial.sh             -- the bench that exposes D4's WC.
    - kb/spec/why-bounded-cascade.md §1 -- why amortised fails on
                                          persistent workloads.
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
    - kb/spec/section4-repair-cases.md  -- verbatim KT99 §4.2 trace.
    - manual §§5-7.
*)

type color3 = Green3 | Yellow3 | Red3

(* ------------------------------------------------------------------ *)
(* Buf5: 0..5 elements at one level                                     *)
(* ------------------------------------------------------------------ *)

type 'a buf5 =
  | B0
  | B1 of 'a
  | B2 of 'a * 'a
  | B3 of 'a * 'a * 'a
  | B4 of 'a * 'a * 'a * 'a
  | B5 of 'a * 'a * 'a * 'a * 'a

let buf5_size : type a. a buf5 -> int = function
  | B0 -> 0
  | B1 _ -> 1
  | B2 _ -> 2
  | B3 _ -> 3
  | B4 _ -> 4
  | B5 _ -> 5

let buf5_color : type a. a buf5 -> color3 = function
  | B0 | B5 _ -> Red3
  | B1 _ | B4 _ -> Yellow3
  | B2 _ | B3 _ -> Green3

(* ------------------------------------------------------------------ *)
(* Chain: nested per-level structure; polymorphic recursion            *)
(* ------------------------------------------------------------------ *)

type 'a chain =
  | One of 'a buf5
  | Two of 'a buf5 * ('a * 'a) chain * 'a buf5

type 'a t = 'a chain option

let empty : 'a t = None
let is_empty : 'a t -> bool = function None -> true | _ -> false

(* ------------------------------------------------------------------ *)
(* Buffer naive operations (Some/None on overflow/underflow)            *)
(* ------------------------------------------------------------------ *)

let buf5_push : type a. a -> a buf5 -> a buf5 option =
  fun x b -> match b with
  | B0 -> Some (B1 x)
  | B1 a -> Some (B2 (x, a))
  | B2 (a, b) -> Some (B3 (x, a, b))
  | B3 (a, b, c) -> Some (B4 (x, a, b, c))
  | B4 (a, b, c, d) -> Some (B5 (x, a, b, c, d))
  | B5 _ -> None

let buf5_pop : type a. a buf5 -> (a * a buf5) option = function
  | B0 -> None
  | B1 a -> Some (a, B0)
  | B2 (a, b) -> Some (a, B1 b)
  | B3 (a, b, c) -> Some (a, B2 (b, c))
  | B4 (a, b, c, d) -> Some (a, B3 (b, c, d))
  | B5 (a, b, c, d, e) -> Some (a, B4 (b, c, d, e))

let buf5_inject : type a. a buf5 -> a -> a buf5 option =
  fun b x -> match b with
  | B0 -> Some (B1 x)
  | B1 a -> Some (B2 (a, x))
  | B2 (a, b) -> Some (B3 (a, b, x))
  | B3 (a, b, c) -> Some (B4 (a, b, c, x))
  | B4 (a, b, c, d) -> Some (B5 (a, b, c, d, x))
  | B5 _ -> None

let buf5_eject : type a. a buf5 -> (a buf5 * a) option = function
  | B0 -> None
  | B1 a -> Some (B0, a)
  | B2 (a, b) -> Some (B1 a, b)
  | B3 (a, b, c) -> Some (B2 (a, b), c)
  | B4 (a, b, c, d) -> Some (B3 (a, b, c), d)
  | B5 (a, b, c, d, e) -> Some (B4 (a, b, c, d), e)

(* Take 2 elements from the back of a buf5; precondition: size >= 2 *)
let buf5_eject2 : type a. a buf5 -> (a buf5 * (a * a)) option = function
  | B0 | B1 _ -> None
  | B2 (a, b) -> Some (B0, (a, b))
  | B3 (a, b, c) -> Some (B1 a, (b, c))
  | B4 (a, b, c, d) -> Some (B2 (a, b), (c, d))
  | B5 (a, b, c, d, e) -> Some (B3 (a, b, c), (d, e))

(* Take 2 from the front of a buf5 *)
let buf5_pop2 : type a. a buf5 -> ((a * a) * a buf5) option = function
  | B0 | B1 _ -> None
  | B2 (a, b) -> Some ((a, b), B0)
  | B3 (a, b, c) -> Some ((a, b), B1 c)
  | B4 (a, b, c, d) -> Some ((a, b), B2 (c, d))
  | B5 (a, b, c, d, e) -> Some ((a, b), B3 (c, d, e))

(* Inject a pair into a buf5 *)
let buf5_inject_pair : type a. a buf5 -> (a * a) -> a buf5 option =
  fun b (x, y) -> match b with
  | B0 -> Some (B2 (x, y))
  | B1 a -> Some (B3 (a, x, y))
  | B2 (a, b) -> Some (B4 (a, b, x, y))
  | B3 (a, b, c) -> Some (B5 (a, b, c, x, y))
  | B4 _ | B5 _ -> None

(* Push a pair onto the front of a buf5 *)
let buf5_push_pair : type a. (a * a) -> a buf5 -> a buf5 option =
  fun (x, y) b -> match b with
  | B0 -> Some (B2 (x, y))
  | B1 a -> Some (B3 (x, y, a))
  | B2 (a, b) -> Some (B4 (x, y, a, b))
  | B3 (a, b, c) -> Some (B5 (x, y, a, b, c))
  | B4 _ | B5 _ -> None

(* ------------------------------------------------------------------ *)
(* push / pop on chain — with spill on overflow                         *)
(* ------------------------------------------------------------------ *)

(* When pushing onto a full prefix, spill 2 elements to the child.
   The child holds pairs of the parent's element type. *)
let rec push_chain : type a. a -> a chain -> a chain =
  fun x c ->
  match c with
  | One b ->
      (match buf5_push x b with
       | Some b' -> One b'
       | None ->
           (* b is B5; eject 2 to make a pair, push onto a new child,
              then push x onto the now-non-full b *)
           (match buf5_eject2 b with
            | Some (b', pair) ->
                (* b' is B3; pushing x gives B4 *)
                (match buf5_push x b' with
                 | Some b'' ->
                     let child = One (B1 pair) in
                     Two (b'', child, B0)
                 | None -> assert false)
            | None -> assert false))
  | Two (p, child, s) ->
      (match buf5_push x p with
       | Some p' -> Two (p', child, s)
       | None ->
           (* p is full; spill *)
           (match buf5_eject2 p with
            | Some (p', pair) ->
                (match buf5_push x p' with
                 | Some p'' ->
                     let child' = push_chain pair child in
                     Two (p'', child', s)
                 | None -> assert false)
            | None -> assert false))

(* When popping from an empty prefix, refill from the child or fall
   through to the suffix.  *)
let rec pop_chain : type a. a chain -> (a * a chain option) option =
  fun c ->
  match c with
  | One b ->
      (match buf5_pop b with
       | Some (x, b') ->
           if buf5_size b' = 0 then Some (x, None)
           else Some (x, Some (One b'))
       | None -> None)
  | Two (p, child, s) ->
      (match buf5_pop p with
       | Some (x, p') ->
           Some (x, Some (Two (p', child, s)))
       | None ->
           (* p is empty; refill from child by popping a pair, hand
              out the first element, leave the second in p. *)
           (match pop_chain child with
            | Some ((x, y), child_opt) ->
                let p'' = B1 y in
                (match child_opt with
                 | Some child' -> Some (x, Some (Two (p'', child', s)))
                 | None ->
                     (* child became empty; collapse to a One-cell,
                        merging p'' and s as best we can *)
                     if buf5_size s = 0 then Some (x, Some (One p''))
                     else
                       (* p'' has 1 elt, s has 1+; we can keep them
                          as a Two with empty child, but that's still
                          a Two cell — accept the asymmetry *)
                       Some (x, Some (Two (p'', One B0, s))))
            | None ->
                (* child is empty too; fall back to suf *)
                (match buf5_pop s with
                 | Some (x, s') ->
                     if buf5_size s' = 0 then Some (x, None)
                     else Some (x, Some (One s'))
                 | None -> None)))

(* inject is push's mirror at the suffix end *)
let rec inject_chain : type a. a chain -> a -> a chain =
  fun c x ->
  match c with
  | One b ->
      (match buf5_inject b x with
       | Some b' -> One b'
       | None ->
           (match buf5_pop2 b with
            | Some (pair, b') ->
                (* b' is B3; injecting x gives B4 *)
                (match buf5_inject b' x with
                 | Some b'' ->
                     let child = One (B1 pair) in
                     Two (B0, child, b'')
                 | None -> assert false)
            | None -> assert false))
  | Two (p, child, s) ->
      (match buf5_inject s x with
       | Some s' -> Two (p, child, s')
       | None ->
           (match buf5_pop2 s with
            | Some (pair, s') ->
                (match buf5_inject s' x with
                 | Some s'' ->
                     let child' = inject_chain child pair in
                     Two (p, child', s'')
                 | None -> assert false)
            | None -> assert false))

let rec eject_chain : type a. a chain -> (a chain option * a) option =
  fun c ->
  match c with
  | One b ->
      (match buf5_eject b with
       | Some (b', x) ->
           if buf5_size b' = 0 then Some (None, x)
           else Some (Some (One b'), x)
       | None -> None)
  | Two (p, child, s) ->
      (match buf5_eject s with
       | Some (s', x) -> Some (Some (Two (p, child, s')), x)
       | None ->
           (match eject_chain child with
            | Some (child_opt, (x, y)) ->
                let s'' = B1 x in
                let popped = y in
                (match child_opt with
                 | Some child' -> Some (Some (Two (p, child', s'')), popped)
                 | None ->
                     if buf5_size p = 0 then Some (Some (One s''), popped)
                     else Some (Some (Two (p, One B0, s'')), popped))
            | None ->
                (match buf5_eject p with
                 | Some (p', x) ->
                     if buf5_size p' = 0 then Some (None, x)
                     else Some (Some (One p'), x)
                 | None -> None)))

(* ------------------------------------------------------------------ *)
(* Public API                                                           *)
(* ------------------------------------------------------------------ *)

let push : 'a -> 'a t -> 'a t = fun x d ->
  match d with
  | None -> Some (One (B1 x))
  | Some c -> Some (push_chain x c)

let pop : 'a t -> ('a * 'a t) option = function
  | None -> None
  | Some c ->
      (match pop_chain c with
       | Some (x, d') -> Some (x, d')
       | None -> None)

let inject : 'a t -> 'a -> 'a t = fun d x ->
  match d with
  | None -> Some (One (B1 x))
  | Some c -> Some (inject_chain c x)

let eject : 'a t -> ('a t * 'a) option = function
  | None -> None
  | Some c ->
      (match eject_chain c with
       | Some (d', x) -> Some (d', x)
       | None -> None)

(* ------------------------------------------------------------------ *)
(* to_list and to_seq                                                   *)
(* ------------------------------------------------------------------ *)

let rec chain_to_list : type a. (a -> 'b list) -> a chain -> 'b list =
  fun flat c ->
  match c with
  | One b -> buf5_to_list flat b
  | Two (p, child, s) ->
      buf5_to_list flat p
      @ chain_to_list (fun (x, y) -> flat x @ flat y) child
      @ buf5_to_list flat s

and buf5_to_list : type a. (a -> 'b list) -> a buf5 -> 'b list =
  fun flat b -> match b with
  | B0 -> []
  | B1 a -> flat a
  | B2 (a, b) -> flat a @ flat b
  | B3 (a, b, c) -> flat a @ flat b @ flat c
  | B4 (a, b, c, d) -> flat a @ flat b @ flat c @ flat d
  | B5 (a, b, c, d, e) -> flat a @ flat b @ flat c @ flat d @ flat e

let to_list : 'a t -> 'a list = function
  | None -> []
  | Some c -> chain_to_list (fun x -> [x]) c

let to_seq (d : 'a t) : 'a Seq.t = to_list d |> List.to_seq
