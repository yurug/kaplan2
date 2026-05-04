(** Monolith model-based fuzzing for the **verified** [kt_deque_ptr]
    library.

    Compares the published library
    ([KTDeque.push_kt2 / pop_kt2 / inject_kt2 / eject_kt2]) against
    the list reference [Kaplan2_bench_helpers.Deque4_ref], generating
    millions of random scenarios.  Per VWGP §9.1's harness pattern,
    parallel to fuzz_deque4 (which targets the bench-helper).

    This addresses the gap noted in ocaml/README.md: the previous
    Monolith run only covered the bench-helper.  Now the verified
    library is also fuzzed under the same harness.

    Cross-references:
    - kb/external/monolith-fuzzing.md
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
*)

(* ------------------------------------------------------------------ *)
(* Adapter: wrap kt2 entry points to look like a simple ['a t]        *)
(* interface, hiding the Coq_E.t element wrapper.  Matches the shape  *)
(* expected by Monolith and the [R] reference below.                   *)
(* ------------------------------------------------------------------ *)

module C = struct
  open KTDeque

  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let is_empty (d : 'a t) : bool =
    match pop_kt2 d with None -> true | Some _ -> false

  let push (x : 'a) (d : 'a t) : 'a t =
    match push_kt2 (Coq_E.base x) d with
    | Some d' -> d'
    | None -> failwith "push_kt2: regularity violated"

  let inject (d : 'a t) (x : 'a) : 'a t =
    match inject_kt2 d (Coq_E.base x) with
    | Some d' -> d'
    | None -> failwith "inject_kt2: regularity violated"

  let pop (d : 'a t) : ('a * 'a t) option =
    match pop_kt2 d with
    | None -> None
    | Some (e, d') ->
        (match Coq_E.to_list e with
         | [x] -> Some (x, d')
         | _ -> failwith "pop_kt2: top element is not a base singleton")

  let eject (d : 'a t) : ('a t * 'a) option =
    match eject_kt2 d with
    | None -> None
    | Some (d', e) ->
        (match Coq_E.to_list e with
         | [x] -> Some (d', x)
         | _ -> failwith "eject_kt2: top element is not a base singleton")
end

module R = Kaplan2_bench_helpers.Deque4_ref

open Monolith

let elt = closed_interval 0 100

let deque = declare_abstract_type ()

let () =
  declare "empty"    deque                                R.empty    C.empty;
  declare "is_empty" (deque ^> bool)                      R.is_empty C.is_empty;
  declare "push"     (elt ^> deque ^> deque)              R.push     C.push;
  declare "pop"      (deque ^!> option (elt *** deque))   R.pop      C.pop;
  declare "inject"   (deque ^> elt ^> deque)              R.inject   C.inject;
  declare "eject"    (deque ^!> option (deque *** elt))   R.eject    C.eject;
  main 42
