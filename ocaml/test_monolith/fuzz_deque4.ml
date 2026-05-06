(** Monolith model-based fuzzing for Deque4.

    Compares the candidate hand-written [Ktdeque_bench_helpers.Deque4] against the list
    reference [Ktdeque_bench_helpers.Deque4_ref], generating millions of random scenarios.
    Per VWGP §9.1's harness pattern.

    Cross-references:
    - kb/external/monolith-fuzzing.md
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
*)

module C = Ktdeque_bench_helpers.Deque4
module R = Ktdeque_bench_helpers.Deque4_ref

open Monolith

(* Element type: small ints for readable counterexamples. *)
let elt = closed_interval 0 100

(* The deque type, declared as an abstract type.  Equivalence is checked
   operationally: two deques are equivalent iff they were produced by the
   same sequence of operations from [empty]. *)
let deque = declare_abstract_type ()

let () =
  declare "empty"    deque                                R.empty    C.empty;
  declare "is_empty" (deque ^> bool)                      R.is_empty C.is_empty;
  declare "push"     (elt ^> deque ^> deque)              R.push     C.push;
  declare "pop"      (deque ^!> option (elt *** deque))   R.pop      C.pop;
  declare "inject"   (deque ^> elt ^> deque)              R.inject   C.inject;
  declare "eject"    (deque ^!> option (deque *** elt))   R.eject    C.eject;
  main 42
