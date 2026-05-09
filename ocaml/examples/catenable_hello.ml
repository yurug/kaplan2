(** catenable_hello.ml -- minimal demo of [KTCatenableDeque].
 *
 * Walks through the five core operations (push / inject / pop /
 * eject / concat) on the catenable deque (KT99 §6).  This is the
 * companion to [hello.ml] (which exercises the Section-4 [KTDeque]).
 *
 * For the algorithmic intuition (why catenation can be O(1) WC),
 * read [kb/spec/why-catenable.md] in the project monorepo.
 *
 * For the public OCaml surface, see the [KTCatenableDeque] module
 * docstring (file kTCatenableDeque.mli in the ktdeque opam package).
 *
 * Build via dune:
 *
 *     dune exec ocaml/examples/catenable_hello.exe
 *
 * Then watch the output.
 *)

open KTCatenableDeque

let print_deque label q =
  Printf.printf "%s = [%s]\n" label
    (String.concat "; " (List.map string_of_int (cad_to_list_base q)))

let () =
  (* Build [1; 2; 3] and [4; 5; 6] independently. *)
  let q1 =
    cad_inject (cad_inject (cad_inject cad_empty 1) 2) 3
  in
  let q2 =
    cad_inject (cad_inject (cad_inject cad_empty 4) 5) 6
  in
  print_deque "q1" q1;
  print_deque "q2" q2;

  (* Concatenate via the fully-regularity-preserving variant. *)
  let q = cad_concat_op_full q1 q2 in
  print_deque "concat q1 q2" q;

  (* Persistence: the inputs are unchanged after concat. *)
  print_deque "q1 (still)" q1;
  print_deque "q2 (still)" q2;

  (* Pop and eject from the joined deque via the _full variants. *)
  let q =
    match cad_pop_op_full q with
    | Some (x, q') ->
      Printf.printf "pop:   %d\n" x;
      q'
    | None -> q
  in
  let q =
    match cad_eject_op_full q with
    | Some (q', x) ->
      Printf.printf "eject: %d\n" x;
      q'
    | None -> q
  in
  print_deque "q after pop/eject" q;

  (* Concatenation associativity at the sequence level. *)
  let a = cad_inject cad_empty 1 in
  let b = cad_inject cad_empty 2 in
  let c = cad_inject cad_empty 3 in
  let lab_l = cad_concat_op_full (cad_concat_op_full a b) c in
  let lab_r = cad_concat_op_full a (cad_concat_op_full b c) in
  print_deque "(a ++ b) ++ c" lab_l;
  print_deque "a ++ (b ++ c)" lab_r;
  ()
