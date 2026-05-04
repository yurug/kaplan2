(** hello.ml — minimal example of using the ktdeque OCaml library.
 *
 * Build (after `opam install .` from the repo root):
 *
 *     ocamlfind ocamlopt -package ktdeque -linkpkg hello.ml -o hello
 *
 * Or in the same opam switch via dune (see this directory's dune file).
 *
 * Then: ./hello
 *)

open KTDeque

let push_or_fail x d = match push_kt2 (Coq_E.base x) d with
  | Some d' -> d'
  | None -> failwith "push_kt2: regularity violated"

let inject_or_fail d x = match inject_kt2 d (Coq_E.base x) with
  | Some d' -> d'
  | None -> failwith "inject_kt2: regularity violated"

let pop_or_none d = match pop_kt2 d with
  | None -> None
  | Some (e, d') -> (match Coq_E.to_list e with [x] -> Some (x, d') | _ -> assert false)

let eject_or_none d = match eject_kt2 d with
  | None -> None
  | Some (d', e) -> (match Coq_E.to_list e with [x] -> Some (d', x) | _ -> assert false)

let to_list d = kchain_to_list d

let print_deque label d =
  Printf.printf "%s = [%s]\n" label
    (String.concat "; " (List.map string_of_int (to_list d)))

let () =
  (* Build [10; 20] by push 10 then inject 20. *)
  let d = empty_kchain in
  let d = push_or_fail   10 d in
  let d = inject_or_fail d 20 in
  let d = push_or_fail   30 d in
  print_deque "d" d;

  (* Persistence: branching d gives independent derivatives. *)
  let branch = inject_or_fail d 40 in
  print_deque "branch" branch;
  print_deque "d (still)" d;

  (* Drain d via pop+eject. *)
  let d = match pop_or_none   d with Some (x, d') -> Printf.printf "pop:   %d\n" x; d' | None -> d in
  let d = match eject_or_none d with Some (d', x) -> Printf.printf "eject: %d\n" x; d' | None -> d in
  let d = match pop_or_none   d with Some (x, d') -> Printf.printf "pop:   %d\n" x; d' | None -> d in
  let _ = match pop_or_none   d with None -> Printf.printf "empty? true\n" | Some _ -> Printf.printf "empty? false\n" in
  ()
