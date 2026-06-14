(** hello.ml — minimal example of the ktdeque OCaml library.

    Shows the idiomatic public interface: [Ktdeque.Deque] (the §4
    real-time deque) and [Ktdeque.Cadeque] (adds O(1) concatenation).
    Every operation is purely functional and worst-case O(1); values are
    persistent, so a deque can be "forked" and both branches used.

    Build (after `opam install .` from the repo root):

        ocamlfind ocamlopt -package ktdeque -linkpkg hello.ml -o hello

    Or in-tree: `dune exec ocaml/examples/hello.exe`. *)

open Ktdeque

let show label xs =
  Printf.printf "%s = [%s]\n" label
    (String.concat "; " (List.map string_of_int xs))

let () =
  (* ---- Deque: push at front, inject at back, pop/eject the ends ---- *)
  let d = Deque.of_list [10; 20] in     (* front = 10, back = 20 *)
  let d = Deque.push 30 d in            (* [30; 10; 20] *)
  show "d" (Deque.to_list d);

  (* Persistence: a derived deque leaves the original intact. *)
  let branch = Deque.inject d 40 in     (* [30; 10; 20; 40] *)
  show "branch" (Deque.to_list branch);
  show "d (still)" (Deque.to_list d);

  (match Deque.pop d with
   | Some (x, _) -> Printf.printf "front of d: %d\n" x
   | None -> ());
  (match Deque.eject d with
   | Some (_, x) -> Printf.printf "back of d:  %d\n" x
   | None -> ());

  (* ---- Cadeque: the same, plus worst-case O(1) concat ---- *)
  let a = Cadeque.of_list [1; 2; 3] in
  let b = Cadeque.of_list [4; 5; 6] in
  let c = Cadeque.concat a b in         (* O(1), regardless of size *)
  show "concat a b" (Cadeque.to_list c)
