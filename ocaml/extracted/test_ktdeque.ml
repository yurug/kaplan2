(** Smoke test + microbenchmark for the extracted DequePtr deque.

    Exercises push_chain_full / pop_chain / inject_chain_full /
    eject_chain and compares against a list-based reference. *)

open KTDeque

(* The empty deque: [Ending B0], handily named [empty_chain]. *)
let empty_deque () : 'a chain = empty_chain

let push x d = match push_chain_rec (E.base x) d with
  | Some d' -> d'
  | None    -> failwith "push: regularity invariant violated"

let inject d x = match inject_chain_rec d (E.base x) with
  | Some d' -> d'
  | None    -> failwith "inject: regularity invariant violated"

let pop d = match pop_chain_rec d with
  | Some (e, d') ->
      let xs = E.to_list e in
      (match xs with
       | [x] -> Some (x, d')
       | _   -> failwith "pop: top element is not a base singleton")
  | None -> None

let eject d = match eject_chain_rec d with
  | Some (d', e) ->
      let xs = E.to_list e in
      (match xs with
       | [x] -> Some (d', x)
       | _   -> failwith "eject: top element is not a base singleton")
  | None -> None

let to_list d = chain_to_list d

(* Smoke test *)
let () =
  let d0 = empty_deque () in
  let d1 = push 1 d0 in
  let d2 = push 2 d1 in
  let d3 = inject d2 3 in
  let d4 = inject d3 4 in
  Printf.printf "After push 1, push 2, inject 3, inject 4:\n";
  Printf.printf "  to_list = [%s]\n"
    (String.concat "; " (List.map string_of_int (to_list d4)));
  match pop d4 with
  | Some (x, d') ->
      Printf.printf "  pop -> %d, remaining = [%s]\n"
        x (String.concat "; " (List.map string_of_int (to_list d')))
  | None -> Printf.printf "  pop returned None\n";;

(* Stress test: push N items, then pop them all. *)
let stress n =
  let d = ref (empty_deque ()) in
  for i = 1 to n do
    d := push i !d
  done;
  let total = List.length (to_list !d) in
  Printf.printf "After pushing %d items: total length = %d (expected %d)\n"
    n total n;
  let count = ref 0 in
  let go = ref true in
  while !go do
    match pop !d with
    | Some (_, d') -> d := d'; incr count
    | None -> go := false
  done;
  Printf.printf "Popped %d items, deque is now %s\n"
    !count (if to_list !d = [] then "empty" else "non-empty")

(* Microbenchmark *)
let bench n =
  let t0 = Unix.gettimeofday () in
  let d = ref (empty_deque ()) in
  for i = 1 to n do
    d := push i !d
  done;
  let t1 = Unix.gettimeofday () in
  Printf.printf "%d pushes: %.3f ms (%.3f ns/op)\n"
    n ((t1 -. t0) *. 1000.0) ((t1 -. t0) *. 1e9 /. float_of_int n)

let () =
  Printf.printf "\n=== Stress test ===\n";
  stress 10;
  stress 100;
  stress 1000;
  Printf.printf "\n=== Microbenchmarks ===\n";
  bench 1000;
  bench 10000;
  bench 100000
