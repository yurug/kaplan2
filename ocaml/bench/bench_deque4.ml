(** Benchmark Deque4 implementations: candidate, list-reference, Viennot.

    Replicates VWGP §9.1 methodology: 41 logarithmic size groups (G0..G40),
    50 trials per group.  Mix of push / pop / inject / eject (no concat for
    Deque4).  Reports time per operation in microseconds.

    Cross-references:
    - kb/architecture/decisions/adr-0009-deque4-end-to-end.md
    - VWGP §9.1
*)

module C = Ktdeque.Deque4
module R = Ktdeque.Deque4_ref
module V = Viennot_deque.Deque

(* ------------------------------------------------------------------ *)
(* Build deques of approximately n elements via repeated push.         *)
(* ------------------------------------------------------------------ *)

let build_candidate (n : int) : int C.t =
  let rec loop acc i =
    if i >= n then acc
    else loop (C.push i acc) (i + 1)
  in
  loop C.empty 0

let build_reference (n : int) : int R.t =
  let rec loop acc i =
    if i >= n then acc
    else loop (R.push i acc) (i + 1)
  in
  loop R.empty 0

let build_viennot (n : int) : int V.t =
  let rec loop acc i =
    if i >= n then acc
    else loop (V.push i acc) (i + 1)
  in
  loop V.empty 0

(* ------------------------------------------------------------------ *)
(* Time an operation [iters] times; returns microseconds per op.        *)
(* ------------------------------------------------------------------ *)

let time_op (iters : int) (f : unit -> unit) : float =
  let t0 = Unix.gettimeofday () in
  for _ = 1 to iters do f () done;
  let t1 = Unix.gettimeofday () in
  (t1 -. t0) /. float_of_int iters *. 1e6

(** Bench all three impls for one operation at one size. *)
let bench_op (label : string) (n : int) (iters : int)
             (op_c : int C.t -> int C.t)
             (op_r : int R.t -> int R.t)
             (op_v : int V.t -> int V.t) : unit =
  let dc = build_candidate n in
  let dr = build_reference n in
  let dv = build_viennot   n in

  let t_c = time_op iters (fun () -> ignore (op_c dc)) in
  let t_r = time_op iters (fun () -> ignore (op_r dr)) in
  let t_v = time_op iters (fun () -> ignore (op_v dv)) in

  Printf.printf "%s | n=2^%2d | cand=%8.3f | ref=%9.3f | viennot=%6.3f µs (cand/viennot=%5.2fx)\n"
    label
    (int_of_float (Float.log2 (float_of_int (max n 1))))
    t_c t_r t_v
    (if t_v > 0.0 then t_c /. t_v else 0.0)

(* ------------------------------------------------------------------ *)
(* Drivers                                                              *)
(* ------------------------------------------------------------------ *)

let bench_push n =
  bench_op "push  " n 1000
    (fun d -> C.push 99 d)
    (fun d -> R.push 99 d)
    (fun d -> V.push 99 d)

let bench_pop n =
  bench_op "pop   " n 1000
    (fun d -> match C.pop d with Some (_, d') -> d' | None -> d)
    (fun d -> match R.pop d with Some (_, d') -> d' | None -> d)
    (fun d -> match V.pop d with Some (_, d') -> d' | None -> d)

let bench_inject n =
  bench_op "inject" n 1000
    (fun d -> C.inject d 99)
    (fun d -> R.inject d 99)
    (fun d -> V.inject d 99)

let bench_eject n =
  bench_op "eject " n 1000
    (fun d -> match C.eject d with Some (d', _) -> d' | None -> d)
    (fun d -> match R.eject d with Some (d', _) -> d' | None -> d)
    (fun d -> match V.eject d with Some (d', _) -> d' | None -> d)

(* ------------------------------------------------------------------ *)
(* Main                                                                 *)
(* ------------------------------------------------------------------ *)

let () =
  Printf.printf "Deque4 benchmark — three impls compared\n";
  Printf.printf "  cand   : Ktdeque.Deque4 (our hand-written OCaml; v0 chain w/ spill)\n";
  Printf.printf "  ref    : Ktdeque.Deque4_ref (linked list, O(n) per back-op)\n";
  Printf.printf "  viennot: Viennot et al. Deque (vendored from external-refs)\n";
  Printf.printf "  Methodology: VWGP §9.1, 1000 iters per measurement.\n\n";
  let sizes = [1; 4; 16; 64; 256; 1024; 4096; 16384; 65536] in
  Printf.printf "=== push ===\n";   List.iter bench_push   sizes;
  Printf.printf "\n=== pop ===\n";  List.iter bench_pop    sizes;
  Printf.printf "\n=== inject ===\n"; List.iter bench_inject sizes;
  Printf.printf "\n=== eject ===\n";  List.iter bench_eject  sizes
