(** wcet.ml — worst-case per-operation cost probe for the §4 deque.

    For each implementation and operation we measure, over a battery of
    reachable states (built by several different op-histories plus a
    seeded pseudo-random walk), two quantities:

    - {b allocation words per op} — via [Gc.minor_words].  A deque op is
      a pure function, so at a fixed state it allocates exactly the same
      number of words on every call; this column is therefore an exact,
      reproducible measure of the op's worst-case {e work}, directly
      comparable to the proven constant primitive bound.  For the WC-O(1)
      implementations it is flat across state and size; for the amortized
      D4 it grows with the cascade depth.

    - {b wall-clock ns per op} — measured by re-running one op on one
      saved state many times (the persistent-fork trick from
      [adversarial.ml]; the op is pure so every call repeats the same
      work).  We take the {e min over trials} to suppress
      microarchitectural noise — the per-state cost we want is the clean
      one — then report the {e max over the state battery}.

    This is {b measurement-based} worst-case over an adversarial state
    battery, not a sound hardware WCET: out-of-order x86 plus the GC
    defeat cycle-exact static bounds.  What makes it meaningful here is
    that the algorithm is proven WC O(1) (the true worst case is bounded
    and reachable at small sizes), and the deterministic allocation
    column corroborates that the sampled worst really is the structural
    worst.  See BENCHMARKS.md. *)

(* ------------------------------------------------------------------ *)
(* Uniform interface over the three §4 implementations.  Elements are  *)
(* int; [pop]/[eject] return the remaining deque (we discard it).      *)
(* ------------------------------------------------------------------ *)

module type DEQUE = sig
  type t
  val name : string
  val empty : t
  val push   : int -> t -> t
  val inject : t -> int -> t
  val pop    : t -> t
  val eject  : t -> t
  val is_empty : t -> bool
end

module Kt : DEQUE = struct
  open KTDeque
  type t = int kChain
  let name = "KT (OCaml, verified)"
  let empty = empty_kchain
  let push x t = match push_kt2 (Coq_E.base x) t with
    | Some t' -> t' | None -> failwith "Kt.push: regularity violated"
  let inject t x = match inject_kt2 t (Coq_E.base x) with
    | Some t' -> t' | None -> failwith "Kt.inject: regularity violated"
  let pop t = match pop_kt2 t with Some (_, t') -> t' | None -> t
  let eject t = match eject_kt2 t with Some (t', _) -> t' | None -> t
  let is_empty t = match pop_kt2 t with None -> true | Some _ -> false
end

module Vi : DEQUE = struct
  module D = Viennot_deque.Deque.Base
  type t = int D.t
  let name = "Viennot (OCaml)"
  let empty = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = match D.pop t with Some (_, t') -> t' | None -> t
  let eject t = match D.eject t with Some (t', _) -> t' | None -> t
  let is_empty t = D.is_empty t
end

module D4 : DEQUE = struct
  module D = Ktdeque_bench_helpers.Deque4
  type t = int D.t
  let name = "D4 (amortized O(log n))"
  let empty = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = match D.pop t with Some (_, t') -> t' | None -> t
  let eject t = match D.eject t with Some (t', _) -> t' | None -> t
  let is_empty t = match D.pop t with None -> true | Some _ -> false
end

(* ------------------------------------------------------------------ *)
(* Measurement + state battery, generic over a DEQUE.                  *)
(* ------------------------------------------------------------------ *)

let now () = Unix.gettimeofday ()

module Measure (D : DEQUE) = struct
  (* Deterministic: words allocated per op at a fixed state. *)
  let alloc_per_op (f : D.t -> D.t) (s : D.t) ~k =
    let a0 = Gc.minor_words () in
    for _ = 1 to k do ignore (Sys.opaque_identity (f s)) done;
    let a1 = Gc.minor_words () in
    (a1 -. a0) /. float_of_int k

  (* Min over trials of the mean-at-state cost (ns). *)
  let ns_per_op (f : D.t -> D.t) (s : D.t) ~m ~trials =
    let best = ref infinity in
    for _ = 1 to trials do
      let t0 = now () in
      for _ = 1 to m do ignore (Sys.opaque_identity (f s)) done;
      let dt = ((now () -. t0) *. 1e9) /. float_of_int m in
      if dt < !best then best := dt
    done;
    !best

  (* Builders return (state, logical size). *)
  let build_push n =
    let t = ref D.empty in
    for i = 1 to n do t := D.push i !t done; (!t, n)
  let build_inject n =
    let t = ref D.empty in
    for i = 1 to n do t := D.inject !t i done; (!t, n)
  let build_alt n =
    let t = ref D.empty in
    for i = 1 to n do
      if i land 1 = 0 then t := D.push i !t else t := D.inject !t i
    done; (!t, n)
  let build_churn n =
    (* grow past n, then pop back to n — a post-cascade state *)
    let t = ref D.empty in
    for i = 1 to n + (n / 2) do t := D.push i !t done;
    for _ = 1 to n / 2 do if not (D.is_empty !t) then t := D.pop !t done;
    (!t, n)
  let build_random ~seed n =
    Random.init seed;
    let t = ref D.empty and size = ref 0 in
    for i = 1 to n do t := D.push i !t; incr size done;
    for i = 1 to 2 * n do
      (match Random.int 4 with
       | 0 -> t := D.push i !t; incr size
       | 1 -> t := D.inject !t i; incr size
       | 2 -> if !size > 0 then (t := D.pop !t; decr size)
       | _ -> if !size > 0 then (t := D.eject !t; decr size))
    done;
    (!t, !size)

  let sizes = [ 7; 15; 31; 63; 127; 255; 511; 1023; 4095; 16383; 131071 ]

  let battery () =
    let deterministic =
      List.concat_map (fun n ->
        [ Printf.sprintf "push^%d" n,   build_push n;
          Printf.sprintf "inject^%d" n, build_inject n;
          Printf.sprintf "alt^%d" n,    build_alt n;
          Printf.sprintf "churn~%d" n,  build_churn n ])
        sizes
    in
    let random =
      List.concat_map (fun n ->
        List.map (fun seed ->
          Printf.sprintf "rand%d~%d" seed n, build_random ~seed n)
          [ 1; 2; 3 ])
        [ 127; 4095; 131071 ]
    in
    deterministic @ random
end

(* ------------------------------------------------------------------ *)
(* Small stats helpers.                                                *)
(* ------------------------------------------------------------------ *)

let median xs =
  match List.sort compare xs with
  | [] -> 0.0
  | sorted ->
    let a = Array.of_list sorted in
    let n = Array.length a in
    if n land 1 = 1 then a.(n / 2)
    else (a.((n / 2) - 1) +. a.(n / 2)) /. 2.0

let max_by key = function
  | [] -> None
  | x :: xs ->
    Some (List.fold_left (fun acc y -> if key y > key acc then y else acc) x xs)

(* ------------------------------------------------------------------ *)
(* Driver: one block of rows per implementation.                       *)
(* ------------------------------------------------------------------ *)

let run_impl name (module D : DEQUE) ~m ~trials ~k =
  let module Me = Measure (D) in
  let bat = Me.battery () in
  let ops = [
    "push",   (fun s -> D.push 0 s),   false;
    "inject", (fun s -> D.inject s 0), false;
    "pop",    D.pop,                   true;
    "eject",  D.eject,                 true;
  ] in
  List.iter (fun (opname, f, need_nonempty) ->
    Gc.full_major ();
    let rows =
      List.filter_map (fun (label, (s, sz)) ->
        if need_nonempty && D.is_empty s then None
        else
          let a = Me.alloc_per_op f s ~k in
          let t = Me.ns_per_op f s ~m ~trials in
          Some (label, sz, a, t))
        bat
    in
    let worst_a = max_by (fun (_, _, a, _) -> a) rows in
    let worst_t = max_by (fun (_, _, _, t) -> t) rows in
    let med_t = median (List.map (fun (_, _, _, t) -> t) rows) in
    match worst_a, worst_t with
    | Some (_, _, a, _), Some (lt, szt, _, t) ->
      Printf.printf "| %s | `%s` | %.1f | %.1f | %.1f | %s @ n=%d |\n%!"
        name opname a t med_t lt szt
    | _ -> ())
    ops

let () =
  let m = ref 50_000 and trials = ref 3 and k = ref 10_000 in
  Arg.parse [
    "--m", Arg.Int (fun x -> m := x), "timing reps per state (default 50000)";
    "--trials", Arg.Int (fun x -> trials := x), "timing trials per state (default 3)";
    "--k", Arg.Int (fun x -> k := x), "alloc reps per state (default 10000)";
  ] (fun _ -> ()) "wcet: worst-case per-op cost probe (§4 deque)";
  print_string "| impl | op | max alloc (words/op) | worst-case ns/op | median ns/op | worst-case state |\n";
  print_string "|---|---|---:|---:|---:|---|\n";
  (* Warm runtime once. *)
  let module W = Measure (Kt) in ignore (W.build_push 1000);
  run_impl Kt.name   (module Kt) ~m:!m ~trials:!trials ~k:!k;
  run_impl Vi.name   (module Vi) ~m:!m ~trials:!trials ~k:!k;
  run_impl D4.name   (module D4) ~m:!m ~trials:!trials ~k:!k
