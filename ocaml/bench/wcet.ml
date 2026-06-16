(** wcet.ml — worst-case per-operation cost probe (§4 deque + §6 cadeque).

    For each implementation and operation we measure, over a battery of
    reachable states (built by several different op-histories plus a
    seeded pseudo-random walk; for [concat], a battery of operand pairs),
    two quantities:

    - {b allocation words per op} — via [Gc.minor_words].  A deque/cadeque
      op is a pure function, so at a fixed state it allocates exactly the
      same number of words on every call; this column is therefore an
      exact, reproducible measure of the op's worst-case {e work},
      comparable to the proven constant bound.  For the WC-O(1)
      implementations it is flat across state and size; for the amortized
      D4 (§4 only) it grows with the cascade depth.

    - {b wall-clock ns per op} — by re-running one op on one saved state
      many times (the persistent-fork trick from [adversarial.ml]; the op
      is pure so every call repeats the same work).  We take the {e min
      over trials} to suppress microarchitectural noise, then report the
      {e max over the state battery}.

    Measurement-based worst-case over an adversarial state battery, not a
    sound hardware WCET (out-of-order x86 + GC defeat cycle-exact static
    bounds).  What makes it meaningful: the algorithm is proven WC O(1)
    (the true worst case is bounded and reachable at small sizes), and
    the deterministic allocation column corroborates that the sampled
    worst is the structural worst.  See BENCHMARKS.md. *)

(* ------------------------------------------------------------------ *)
(* Generic measurement (independent of the data structure).            *)
(* ------------------------------------------------------------------ *)

let now () = Unix.gettimeofday ()

(* Deterministic: words allocated per op at a fixed state. *)
let alloc_per_op (f : 'a -> 'a) (s : 'a) ~k =
  let a0 = Gc.minor_words () in
  for _ = 1 to k do ignore (Sys.opaque_identity (f s)) done;
  let a1 = Gc.minor_words () in
  (a1 -. a0) /. float_of_int k

(* Min over trials of the mean-at-state cost (ns). *)
let ns_per_op (f : 'a -> 'a) (s : 'a) ~m ~trials =
  let best = ref infinity in
  for _ = 1 to trials do
    let t0 = now () in
    for _ = 1 to m do ignore (Sys.opaque_identity (f s)) done;
    let dt = ((now () -. t0) *. 1e9) /. float_of_int m in
    if dt < !best then best := dt
  done;
  !best

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

(* ================================================================== *)
(* §4 non-catenable deque.                                             *)
(* ================================================================== *)

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
  let name = "KT (verified)"
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
  let name = "Viennot"
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

let sizes = [ 7; 15; 31; 63; 127; 255; 511; 1023; 4095; 16383; 131071 ]

module Build4 (D : DEQUE) = struct
  let push n =
    let t = ref D.empty in for i = 1 to n do t := D.push i !t done; (!t, n)
  let inject n =
    let t = ref D.empty in for i = 1 to n do t := D.inject !t i done; (!t, n)
  let alt n =
    let t = ref D.empty in
    for i = 1 to n do
      if i land 1 = 0 then t := D.push i !t else t := D.inject !t i
    done; (!t, n)
  let churn n =
    let t = ref D.empty in
    for i = 1 to n + (n / 2) do t := D.push i !t done;
    for _ = 1 to n / 2 do if not (D.is_empty !t) then t := D.pop !t done;
    (!t, n)
  let random ~seed n =
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
  let battery () =
    let det =
      List.concat_map (fun n ->
        [ Printf.sprintf "push^%d" n, push n;
          Printf.sprintf "inject^%d" n, inject n;
          Printf.sprintf "alt^%d" n, alt n;
          Printf.sprintf "churn~%d" n, churn n ]) sizes
    in
    let rnd =
      List.concat_map (fun n ->
        List.map (fun seed -> Printf.sprintf "rand%d~%d" seed n, random ~seed n)
          [ 1; 2; 3 ]) [ 127; 4095; 131071 ]
    in
    det @ rnd
end

let run4 (module D : DEQUE) ~m ~trials ~k =
  let module B = Build4 (D) in
  let bat = B.battery () in
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
        else Some (label, sz, alloc_per_op f s ~k, ns_per_op f s ~m ~trials))
        bat
    in
    match max_by (fun (_,_,a,_) -> a) rows, max_by (fun (_,_,_,t) -> t) rows with
    | Some (_,_,a,_), Some (lt, szt, _, t) ->
      Printf.printf "| %s | `%s` | %.1f | %.1f | %.1f | %s @ n=%d |\n%!"
        D.name opname a t (median (List.map (fun (_,_,_,t) -> t) rows)) lt szt
    | _ -> ())
    ops

(* ================================================================== *)
(* §6 catenable deque (adds concat, measured over operand pairs).      *)
(* ================================================================== *)

module type CADEQUE = sig
  type t
  val name : string
  val empty : t
  val push   : int -> t -> t
  val inject : t -> int -> t
  val pop    : t -> t
  val eject  : t -> t
  val concat : t -> t -> t
  val is_empty : t -> bool
end

module KTf : CADEQUE = struct
  module K = KTFlatCadeque
  type t = int K.fchain
  let name = "KTf (verified §6)"
  let empty = K.fcad_empty
  let push x t = K.cad_push_x x t
  let inject t x = K.cad_inject_x t x
  let pop t = match K.cad_pop_x t with Some (_, t') -> t' | None -> t
  let eject t = match K.cad_eject_x t with Some (t', _) -> t' | None -> t
  let concat a b = match K.cad_concat_x a b with Some c -> c | None -> failwith "concat None"
  let is_empty t = match K.cad_pop_x t with None -> true | Some _ -> false
end

module ViCad : CADEQUE = struct
  module C = Viennot_deque.Cadeque
  type t = int C.t
  let name = "Viennot §6"
  let empty = C.empty
  let push x t = C.push x t
  let inject t x = C.inject t x
  let pop t = match C.pop t with Some (_, t') -> t' | None -> t
  let eject t = match C.eject t with Some (t', _) -> t' | None -> t
  let concat a b = C.append a b
  let is_empty t = match C.pop t with None -> true | Some _ -> false
end

module Build6 (C : CADEQUE) = struct
  let push n = let t = ref C.empty in for i = 1 to n do t := C.push i !t done; (!t, n)
  let inject n = let t = ref C.empty in for i = 1 to n do t := C.inject !t i done; (!t, n)
  let churn n =
    let t = ref C.empty in
    for i = 1 to n + (n / 2) do t := C.push i !t done;
    for _ = 1 to n / 2 do if not (C.is_empty !t) then t := C.pop !t done;
    (!t, n)
  let random ~seed n =
    Random.init seed;
    let t = ref C.empty and size = ref 0 in
    for i = 1 to n do t := C.push i !t; incr size done;
    for i = 1 to 2 * n do
      (match Random.int 4 with
       | 0 -> t := C.push i !t; incr size
       | 1 -> t := C.inject !t i; incr size
       | 2 -> if !size > 0 then (t := C.pop !t; decr size)
       | _ -> if !size > 0 then (t := C.eject !t; decr size))
    done;
    (!t, !size)
  (* single-state battery for push/inject/pop/eject *)
  let battery () =
    let det =
      List.concat_map (fun n ->
        [ Printf.sprintf "push^%d" n, push n;
          Printf.sprintf "inject^%d" n, inject n;
          Printf.sprintf "churn~%d" n, churn n ]) sizes
    in
    let rnd =
      List.concat_map (fun n ->
        List.map (fun seed -> Printf.sprintf "rand%d~%d" seed n, random ~seed n)
          [ 1; 2 ]) [ 127; 4095; 131071 ]
    in
    det @ rnd
  (* Operands for the concat pair battery.  Crucially includes the SMALL
     sizes 1..7: §6 concat absorbs a small operand element-by-element
     (bounded by a threshold), so the worst case lives just below that
     threshold, NOT at large sizes (large++large is the cheap O(1)
     spine-join).  Probing only large operands misses the real worst. *)
  let operands () =
    List.map (fun n -> Printf.sprintf "p%d" n, push n)
      [ 1; 2; 3; 4; 5; 6; 7; 4095 ]
    @ [ "rand4095", random ~seed:1 4095 ]
end

let run6 (module C : CADEQUE) ~m ~trials ~k =
  let module B = Build6 (C) in
  let bat = B.battery () in
  let ops = [
    "push",   (fun s -> C.push 0 s),   false;
    "inject", (fun s -> C.inject s 0), false;
    "pop",    C.pop,                   true;
    "eject",  C.eject,                 true;
  ] in
  List.iter (fun (opname, f, need_nonempty) ->
    Gc.full_major ();
    let rows =
      List.filter_map (fun (label, (s, sz)) ->
        if need_nonempty && C.is_empty s then None
        else Some (label, sz, alloc_per_op f s ~k, ns_per_op f s ~m ~trials))
        bat
    in
    match max_by (fun (_,_,a,_) -> a) rows, max_by (fun (_,_,_,t) -> t) rows with
    | Some (_,_,a,_), Some (lt, szt, _, t) ->
      Printf.printf "| %s | `%s` | %.1f | %.1f | %.1f | %s @ n=%d |\n%!"
        C.name opname a t (median (List.map (fun (_,_,_,t) -> t) rows)) lt szt
    | _ -> ())
    ops;
  (* concat over the operand-pair battery *)
  Gc.full_major ();
  let ops_l = B.operands () in
  let pairs =
    List.concat_map (fun (la, (a, _)) ->
      List.map (fun (lb, (b, _)) -> (la, lb, a, b)) ops_l) ops_l
  in
  let rows =
    List.map (fun (la, lb, a, b) ->
      let f = (fun _ -> C.concat a b) in
      (Printf.sprintf "%s++%s" la lb,
       alloc_per_op f a ~k, ns_per_op f a ~m ~trials)) pairs
  in
  (match max_by (fun (_,a,_) -> a) rows, max_by (fun (_,_,t) -> t) rows with
   | Some (_,a,_), Some (lt,_,t) ->
     Printf.printf "| %s | `concat` | %.1f | %.1f | %.1f | %s |\n%!"
       C.name a t (median (List.map (fun (_,_,t) -> t) rows)) lt
   | _ -> ())

(* ------------------------------------------------------------------ *)

let () =
  let m = ref 50_000 and trials = ref 5 and k = ref 10_000 in
  Arg.parse [
    "--m", Arg.Int (fun x -> m := x), "timing reps per state (default 50000)";
    "--trials", Arg.Int (fun x -> trials := x), "timing trials per state (default 5)";
    "--k", Arg.Int (fun x -> k := x), "alloc reps per state (default 10000)";
  ] (fun _ -> ()) "wcet: worst-case per-op cost probe (§4 + §6)";
  let header () =
    print_string "| impl | op | max alloc (words/op) | worst-case ns/op | median ns/op | worst-case state |\n";
    print_string "|---|---|---:|---:|---:|---|\n"
  in
  let module W = Build4 (Kt) in ignore (W.push 1000); (* warm *)
  print_string "### §4 non-catenable deque\n\n";
  header ();
  run4 (module Kt) ~m:!m ~trials:!trials ~k:!k;
  run4 (module Vi) ~m:!m ~trials:!trials ~k:!k;
  run4 (module D4) ~m:!m ~trials:!trials ~k:!k;
  print_string "\n### §6 catenable deque\n\n";
  header ();
  run6 (module KTf) ~m:!m ~trials:!trials ~k:!k;
  run6 (module ViCad) ~m:!m ~trials:!trials ~k:!k
