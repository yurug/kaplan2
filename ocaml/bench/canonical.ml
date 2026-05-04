(** canonical.ml — head-to-head benchmark of the verified ktdeque against
    other canonical persistent-deque implementations available in this repo.

    Comparison set:
      - [KTDeque]               — our verified extraction, push_kt2 / pop_kt2 /
                                  inject_kt2 / eject_kt2 (bounded-cascade WC O(1)).
      - [Viennot]               — VWGP PLDI'24 hand-written real-time deque
                                  (vendored at ocaml/bench/viennot/).  The
                                  closest external reference: also worst-case
                                  O(1) per op, also purely functional.
      - [Deque4_handwritten]    — our own hand-written cell-based deque
                                  (amortized O(log n) per op, NOT real-time).
                                  Approximates an "Okasaki banker's-style"
                                  point in the design space.
      - [Deque4_ref]            — list-based reference; O(1) push/pop on the
                                  front, O(n) inject/eject.  Baseline / sanity
                                  oracle.

    Workloads (per Viennot §9, with adversarial variants):
      - steady_push            : just push N; final size = N.
      - steady_inject          : just inject N.
      - drain                  : pre-fill N then pop N; ends empty.
      - alt_push_pop           : push, pop, push, pop, ... at constant size 0–1.
                                  This is the classic adversarial workload that
                                  exposes amortized-vs-WC differences, since the
                                  amortized scheme's cleanup is forced every op.
      - mixed_pipopo           : push, inject, pop, pop in cycles.
      - fork_stress            : at each iter, snapshot and push 16 onto the
                                  copy.  Tests persistence/sharing cost.

    All four implementations run on the same workload bodies via a small
    functor (S below) so the only thing changing is the deque module.

    Output: a Markdown table per workload at sizes 1k / 100k / 1M, with
    ns/op for each implementation and a ratio against Viennot.  Send to
    stdout; stdout is captured by bench/canonical.sh.
*)

(* ------------------------------------------------------------------ *)
(* The interface we benchmark all impls against.                       *)
(* ------------------------------------------------------------------ *)

module type DEQUE = sig
  type 'a t
  val empty   : 'a t
  val push    : 'a -> 'a t -> 'a t
  val pop     : 'a t -> ('a * 'a t) option
  val inject  : 'a t -> 'a -> 'a t
  val eject   : 'a t -> ('a t * 'a) option
end

(* ------------------------------------------------------------------ *)
(* The four implementations, adapted to DEQUE.                         *)
(* ------------------------------------------------------------------ *)

module Kt : DEQUE = struct
  open KTDeque
  type 'a t = 'a kChain
  let empty = empty_kchain
  let push x d = match push_kt2 (Coq_E.base x) d with
    | Some d' -> d' | None -> failwith "Kt.push: regularity violated"
  let inject d x = match inject_kt2 d (Coq_E.base x) with
    | Some d' -> d' | None -> failwith "Kt.inject: regularity violated"
  let pop d = match pop_kt2 d with
    | None -> None
    | Some (e, d') -> (match Coq_E.to_list e with [x] -> Some (x, d') | _ -> assert false)
  let eject d = match eject_kt2 d with
    | None -> None
    | Some (d', e) -> (match Coq_E.to_list e with [x] -> Some (d', x) | _ -> assert false)
end

module Vi : DEQUE = struct
  module D = Viennot_deque.Deque.Base
  type 'a t = 'a D.t
  let empty = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

module D4 : DEQUE = struct
  module D = Kaplan2_bench_helpers.Deque4
  type 'a t = 'a D.t
  let empty = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

module Ref : DEQUE = struct
  module D = Kaplan2_bench_helpers.Deque4_ref
  type 'a t = 'a D.t
  let empty = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

(* ------------------------------------------------------------------ *)
(* Workloads, parameterized by DEQUE.                                  *)
(* ------------------------------------------------------------------ *)

module Workloads (D : DEQUE) = struct
  let steady_push n =
    let d = ref D.empty in
    for i = 1 to n do d := D.push i !d done

  let steady_inject n =
    let d = ref D.empty in
    for i = 1 to n do d := D.inject !d i done

  let drain n =
    let d = ref D.empty in
    for i = 1 to n do d := D.push i !d done;
    for _ = 1 to n do
      match D.pop !d with Some (_, d') -> d := d' | None -> ()
    done

  let alt_push_pop n =
    let d = ref D.empty in
    for i = 1 to n do
      d := D.push i !d;
      (match D.pop !d with Some (_, d') -> d := d' | None -> ())
    done

  let mixed_pipopo n =
    let d = ref D.empty in
    for i = 1 to n do
      d := D.push i !d;
      d := D.inject !d (i+1);
      (match D.pop !d with Some (_, d') -> d := d' | None -> ());
      (match D.pop !d with Some (_, d') -> d := d' | None -> ())
    done

  let fork_stress n =
    let d = ref D.empty in
    for i = 1 to n do d := D.push i !d done;
    for _ = 1 to n do
      let snap = !d in
      let s = ref snap in
      for j = 1 to 16 do s := D.push j !s done
    done
end

(* ------------------------------------------------------------------ *)
(* Timer.                                                              *)
(* ------------------------------------------------------------------ *)

let time_one f =
  let t0 = Unix.gettimeofday () in
  f ();
  let t1 = Unix.gettimeofday () in
  (t1 -. t0) *. 1000.0  (* ms *)

let ns_per_op ~ms ~ops =
  (ms *. 1e6) /. float_of_int ops

(* ------------------------------------------------------------------ *)
(* Reporter.                                                           *)
(* ------------------------------------------------------------------ *)

type row = { kt : float; vi : float; d4 : float; r : float }

(* ------------------------------------------------------------------ *)
(* Workload table — name × ops_per_iter (so we can compute ns/op).     *)
(* ------------------------------------------------------------------ *)

let workloads = [
  "steady_push",    1;   (* 1 op per iter *)
  "steady_inject",  1;
  "drain",          2;   (* push + pop  *)
  "alt_push_pop",   2;   (* push + pop  *)
  "mixed_pipopo",   4;   (* push + inject + pop + pop *)
  "fork_stress",    16;  (* 16 pushes per iter *)
]

(* Whether to include the [Ref] (list) implementation on a given workload.
 * Ref's inject/eject are O(n) per op, so total cost is O(n²); any workload
 * that does inject at large n becomes intractable (n=100k → 10¹⁰ ops).
 * Skip Ref on those — print "—" instead. *)
let ref_runs ~name ~iters =
  match name with
  | "steady_push" | "alt_push_pop" | "fork_stress" -> true
  | "drain" -> true                            (* push N then pop N — both O(1) *)
  | "steady_inject" | "mixed_pipopo" -> iters <= 10_000
  | _ -> false

(* Likewise, D4 is amortized O(log n) which is fine for small n, but
 * its inject cascade at very large n + the O(log n) per-op overhead can
 * make 1M-size inject heavy.  Cap at 100k for the inject-heavy workloads. *)
let d4_runs ~name ~iters =
  match name with
  | "steady_inject" | "mixed_pipopo" -> iters <= 100_000
  | _ -> true

let bench_workload_partial ~name ~iters ~ops =
  let module Wkt  = Workloads (Kt)  in
  let module Wvi  = Workloads (Vi)  in
  let module Wd4  = Workloads (D4)  in
  let module Wref = Workloads (Ref) in
  let pick_kt   = function
    | "steady_push"    -> Wkt.steady_push    | "steady_inject"  -> Wkt.steady_inject
    | "drain"          -> Wkt.drain          | "alt_push_pop"   -> Wkt.alt_push_pop
    | "mixed_pipopo"   -> Wkt.mixed_pipopo   | "fork_stress"    -> Wkt.fork_stress
    | _ -> assert false in
  let pick_vi   = function
    | "steady_push"    -> Wvi.steady_push    | "steady_inject"  -> Wvi.steady_inject
    | "drain"          -> Wvi.drain          | "alt_push_pop"   -> Wvi.alt_push_pop
    | "mixed_pipopo"   -> Wvi.mixed_pipopo   | "fork_stress"    -> Wvi.fork_stress
    | _ -> assert false in
  let pick_d4   = function
    | "steady_push"    -> Wd4.steady_push    | "steady_inject"  -> Wd4.steady_inject
    | "drain"          -> Wd4.drain          | "alt_push_pop"   -> Wd4.alt_push_pop
    | "mixed_pipopo"   -> Wd4.mixed_pipopo   | "fork_stress"    -> Wd4.fork_stress
    | _ -> assert false in
  let pick_ref  = function
    | "steady_push"    -> Wref.steady_push   | "steady_inject"  -> Wref.steady_inject
    | "drain"          -> Wref.drain         | "alt_push_pop"   -> Wref.alt_push_pop
    | "mixed_pipopo"   -> Wref.mixed_pipopo  | "fork_stress"    -> Wref.fork_stress
    | _ -> assert false in
  let ms_kt = time_one (fun () -> pick_kt name iters) in
  let ms_vi = time_one (fun () -> pick_vi name iters) in
  let ms_d4 = if d4_runs  ~name ~iters then time_one (fun () -> pick_d4  name iters)
              else nan in
  let ms_ref = if ref_runs ~name ~iters then time_one (fun () -> pick_ref name iters)
               else nan in
  { kt = ns_per_op ~ms:ms_kt ~ops;
    vi = ns_per_op ~ms:ms_vi ~ops;
    d4 = if Float.is_nan ms_d4  then nan else ns_per_op ~ms:ms_d4  ~ops;
    r  = if Float.is_nan ms_ref then nan else ns_per_op ~ms:ms_ref ~ops; }

let pp_ns x = if Float.is_nan x then "—" else Printf.sprintf "%.1f" x
let pp_ratio f vi =
  if Float.is_nan f || vi = 0.0 then "—"
  else Printf.sprintf "%.2f" (f /. vi)

let print_row_partial name iters _ops_per_iter row =
  Printf.printf
    "| %-15s | %7d | %7s | %7s | %7s | %7s | %5s | %5s | %5s |\n%!"
    name iters
    (pp_ns row.kt) (pp_ns row.vi) (pp_ns row.d4) (pp_ns row.r)
    (pp_ratio row.kt row.vi) (pp_ratio row.d4 row.vi) (pp_ratio row.r row.vi)

let () =
  (* Sizes can be overridden:  ./canonical.exe 1000 10000 100000  *)
  let sizes =
    if Array.length Sys.argv > 1 then
      Array.to_list (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
      |> List.map int_of_string
    else
      [1_000; 10_000; 100_000]
  in
  Printf.printf "# Canonical-implementation comparison\n\n";
  Printf.printf "ns/op for each implementation across workloads × sizes. \
                  Lower is better; ratio columns are vs Viennot.\n\n";
  Printf.printf "Implementations:\n";
  Printf.printf "  - **KT**  = our verified extraction (`KTDeque.push_kt2 / ...`, WC O(1))\n";
  Printf.printf "  - **Vi**  = Viennot OCaml (vendored, hand-written WC O(1))\n";
  Printf.printf "  - **D4**  = our hand-written `Deque4` (amortized O(log n))\n";
  Printf.printf "  - **Ref** = list-based reference (O(1) push/pop, O(n) inject/eject)\n\n";
  Printf.printf "A `—` means the implementation was skipped on that cell because\n";
  Printf.printf "its asymptotic cost made the run intractable.  See `ref_runs` / \
                  `d4_runs` predicates in the source.\n\n";
  List.iter (fun n ->
    Printf.printf "## n = %d iters\n\n" n;
    Printf.printf "| Workload        |  iters  |    KT   |    Vi   |    D4   |   Ref   | KT/Vi | D4/Vi | Ref/Vi |\n";
    Printf.printf "| --------------- | ------: | ------: | ------: | ------: | ------: | ----: | ----: | -----: |\n%!";
    List.iter (fun (name, ops_per_iter) ->
      let ops = n * ops_per_iter in
      let row = bench_workload_partial ~name ~iters:n ~ops in
      print_row_partial name n ops_per_iter row
    ) workloads;
    Printf.printf "\n%!";
  ) sizes;
  Printf.printf "## Notes\n\n";
  Printf.printf "* `Ref` is excluded from inject-heavy workloads at large n\n";
  Printf.printf "  because its O(n)-per-inject cost makes total time O(n²) — at\n";
  Printf.printf "  n=100k, that is ~10¹⁰ pointer dereferences.  Where shown, it\n";
  Printf.printf "  acts as a sanity oracle: if KT/Vi/D4 disagreed with Ref on\n";
  Printf.printf "  trace output, that would be a bug — but here we only\n";
  Printf.printf "  measure timing, not correctness (see `dune runtest` for that).\n";
  Printf.printf "* `D4` (our hand-written) uses a recursive spill scheme;\n";
  Printf.printf "  worst-case is O(log n) per op.  It is included to show the\n";
  Printf.printf "  cost the verified WC-O(1) variant `KT` saves over a more\n";
  Printf.printf "  naive functional design.\n";
  Printf.printf "* The strongest external reference is `Vi` (Viennot's\n";
  Printf.printf "  hand-written real-time deque from VWGP PLDI'24).  Adding\n";
  Printf.printf "  more canonical alternatives (e.g. Okasaki banker's deque,\n";
  Printf.printf "  Hood-Melville real-time deque) requires vendoring those\n";
  Printf.printf "  implementations into `ocaml/bench/`; the framework here\n";
  Printf.printf "  (`module type DEQUE` + `Workloads` functor) is set up so\n";
  Printf.printf "  adding one is ≈ 30 lines.\n"
