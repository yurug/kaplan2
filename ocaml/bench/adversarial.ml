(** adversarial.ml — persistent-fork microbench.

    Purpose: demonstrate the operational difference between worst-case
    O(1) (KT, Vi) and amortized O(log n) (D4) under a workload that
    breaks the amortized analysis.

    The amortized analysis on D4 buys "average over a sequence of M
    operations".  It does NOT bound a single operation: D4's cascade
    depth at a state s is whatever s deserves, up to O(log n).

    Persistence breaks the amortized argument: take a saved state s,
    apply ONE op repeatedly (each call returns a new deque, the saved
    state is unchanged).  Each call pays the *single-op* cost of state
    s.  No credits carry across calls because the calls do not chain.

    All states tested here are *reachable* from empty by ordinary
    sequences of push operations.  We pick logical sizes
    N = 5*(2^(d+1)-1) — the depth where, after N sequential pushes from
    empty, the resulting D4 chain has just enough cascade boundaries
    aligned that a single additional push pays Θ(d) work.  Persistent
    push from such a state pays that Θ(d) cost on every iteration.

    For KT, Vi and the C library we build via sequential pushes to the
    same logical size; their per-op cost is state-independent (WC O(1))
    so any state suffices.

    Run via [bench/adversarial.sh].  Output is one row per (impl, depth)
    with ns/op for [m] persistent pushes from the saved state. *)

open Ktdeque_bench_helpers

(* ------------------------------------------------------------------ *)
(* Generic timer                                                        *)
(* ------------------------------------------------------------------ *)

let now () = Unix.gettimeofday ()

let warmup () =
  (* One light pass through every impl to warm allocator, major heap,
     branch predictor, ICache.  Output is suppressed. *)
  let n = 1000 in
  let kt = ref KTDeque.empty_kchain in
  for i = 1 to n do
    match KTDeque.push_kt2 (KTDeque.Coq_E.base i) !kt with
    | Some k' -> kt := k'
    | None -> ()
  done;
  let vi = ref Viennot_deque.Deque.Base.empty in
  for i = 1 to n do vi := Viennot_deque.Deque.Base.push i !vi done;
  let d4 = ref Deque4.empty in
  for i = 1 to n do d4 := Deque4.push i !d4 done

(* ------------------------------------------------------------------ *)
(* Logical size we run at for each "depth" point.                      *)
(* N = 5*(2^(d+1) - 1) — the size where N sequential pushes from empty *)
(* leave D4 in a state from which one more push triggers a Θ(d)       *)
(* cascade.  Match the C-side bench's logical_size so the X-axis is    *)
(* identical across runtimes.                                           *)
(* ------------------------------------------------------------------ *)

let logical_size depth = 5 * ((1 lsl (depth + 1)) - 1)

(* ------------------------------------------------------------------ *)
(* For KT and Vi we build via sequential pushes to the same N.         *)
(* Their per-op cost is state-independent (WC O(1)) so any state       *)
(* of the right size makes the comparison fair.                         *)
(* ------------------------------------------------------------------ *)

let build_kt n =
  let kt = ref KTDeque.empty_kchain in
  for i = 1 to n do
    match KTDeque.push_kt2 (KTDeque.Coq_E.base i) !kt with
    | Some k' -> kt := k'
    | None -> failwith "build_kt: regularity violated"
  done;
  !kt

let build_vi n =
  let vi = ref Viennot_deque.Deque.Base.empty in
  for i = 1 to n do vi := Viennot_deque.Deque.Base.push i !vi done;
  !vi

let build_d4 n =
  let d4 = ref Deque4.empty in
  for i = 1 to n do d4 := Deque4.push i !d4 done;
  !d4

(* ------------------------------------------------------------------ *)
(* Timed loops: M persistent pushes from a saved state.  We discard    *)
(* the resulting deques (let _ =) so each iteration starts from the    *)
(* same saved state.                                                   *)
(* ------------------------------------------------------------------ *)

let time_persistent_push_kt ~m saved =
  let t0 = now () in
  for i = 1 to m do
    match KTDeque.push_kt2 (KTDeque.Coq_E.base i) saved with
    | Some _ -> ()
    | None -> ()
  done;
  ((now () -. t0) *. 1e9) /. float m

let time_persistent_push_vi ~m saved =
  let t0 = now () in
  for i = 1 to m do
    let _ = Viennot_deque.Deque.Base.push i saved in ()
  done;
  ((now () -. t0) *. 1e9) /. float m

let time_persistent_push_d4 ~m saved =
  let t0 = now () in
  for i = 1 to m do
    let _ = Deque4.push i saved in ()
  done;
  ((now () -. t0) *. 1e9) /. float m

(* ------------------------------------------------------------------ *)
(* CSV emitter.  One row per (impl, depth, ns_per_op).                 *)
(* ------------------------------------------------------------------ *)

let emit ~impl ~depth ~size ~ns =
  Printf.printf "%s,%d,%d,%.3f\n%!" impl depth size ns

(* ------------------------------------------------------------------ *)
(* Driver: range over cascade depths, run M persistent pushes per      *)
(* (impl, depth), emit CSV rows.                                       *)
(* ------------------------------------------------------------------ *)

let run depths m =
  Printf.printf "impl,depth,size,ns_per_op\n";
  warmup ();
  List.iter (fun depth ->
    let size = logical_size depth in
    (* D4 built by sequential push from empty — reachable, and at this
       choice of size already pays Θ(d) per persistent push. *)
    let d4_state = build_d4 size in
    let ns_d4 = time_persistent_push_d4 ~m d4_state in
    emit ~impl:"D4" ~depth ~size ~ns:ns_d4;
    (* KT and Vi at the same size — WC bounds make state irrelevant. *)
    let kt_state = build_kt size in
    let ns_kt = time_persistent_push_kt ~m kt_state in
    emit ~impl:"KT" ~depth ~size ~ns:ns_kt;
    let vi_state = build_vi size in
    let ns_vi = time_persistent_push_vi ~m vi_state in
    emit ~impl:"Viennot" ~depth ~size ~ns:ns_vi;
  ) depths

let () =
  (* Default: depths 0..16 (sizes 5 .. 5*(2^17-1) ≈ 655k), M=200k. *)
  let depths = ref (List.init 17 (fun i -> i)) in
  let m = ref 200_000 in
  let depths_arg = ref None in
  let m_arg = ref None in
  Arg.parse [
    "--depths", Arg.String (fun s -> depths_arg := Some s),
      "comma-separated cascade depths (default: 0..16)";
    "--m", Arg.Int (fun x -> m_arg := Some x),
      "iterations per (impl, depth) point (default: 200000)";
  ] (fun _ -> ()) "adversarial: persistent-fork microbench";
  (match !depths_arg with
   | Some s -> depths := List.map int_of_string (String.split_on_char ',' s)
   | None -> ());
  (match !m_arg with Some x -> m := x | None -> ());
  run !depths !m
