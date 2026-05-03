(** Three-way crossover bench: KtRec (recursive proof artifact, theoretically
    O(log n)), KtFull (non-recursive, certified WC O(1)), and Viennot.

    Goal: find the depth (chain-size) at which the log(n) tail of the recursive
    artifact starts to lose to the WC O(1) variant, and where each implementation
    sits relative to Viennot's hand-written reference.

    Method: pre-fill the chain to size n (which gives chain depth ~ log_5(n)).
    Then time M additional pushes on top of that filled chain. Repeat for
    several sizes to plot ns/op vs n. *)

(* ---------- KtRec: recursive proof artifact ---------- *)
module KtRec = struct
  open Kt_deque_ptr

  type 'a t = 'a chain

  let empty : 'a t = empty_chain

  let push x t = match push_chain_rec (E.base x) t with
    | Some t' -> t'
    | None    -> failwith "KtRec.push: regularity invariant violated"

  let inject t x = match inject_chain_rec t (E.base x) with
    | Some t' -> t'
    | None    -> failwith "KtRec.inject: regularity invariant violated"

  let pop t = match pop_chain_rec t with
    | Some (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "KtRec.pop: top element not a base singleton")
    | None -> None

  let eject t = match eject_chain_rec t with
    | Some (t', e) ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (t', x)
         | _   -> failwith "KtRec.eject: top element not a base singleton")
    | None -> None
end

(* ---------- KtFull: Viennot-mirroring WC O(1) push (push_kt2 on KChain) - *)
module KtFull = struct
  open Kt_deque_ptr

  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let push x t = match push_kt2 (E.base x) t with
    | Some t' -> t'
    | None    -> failwith "KtFull.push: invariant violation (push_kt2 None)"

  let inject t x = match inject_kt2 t (E.base x) with
    | Some t' -> t'
    | None    -> failwith "KtFull.inject: invariant violation (inject_kt2 None)"

  let pop t = match pop_kt2 t with
    | Some (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "KtFull.pop: top element not a base singleton")
    | None -> None

  let eject t = match eject_kt2 t with
    | Some (t', e) ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (t', x)
         | _   -> failwith "KtFull.eject: top element not a base singleton")
    | None -> None
end

(* ---------- KtFast: KChain inlined / fast-path ops (push_kt3 etc.) ---------- *)
module KtFast = struct
  open Kt_deque_ptr

  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let push x t = match push_kt3 (E.base x) t with
    | Some t' -> t'
    | None    -> failwith "KtFast.push: invariant violation"

  let inject t x = match inject_kt3 t (E.base x) with
    | Some t' -> t'
    | None    -> failwith "KtFast.inject: invariant violation"

  let pop t = match pop_kt3 t with
    | Some (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "KtFast.pop: top element not a base singleton")
    | None -> None

  let eject t = match eject_kt3 t with
    | Some (t', e) ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (t', x)
         | _   -> failwith "KtFast.eject: top element not a base singleton")
    | None -> None
end

(* ---------- KtFastest: kt4 with PushOk/PopOk no-option allocation ---------- *)
module KtFastest = struct
  open Kt_deque_ptr

  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let push x t = match push_kt4 (E.base x) t with
    | PushOk t' -> t'
    | PushFail  -> failwith "KtFastest.push: invariant violation"

  let inject t x = match inject_kt4 t (E.base x) with
    | PushOk t' -> t'
    | PushFail  -> failwith "KtFastest.inject: invariant violation"

  let pop t = match pop_kt4 t with
    | PopOk (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "KtFastest.pop: top element not a base singleton")
    | PopFail -> None

  let eject t = match eject_kt4 t with
    | PopOk (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (t', x)
         | _   -> failwith "KtFastest.eject: top element not a base singleton")
    | PopFail -> None
end

(* ---------- Vi: Viennot reference ---------- *)
module Vi = struct
  module D = Viennot_deque.Deque.Base

  type 'a t = 'a D.t

  let empty : 'a t = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

(* ---------- Timing helpers ---------- *)

(** Time `iters` calls of [step], starting from [init].  Returns ns/op. *)
let bench_steady : type a. iters:int -> init:a -> step:(int -> a -> a) -> float =
 fun ~iters ~init ~step ->
  (* warmup pass *)
  let s = ref init in
  for i = 0 to min iters 1000 - 1 do s := step i !s done;
  let s = ref init in
  let t0 = Unix.gettimeofday () in
  for i = 0 to iters - 1 do s := step i !s done;
  let t1 = Unix.gettimeofday () in
  ignore (Sys.opaque_identity !s);
  (t1 -. t0) *. 1e9 /. float_of_int iters

(** Build a chain of size n by pushing 1..n. *)
let build_kt_rec n =
  let t = ref KtRec.empty in
  for i = 1 to n do t := KtRec.push i !t done;
  !t

let build_kt_full n =
  let t = ref KtFull.empty in
  for i = 1 to n do t := KtFull.push i !t done;
  !t

let build_kt_fast n =
  let t = ref KtFast.empty in
  for i = 1 to n do t := KtFast.push i !t done;
  !t

let build_kt_fastest n =
  let t = ref KtFastest.empty in
  for i = 1 to n do t := KtFastest.push i !t done;
  !t

let build_vi n =
  let t = ref Vi.empty in
  for i = 1 to n do t := Vi.push i !t done;
  !t

(** chain_depth (KtRec, recursive Chain). *)
let chain_depth_kt c =
  let open Kt_deque_ptr in
  let rec go : type a. a chain -> int = fun c -> match c with
    | Ending _ -> 0
    | ChainCons (_, c') -> 1 + go c'
  in go c

let kchain_depth c =
  let open Kt_deque_ptr in
  let rec go : type a. a kChain -> int = fun c -> match c with
    | KEnding _ -> 0
    | KCons (_, _, c') -> 1 + go c'
  in go c

(* ---------- Workload: steady-state push at size n ---------- *)

let workload_steady_push ~iters ~size =
  Printf.printf "size=%d  iters=%d\n%!" size iters;
  let kr = build_kt_rec size in
  let kf = build_kt_full size in
  let ka = build_kt_fast size in
  let kx = build_kt_fastest size in
  let vi = build_vi size in
  Printf.printf "  chain depth: rec=%d  full=%d  fast=%d  fastest=%d\n%!"
    (chain_depth_kt kr) (kchain_depth kf) (kchain_depth ka) (kchain_depth kx);
  (* Pre-compute one element once; reuse in the hot loop to avoid
     E.base alloc cost per call. *)
  let elt = Kt_deque_ptr.E.base 42 in
  let ns_kr = bench_steady ~iters ~init:kr
    ~step:(fun _ t ->
      match Kt_deque_ptr.push_chain_rec elt t with Some t' -> t' | None -> t) in
  let ns_kf =
    try bench_steady ~iters ~init:kf
      ~step:(fun _ t ->
        match Kt_deque_ptr.push_kt2 elt t with Some t' -> t' | None -> t)
    with Failure _ -> nan in
  let ns_ka =
    try bench_steady ~iters ~init:ka
      ~step:(fun _ t ->
        match Kt_deque_ptr.push_kt3 elt t with Some t' -> t' | None -> t)
    with Failure _ -> nan in
  let ns_kx =
    try bench_steady ~iters ~init:kx
      ~step:(fun _ t ->
        match Kt_deque_ptr.push_kt4 elt t with PushOk t' -> t' | PushFail -> t)
    with Failure _ -> nan in
  let ns_vi = bench_steady ~iters ~init:vi
    ~step:(fun i t -> Vi.push (size + i) t) in
  Printf.printf "  push    rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

let workload_steady_pop ~iters ~size =
  let kr = build_kt_rec (size + iters) in
  let kf = build_kt_full (size + iters) in
  let ka = build_kt_fast (size + iters) in
  let kx = build_kt_fastest (size + iters) in
  let vi = build_vi (size + iters) in
  let ns_kr = bench_steady ~iters ~init:kr
    ~step:(fun _ t -> match KtRec.pop t with Some (_, t') -> t' | None -> t) in
  let ns_kf = bench_steady ~iters ~init:kf
    ~step:(fun _ t -> match KtFull.pop t with Some (_, t') -> t' | None -> t) in
  (* Direct call into pop_kt3 / pop_kt4 — bypass the wrapper's Some-allocation. *)
  let ns_ka = bench_steady ~iters ~init:ka
    ~step:(fun _ t -> match Kt_deque_ptr.pop_kt3 t with
                       | Some (_, t') -> t'
                       | None -> t) in
  let ns_kx = bench_steady ~iters ~init:kx
    ~step:(fun _ t -> match Kt_deque_ptr.pop_kt4 t with
                       | PopOk (_, t') -> t'
                       | PopFail -> t) in
  let ns_vi = bench_steady ~iters ~init:vi
    ~step:(fun _ t -> match Vi.pop t with Some (_, t') -> t' | None -> t) in
  Printf.printf "  pop     rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

let workload_steady_inject ~iters ~size =
  Printf.printf "  size=%d inject:\n%!" size;
  let kr = build_kt_rec size in
  let kf = build_kt_full size in
  let ka = build_kt_fast size in
  let vi = build_vi size in
  let ns_kr = bench_steady ~iters ~init:kr
    ~step:(fun i t -> KtRec.inject t (size + i)) in
  let kx = build_kt_fastest size in
  let elt = Kt_deque_ptr.E.base 42 in
  let ns_kf =
    try bench_steady ~iters ~init:kf
      ~step:(fun _ t -> match Kt_deque_ptr.inject_kt2 t elt with Some t' -> t' | None -> t)
    with Failure _ -> nan in
  let ns_ka =
    try bench_steady ~iters ~init:ka
      ~step:(fun _ t -> match Kt_deque_ptr.inject_kt3 t elt with Some t' -> t' | None -> t)
    with Failure _ -> nan in
  let ns_kx =
    try bench_steady ~iters ~init:kx
      ~step:(fun _ t -> match Kt_deque_ptr.inject_kt4 t elt with PushOk t' -> t' | PushFail -> t)
    with Failure _ -> nan in
  let ns_vi = bench_steady ~iters ~init:vi
    ~step:(fun i t -> Vi.inject t (size + i)) in
  Printf.printf "  inject  rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

let workload_steady_eject ~iters ~size =
  Printf.printf "  size=%d eject:\n%!" size;
  let kr = build_kt_rec (size + iters) in
  let kf = build_kt_full (size + iters) in
  let ka = build_kt_fast (size + iters) in
  let vi = build_vi (size + iters) in
  let ns_kr = bench_steady ~iters ~init:kr
    ~step:(fun _ t -> match KtRec.eject t with Some (t', _) -> t' | None -> t) in
  let kx = build_kt_fastest (size + iters) in
  let ns_kf =
    try bench_steady ~iters ~init:kf
      ~step:(fun _ t -> match Kt_deque_ptr.eject_kt2 t with Some (t', _) -> t' | None -> t)
    with Failure _ -> nan in
  let ns_ka =
    try bench_steady ~iters ~init:ka
      ~step:(fun _ t -> match Kt_deque_ptr.eject_kt3 t with Some (t', _) -> t' | None -> t)
    with Failure _ -> nan in
  let ns_kx =
    try bench_steady ~iters ~init:kx
      ~step:(fun _ t -> match Kt_deque_ptr.eject_kt4 t with PopOk (_, t') -> t' | PopFail -> t)
    with Failure _ -> nan in
  let ns_vi = bench_steady ~iters ~init:vi
    ~step:(fun _ t -> match Vi.eject t with Some (t', _) -> t' | None -> t) in
  Printf.printf "  eject   rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

(* ========================================================================== *)
(* Adversarial workloads                                                       *)
(* ========================================================================== *)

(** Push-pop alternation: build to size N, then for each iter do push+pop.
    Net chain size stays at N but every iter exercises both directions and
    repeatedly hits the "push that fills B4 → B5 → make_red" boundary. *)
let workload_alt_pp ~iters ~size =
  Printf.printf "  size=%d alt-push-pop:\n%!" size;
  let kr = build_kt_rec size in
  let kf = build_kt_full size in
  let ka = build_kt_fast size in
  let kx = build_kt_fastest size in
  let vi = build_vi size in
  let elt = Kt_deque_ptr.E.base 42 in
  let ns_kr = bench_steady ~iters ~init:kr ~step:(fun _ t ->
    let t' = (match Kt_deque_ptr.push_chain_rec elt t with
              | Some t' -> t' | None -> t) in
    match Kt_deque_ptr.pop_chain_rec t' with
    | Some (_, t'') -> t'' | None -> t') in
  let ns_kf = try bench_steady ~iters ~init:kf ~step:(fun _ t ->
    let t' = (match Kt_deque_ptr.push_kt2 elt t with
              | Some t' -> t' | None -> t) in
    match Kt_deque_ptr.pop_kt2 t' with
    | Some (_, t'') -> t'' | None -> t')
    with Failure _ -> nan in
  let ns_ka = try bench_steady ~iters ~init:ka ~step:(fun _ t ->
    let t' = (match Kt_deque_ptr.push_kt3 elt t with
              | Some t' -> t' | None -> t) in
    match Kt_deque_ptr.pop_kt3 t' with
    | Some (_, t'') -> t'' | None -> t')
    with Failure _ -> nan in
  let ns_kx = try bench_steady ~iters ~init:kx ~step:(fun _ t ->
    let t' = (match Kt_deque_ptr.push_kt4 elt t with
              | PushOk t' -> t' | PushFail -> t) in
    match Kt_deque_ptr.pop_kt4 t' with
    | PopOk (_, t'') -> t'' | PopFail -> t')
    with Failure _ -> nan in
  let ns_vi = bench_steady ~iters ~init:vi ~step:(fun i t ->
    let t' = Vi.push (size + i) t in
    match Vi.pop t' with Some (_, t'') -> t'' | None -> t') in
  Printf.printf "  alt-pp  rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

(** Mixed cycle: each iter does push, inject, pop, eject (4 ops). *)
let workload_mixed ~iters ~size =
  Printf.printf "  size=%d mixed (P/I/Po/E):\n%!" size;
  let kr = build_kt_rec size in
  let kf = build_kt_full size in
  let ka = build_kt_fast size in
  let kx = build_kt_fastest size in
  let vi = build_vi size in
  let elt = Kt_deque_ptr.E.base 42 in
  let ns_kr = bench_steady ~iters ~init:kr ~step:(fun _ t ->
    let t = match Kt_deque_ptr.push_chain_rec elt t with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.inject_chain_rec t elt with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.pop_chain_rec t with Some (_, t) -> t | None -> t in
    match Kt_deque_ptr.eject_chain_rec t with Some (t, _) -> t | None -> t) in
  let ns_kf = try bench_steady ~iters ~init:kf ~step:(fun _ t ->
    let t = match Kt_deque_ptr.push_kt2 elt t with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.inject_kt2 t elt with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.pop_kt2 t with Some (_, t) -> t | None -> t in
    match Kt_deque_ptr.eject_kt2 t with Some (t, _) -> t | None -> t)
    with Failure _ -> nan in
  let ns_ka = try bench_steady ~iters ~init:ka ~step:(fun _ t ->
    let t = match Kt_deque_ptr.push_kt3 elt t with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.inject_kt3 t elt with Some t -> t | None -> t in
    let t = match Kt_deque_ptr.pop_kt3 t with Some (_, t) -> t | None -> t in
    match Kt_deque_ptr.eject_kt3 t with Some (t, _) -> t | None -> t)
    with Failure _ -> nan in
  let ns_kx = try bench_steady ~iters ~init:kx ~step:(fun _ t ->
    let t = match Kt_deque_ptr.push_kt4 elt t with PushOk t -> t | PushFail -> t in
    let t = match Kt_deque_ptr.inject_kt4 t elt with PushOk t -> t | PushFail -> t in
    let t = match Kt_deque_ptr.pop_kt4 t with PopOk (_, t) -> t | PopFail -> t in
    match Kt_deque_ptr.eject_kt4 t with PopOk (_, t) -> t | PopFail -> t)
    with Failure _ -> nan in
  let ns_vi = bench_steady ~iters ~init:vi ~step:(fun i t ->
    let t = Vi.push (size + i) t in
    let t = Vi.inject t (size + i) in
    let t = match Vi.pop t with Some (_, t) -> t | None -> t in
    match Vi.eject t with Some (t, _) -> t | None -> t) in
  Printf.printf "  mixed   rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

(** Persistent fork stress: each iter snapshots t, does push 16 + pop 16, then
    discards and restarts from snapshot.  Tests pure-functional persistence
    cost — every iter starts from the same chain, so no chained mutation. *)
let workload_fork ~iters ~size =
  Printf.printf "  size=%d fork-stress (snap; +16; -16):\n%!" size;
  let kr = build_kt_rec size in
  let kf = build_kt_full size in
  let ka = build_kt_fast size in
  let kx = build_kt_fastest size in
  let vi = build_vi size in
  let elt = Kt_deque_ptr.E.base 42 in
  let pushpop16_kr (snap : int Kt_deque_ptr.chain) =
    let t = ref snap in
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.push_chain_rec elt !t with Some t' -> t' | None -> !t
    done;
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.pop_chain_rec !t with Some (_, t') -> t' | None -> !t
    done; () in
  let pushpop16_kf (snap : int Kt_deque_ptr.kChain) =
    let t = ref snap in
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.push_kt2 elt !t with Some t' -> t' | None -> !t
    done;
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.pop_kt2 !t with Some (_, t') -> t' | None -> !t
    done; () in
  let pushpop16_ka (snap : int Kt_deque_ptr.kChain) =
    let t = ref snap in
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.push_kt3 elt !t with Some t' -> t' | None -> !t
    done;
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.pop_kt3 !t with Some (_, t') -> t' | None -> !t
    done; () in
  let pushpop16_kx (snap : int Kt_deque_ptr.kChain) =
    let t = ref snap in
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.push_kt4 elt !t with PushOk t' -> t' | PushFail -> !t
    done;
    for _ = 1 to 16 do
      t := match Kt_deque_ptr.pop_kt4 !t with PopOk (_, t') -> t' | PopFail -> !t
    done; () in
  let pushpop16_vi (snap : int Vi.t) =
    let t = ref snap in
    for i = 1 to 16 do t := Vi.push i !t done;
    for _ = 1 to 16 do t := match Vi.pop !t with Some (_, t') -> t' | None -> !t done;
    () in
  let bench_fork f init =
    let t0 = Unix.gettimeofday () in
    for _ = 1 to iters do f init done;
    let t1 = Unix.gettimeofday () in
    (* 32 ops per fork iter (16 push + 16 pop) *)
    (t1 -. t0) *. 1e9 /. (float_of_int (iters * 32))
  in
  let ns_kr = bench_fork pushpop16_kr kr in
  let ns_kf = try bench_fork pushpop16_kf kf with Failure _ -> nan in
  let ns_ka = try bench_fork pushpop16_ka ka with Failure _ -> nan in
  let ns_kx = try bench_fork pushpop16_kx kx with Failure _ -> nan in
  let ns_vi = bench_fork pushpop16_vi vi in
  Printf.printf "  fork    rec=%6.1f  full=%6.1f  fast=%6.1f  fastest=%6.1f  vi=%6.1f   fast/vi=%.3f  fastest/vi=%.3f\n%!"
    ns_kr ns_kf ns_ka ns_kx ns_vi (ns_ka /. ns_vi) (ns_kx /. ns_vi)

(* ---------- Main: scan sizes ---------- *)

let () =
  Printf.printf "=== Three-way crossover bench (KtRec / KtFull / Viennot) ===\n%!";
  Printf.printf "Steady-state per-op timing at varying chain pre-fill sizes.\n%!";
  Printf.printf "rec    = push_chain_rec   (recursive proof artifact, O(log n) WC)\n";
  Printf.printf "full   = push_chain_full  (non-recursive, certified WC O(1))\n";
  Printf.printf "vi     = Viennot          (hand-written WC O(1) reference)\n\n%!";

  let sizes = [10; 100; 1_000; 10_000; 100_000; 1_000_000; 10_000_000] in
  let iters = 200_000 in
  List.iter (fun size -> workload_steady_push   ~iters ~size) sizes;
  Printf.printf "\n";
  List.iter (fun size -> workload_steady_pop    ~iters ~size) sizes;
  Printf.printf "\n";
  List.iter (fun size -> workload_steady_inject ~iters ~size) sizes;
  Printf.printf "\n";
  List.iter (fun size -> workload_steady_eject  ~iters ~size) sizes;
  Printf.printf "\n=== ADVERSARIAL ===\n";
  List.iter (fun size -> workload_alt_pp        ~iters ~size) sizes;
  Printf.printf "\n";
  List.iter (fun size -> workload_mixed         ~iters ~size) sizes;
  Printf.printf "\n";
  List.iter (fun size -> workload_fork ~iters:(iters / 32) ~size) sizes;
  ()
