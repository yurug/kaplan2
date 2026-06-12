(* cadeque_compare.ml — head-to-head benchmark of the CATENABLE deques:

     KT  : our Rocq-extracted KT99 §6 cadeque, MODEL layer
           (ocaml/extracted/kTCadeque.ml): buffers are lists, colours
           recompute [length] — wall-clock per op is O(root buffer
           size); kept in the table as the honest baseline.
     KTf : our PRODUCTION extraction (ocaml/extracted/kTFlatCadeque.ml):
           the fused-spine mirror (FlatChain/FlatOps: one heap block
           per spine cell; keystone bundle in Catenable/FlatKeystone.v
           via erasure commutation) with buffers remapped at
           extraction to Fastbuf = the verified §4 kt4 deque + O(1)
           size.  Wall-clock WC O(1) on every end.
     Vi  : Viennot/Wendling/Guéneau/Pottier hand-written OCaml cadeque
           (vendored at ocaml/bench/viennot/, MIT), production-quality,
           wall-clock WC O(1).

   Driven by bench/cadeque-compare.sh.  Output: one markdown table of
   ns/op.  A per-cell time guard skips larger sizes for an (impl,
   workload) pair once a smaller size blows the budget — quadratic cells
   print as "(>cap)" instead of hanging the run. *)

let time_budget = 10.0 (* seconds per cell before larger sizes are skipped *)

(* ------------------------------------------------------------------ *)
(* Implementations behind one signature.                               *)
(* ------------------------------------------------------------------ *)

module type CADEQUE = sig
  type 'a t
  val empty : 'a t
  val push : 'a -> 'a t -> 'a t
  val inject : 'a t -> 'a -> 'a t
  val pop : 'a t -> ('a * 'a t) option
  val eject : 'a t -> ('a t * 'a) option
  val concat : 'a t -> 'a t -> 'a t
  val to_list : 'a t -> 'a list
end

module KT : CADEQUE = struct
  type 'a t = 'a KTCadeque.cadeque
  let empty = KTCadeque.cad_empty
  let push = KTCadeque.cad_push
  let inject = KTCadeque.cad_inject
  let pop = KTCadeque.cad_pop
  let eject = KTCadeque.cad_eject
  let concat a b =
    match KTCadeque.cad_concat a b with
    | Some c -> c
    | None -> failwith "cad_concat returned None on regular inputs"
  let to_list = KTCadeque.cad_to_list
end

(* the production extraction: fused-spine mirror + Fastbuf (kt4 + size) *)
module KTF : CADEQUE = struct
  type 'a t = 'a KTFlatCadeque.fchain
  let empty = KTFlatCadeque.fcad_empty
  let push = KTFlatCadeque.cad_push_x
  let inject = KTFlatCadeque.cad_inject_x
  let pop = KTFlatCadeque.cad_pop_x
  let eject = KTFlatCadeque.cad_eject_x
  let concat a b =
    match KTFlatCadeque.cad_concat_x a b with
    | Some c -> c
    | None -> failwith "cad_concat_x returned None on regular inputs"
  let to_list d =
    let rec go acc d =
      match KTFlatCadeque.cad_pop_x d with
      | Some (x, d') -> go (x :: acc) d'
      | None -> List.rev acc
    in
    go [] d
end

module Vi : CADEQUE = struct
  module Cadeque = Viennot_deque.Cadeque
  type 'a t = 'a Cadeque.t
  let empty = Cadeque.empty
  let push = Cadeque.push
  let inject = Cadeque.inject
  let pop = Cadeque.pop
  let eject = Cadeque.eject
  let concat = Cadeque.append
  let to_list d =
    List.rev (Cadeque.fold_left (fun acc x -> x :: acc) [] d)
end

(* ------------------------------------------------------------------ *)
(* Workloads (functorized).  Each returns an int guard so the work     *)
(* cannot be eliminated.  [n] is the op count of the TIMED phase.      *)
(* ------------------------------------------------------------------ *)

module Work (D : CADEQUE) = struct
  let build_push n =
    let d = ref D.empty in
    for i = 0 to n - 1 do d := D.push i !d done;
    !d

  let build_inject n =
    let d = ref D.empty in
    for i = 0 to n - 1 do d := D.inject !d i done;
    !d

  (* steady push of n elements *)
  let w_push n = let d = build_push n in match D.pop d with Some (x, _) -> x | None -> 0

  (* steady inject of n elements *)
  let w_inject n = let d = build_inject n in match D.pop d with Some (x, _) -> x | None -> 0

  (* drain a prebuilt deque from the front; prep is untimed (see runner) *)
  let w_pop_all d =
    let s = ref 0 and c = ref d in
    let rec go () = match D.pop !c with
      | None -> ()
      | Some (x, c') -> s := !s + x; c := c'; go ()
    in go (); !s

  let w_eject_all d =
    let s = ref 0 and c = ref d in
    let rec go () = match D.eject !c with
      | None -> ()
      | Some (c', x) -> s := !s + x; c := c'; go ()
    in go (); !s

  (* steady-state queue: n rounds of push;push;pop — deque stays small-ish
     only if pops keep up; here it grows to n, mixing both ends' costs *)
  let w_mixed n =
    let d = ref D.empty and s = ref 0 in
    for i = 0 to n - 1 do
      d := D.push i !d;
      d := D.push (i + 1) !d;
      (match D.pop !d with
       | Some (x, d') -> s := !s + x; d := d'
       | None -> ())
    done; !s

  (* fold-concat k deques of m elements each, left to right (timed phase =
     k-1 concats); op count reported = k *)
  let w_concat_fold blocks =
    let d = List.fold_left D.concat D.empty blocks in
    match D.pop d with Some (x, _) -> x | None -> 0

  (* balanced pairwise concat rounds (timed phase = k-1 concats) *)
  let w_concat_tree blocks =
    let rec round = function
      | [] -> []
      | [d] -> [d]
      | a :: b :: r -> D.concat a b :: round r
    in
    let rec go = function
      | [] -> D.empty
      | [d] -> d
      | l -> go (round l)
    in
    let d = go blocks in
    match D.pop d with Some (x, _) -> x | None -> 0

  (* concat + removal interleaving: n rounds of (concat an 8-block, pop 4) —
     keeps the deque growing while constantly exercising root repair *)
  let w_concat_pushpop n block8 =
    let d = ref block8 and s = ref 0 in
    for _ = 1 to n - 1 do
      d := D.concat !d block8;
      for _ = 1 to 4 do
        match D.pop !d with
        | Some (x, d') -> s := !s + x; d := d'
        | None -> ()
      done
    done; !s

  (* persistence stress: re-run pop n times from the SAME saved deque —
     defeats amortization, every rerun must be fast *)
  let w_fork_pop d n =
    let s = ref 0 in
    for _ = 1 to n do
      match D.pop d with
      | Some (x, _) -> s := !s + x
      | None -> ()
    done; !s

  (* sequence-correctness self-check at small n *)
  let selfcheck () =
    let d = build_push 100 in                          (* 99..0 *)
    let d = D.inject d 1000 in
    let l1 = D.to_list d in
    let a = build_push 50 and b = build_inject 50 in
    let l2 = D.to_list (D.concat a b) in
    (l1, l2)
end

module WKT = Work (KT)
module WKTF = Work (KTF)
module WVi = Work (Vi)

(* ------------------------------------------------------------------ *)
(* Runner.                                                             *)
(* ------------------------------------------------------------------ *)

let guard = ref 0

let time f =
  let t0 = Unix.gettimeofday () in
  guard := !guard + f ();
  Unix.gettimeofday () -. t0

(* one row of cells: workload w at sizes [ns] for one impl; returns
   strings (ns/op or "(>cap)").  A cell is skipped when the PROJECTED
   time — last cell's time scaled quadratically in n, the worst case
   for the model layer — exceeds the budget, so no cell ever runs for
   minutes. *)
let run_cells ~ops_of ~mk_thunk ns =
  let dead = ref false in
  let last : (int * float) option ref = ref None in
  List.map
    (fun n ->
       let projected =
         match !last with
         | Some (n0, t0) ->
             let r = float_of_int n /. float_of_int n0 in
             t0 *. r *. r
         | None -> 0.0
       in
       if !dead || projected > time_budget then begin dead := true; "(>cap)" end
       else begin
         let thunk = mk_thunk n in
         (* normalize major-heap state between cells: without this, a
            cell's wall-clock depends on the allocation history of the
            cells before it (the model layer's quadratic cells bloat
            the major heap and tax every later measurement). *)
         Gc.compact ();
         let t = time thunk in
         last := Some (n, t);
         if t > time_budget then dead := true;
         Printf.sprintf "%.0f" (t *. 1e9 /. float_of_int (ops_of n))
       end)
    ns

let header ns =
  let cols = String.concat " | " (List.map (fun n -> Printf.sprintf "n=%d" n) ns) in
  Printf.printf "| workload | impl | %s |\n" cols;
  Printf.printf "|---|---|%s\n" (String.concat "" (List.map (fun _ -> "---:|") ns))

let row name impl cells =
  Printf.printf "| %s | %s | %s |\n%!" name impl (String.concat " | " cells)

let () =
  let ns =
    match Array.to_list Sys.argv with
    | _ :: rest when rest <> [] -> List.map int_of_string rest
    | _ -> [ 1_000; 10_000; 100_000; 1_000_000 ]
  in
  (* correctness cross-check first *)
  let (k1, k2) = WKT.selfcheck () and (v1, v2) = WVi.selfcheck () in
  let (f1, f2) = WKTF.selfcheck () in
  if k1 <> v1 || k2 <> v2 || f1 <> v1 || f2 <> v2 then begin
    prerr_endline "SELF-CHECK FAILED: sequence semantics disagree";
    exit 1
  end;
  Printf.printf
    "<!-- self-check OK: KT, KTfast and Viennot agree on sequences -->\n";
  (* warm code paths + minor heap before the first timed cell *)
  guard := !guard + WKT.w_push 2000 + WKTF.w_push 2000 + WVi.w_push 2000;
  Printf.printf "\nAll cells are **ns per operation** (lower is better); \
                 \"(>cap)\" = a smaller size already exceeded the %.0f s \
                 cell budget (quadratic regime).\n\n" time_budget;
  header ns;

  let id n = n in
  (* push *)
  row "push n" "KT" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WKT.w_push n) ns);
  row "push n" "KTf" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WKTF.w_push n) ns);
  row "push n" "Vi" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WVi.w_push n) ns);
  (* inject *)
  row "inject n" "KT" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WKT.w_inject n) ns);
  row "inject n" "KTf" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WKTF.w_inject n) ns);
  row "inject n" "Vi" (run_cells ~ops_of:id ~mk_thunk:(fun n () -> WVi.w_inject n) ns);
  (* pop-all (prebuild untimed) *)
  row "pop all (after push n)" "KT"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKT.build_push n in fun () -> WKT.w_pop_all d) ns);
  row "pop all (after push n)" "KTf"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKTF.build_push n in fun () -> WKTF.w_pop_all d) ns);
  row "pop all (after push n)" "Vi"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WVi.build_push n in fun () -> WVi.w_pop_all d) ns);
  (* eject-all *)
  row "eject all (after inject n)" "KT"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKT.build_inject n in fun () -> WKT.w_eject_all d) ns);
  row "eject all (after inject n)" "KTf"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKTF.build_inject n in fun () -> WKTF.w_eject_all d) ns);
  row "eject all (after inject n)" "Vi"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WVi.build_inject n in fun () -> WVi.w_eject_all d) ns);
  (* mixed *)
  let ops3 n = 3 * n in
  row "mixed push/push/pop (3n ops)" "KT"
    (run_cells ~ops_of:ops3 ~mk_thunk:(fun n () -> WKT.w_mixed n) ns);
  row "mixed push/push/pop (3n ops)" "KTf"
    (run_cells ~ops_of:ops3 ~mk_thunk:(fun n () -> WKTF.w_mixed n) ns);
  row "mixed push/push/pop (3n ops)" "Vi"
    (run_cells ~ops_of:ops3 ~mk_thunk:(fun n () -> WVi.w_mixed n) ns);
  (* concat fold: n/64 blocks of 64 elements *)
  let blocksz = 64 in
  let mk_blocks_kt n =
    List.init (max 1 (n / blocksz)) (fun _ -> WKT.build_push blocksz) in
  let mk_blocks_vi n =
    List.init (max 1 (n / blocksz)) (fun _ -> WVi.build_push blocksz) in
  let mk_blocks_ktf n =
    List.init (max 1 (n / blocksz)) (fun _ -> WKTF.build_push blocksz) in
  let opsk n = max 1 (n / blocksz) in
  row "concat fold (n/64 blocks of 64)" "KT"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_kt n in fun () -> WKT.w_concat_fold bs) ns);
  row "concat fold (n/64 blocks of 64)" "KTf"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_ktf n in fun () -> WKTF.w_concat_fold bs) ns);
  row "concat fold (n/64 blocks of 64)" "Vi"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_vi n in fun () -> WVi.w_concat_fold bs) ns);
  (* concat tree *)
  row "concat tree (n/64 blocks of 64)" "KT"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_kt n in fun () -> WKT.w_concat_tree bs) ns);
  row "concat tree (n/64 blocks of 64)" "KTf"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_ktf n in fun () -> WKTF.w_concat_tree bs) ns);
  row "concat tree (n/64 blocks of 64)" "Vi"
    (run_cells ~ops_of:opsk
       ~mk_thunk:(fun n -> let bs = mk_blocks_vi n in fun () -> WVi.w_concat_tree bs) ns);
  (* concat+pop interleave: n/8 rounds, each = 1 concat + 4 pops *)
  let opscp n = 5 * max 1 (n / 8) in
  row "concat(8)+pop×4 interleave" "KT"
    (run_cells ~ops_of:opscp
       ~mk_thunk:(fun n ->
         let b8 = WKT.build_push 8 in fun () -> WKT.w_concat_pushpop (max 1 (n / 8)) b8) ns);
  row "concat(8)+pop×4 interleave" "KTf"
    (run_cells ~ops_of:opscp
       ~mk_thunk:(fun n ->
         let b8 = WKTF.build_push 8 in fun () -> WKTF.w_concat_pushpop (max 1 (n / 8)) b8) ns);
  row "concat(8)+pop×4 interleave" "Vi"
    (run_cells ~ops_of:opscp
       ~mk_thunk:(fun n ->
         let b8 = WVi.build_push 8 in fun () -> WVi.w_concat_pushpop (max 1 (n / 8)) b8) ns);
  (* fork stress: build size n untimed, then n pops from the same value *)
  row "persistent fork: n× pop(same d)" "KT"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKT.build_push n in fun () -> WKT.w_fork_pop d n) ns);
  row "persistent fork: n× pop(same d)" "KTf"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WKTF.build_push n in fun () -> WKTF.w_fork_pop d n) ns);
  row "persistent fork: n× pop(same d)" "Vi"
    (run_cells ~ops_of:id
       ~mk_thunk:(fun n -> let d = WVi.build_push n in fun () -> WVi.w_fork_pop d n) ns);
  Printf.printf "\n<!-- guard=%d -->\n" !guard
