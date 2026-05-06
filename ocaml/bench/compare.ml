(** Side-by-side benchmark: the verified KTDeque library vs Viennot's Deque4.

    Uses the public [push_kt2 / pop_kt2 / inject_kt2 / eject_kt2] API
    — the bounded-cascade WC O(1) entry points that the [ktdeque] opam
    package advertises and that the QCheck/Monolith suites validate. *)

(* ---------- KTDeque (verified extraction, kt2 family) ---------- *)
module Kt = struct
  open KTDeque

  type 'a t = 'a kChain

  let empty : 'a t = empty_kchain

  let push x t = match push_kt2 (Coq_E.base x) t with
    | Some t' -> t'
    | None    -> failwith "Kt.push: regularity invariant violated"

  let inject t x = match inject_kt2 t (Coq_E.base x) with
    | Some t' -> t'
    | None    -> failwith "Kt.inject: regularity invariant violated"

  let pop t = match pop_kt2 t with
    | Some (e, t') ->
        let xs = Coq_E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "Kt.pop: top element not a base singleton")
    | None -> None

  let eject t = match eject_kt2 t with
    | Some (t', e) ->
        let xs = Coq_E.to_list e in
        (match xs with
         | [x] -> Some (t', x)
         | _   -> failwith "Kt.eject: top element not a base singleton")
    | None -> None
end

(* ---------- Viennot ---------- *)
module Vi = struct
  module D = Viennot_deque.Deque.Base

  type 'a t = 'a D.t

  let empty : 'a t = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

(* ---------- D4: hand-written amortized O(log n) (bench-helpers) ---------- *)
(* Included in the sweep so a reader can see the per-op cost drift
   that the WC-O(1) discipline avoids: D4's cascade depth grows
   logarithmically with N, so its line should rise slowly while KT and
   Vi stay flat. *)
module D4 = struct
  module D = Ktdeque_bench_helpers.Deque4

  type 'a t = 'a D.t

  let empty : 'a t = D.empty
  let push x t = D.push x t
  let inject t x = D.inject t x
  let pop t = D.pop t
  let eject t = D.eject t
end

(* ---------- Generic timer ---------- *)
let time label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-30s : %8.3f ms\n" label ((t1 -. t0) *. 1000.0);
  r

(* Warm allocator, OCaml minor heap, branch predictor, ICache before
   the first timed measurement.  Without this the N=10^4 row of the
   sweep absorbed runtime startup cost (~150-200 ns/op anomaly).
   Keep the warmup small enough that it does not perturb the major
   heap state of the subsequent timed loops. *)
let warmup_runtime () =
  let n = 1_000 in
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  let d4 = ref D4.empty in
  for i = 1 to n do
    kt := Kt.push i !kt;
    vi := Vi.push i !vi;
    d4 := D4.push i !d4
  done;
  for _ = 1 to n do
    (match Kt.pop !kt with Some (_, k') -> kt := k' | None -> ());
    (match Vi.pop !vi with Some (_, v') -> vi := v' | None -> ());
    (match D4.pop !d4 with Some (_, d') -> d4 := d' | None -> ())
  done;
  for i = 1 to n do
    kt := Kt.inject !kt i;
    vi := Vi.inject !vi i;
    d4 := D4.inject !d4 i
  done;
  for _ = 1 to n do
    (match Kt.eject !kt with Some (k', _) -> kt := k' | None -> ());
    (match Vi.eject !vi with Some (v', _) -> vi := v' | None -> ());
    (match D4.eject !d4 with Some (d', _) -> d4 := d' | None -> ())
  done

(* The sweep harness runs this binary once per (impl, size) so that at
   N=10^8 we never hold KT, Vi and D4 alive in the same OCaml heap.
   BENCH_IMPLS picks which impls to run; default = all three (the
   historical behavior, fine at small/medium N). *)
let impls_enabled =
  match Sys.getenv_opt "BENCH_IMPLS" with
  | None | Some "" | Some "ALL" -> ["KT"; "VI"; "D4"]
  | Some s ->
      String.split_on_char ',' s
      |> List.map String.trim
      |> List.filter (fun s -> s <> "")
let want impl = List.mem impl impls_enabled

let benchmark n =
  Printf.printf "=== Benchmark: %d operations ===\n" n;

  Printf.printf "Pushing %d items:\n" n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  let d4 = ref D4.empty in
  if want "KT" then
    time "KTDeque push" (fun () ->
      for i = 1 to n do kt := Kt.push i !kt done);
  if want "VI" then
    time "Viennot   push" (fun () ->
      for i = 1 to n do vi := Vi.push i !vi done);
  if want "D4" then
    time "Deque4    push" (fun () ->
      for i = 1 to n do d4 := D4.push i !d4 done);

  Printf.printf "Popping %d items:\n" n;
  if want "KT" then
    time "KTDeque pop" (fun () ->
      for _ = 1 to n do
        match Kt.pop !kt with
        | Some (_, k') -> kt := k'
        | None         -> ()
      done);
  if want "VI" then
    time "Viennot   pop" (fun () ->
      for _ = 1 to n do
        match Vi.pop !vi with
        | Some (_, v') -> vi := v'
        | None         -> ()
      done);
  if want "D4" then
    time "Deque4    pop" (fun () ->
      for _ = 1 to n do
        match D4.pop !d4 with
        | Some (_, d') -> d4 := d'
        | None         -> ()
      done);

  Printf.printf "Mixed push/pop (alternating, %d each):\n" n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  let d4 = ref D4.empty in
  if want "KT" then
    time "KTDeque mixed" (fun () ->
      for i = 1 to n do
        kt := Kt.push i !kt;
        kt := Kt.push (i+1) !kt;
        (match Kt.pop !kt with
         | Some (_, k') -> kt := k'
         | None         -> ());
      done);
  if want "VI" then
    time "Viennot   mixed" (fun () ->
      for i = 1 to n do
        vi := Vi.push i !vi;
        vi := Vi.push (i+1) !vi;
        (match Vi.pop !vi with
         | Some (_, v') -> vi := v'
         | None         -> ());
      done);
  if want "D4" then
    time "Deque4    mixed" (fun () ->
      for i = 1 to n do
        d4 := D4.push i !d4;
        d4 := D4.push (i+1) !d4;
        (match D4.pop !d4 with
         | Some (_, d') -> d4 := d'
         | None         -> ());
      done);

  Printf.printf "Inject %d items, then eject %d:\n" n n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  let d4 = ref D4.empty in
  if want "KT" then
    time "KTDeque inject" (fun () ->
      for i = 1 to n do kt := Kt.inject !kt i done);
  if want "VI" then
    time "Viennot   inject" (fun () ->
      for i = 1 to n do vi := Vi.inject !vi i done);
  if want "D4" then
    time "Deque4    inject" (fun () ->
      for i = 1 to n do d4 := D4.inject !d4 i done);
  if want "KT" then
    time "KTDeque eject" (fun () ->
      for _ = 1 to n do
        match Kt.eject !kt with
        | Some (k', _) -> kt := k'
        | None         -> ()
      done);
  if want "VI" then
    time "Viennot   eject" (fun () ->
      for _ = 1 to n do
        match Vi.eject !vi with
        | Some (v', _) -> vi := v'
        | None         -> ()
      done);
  if want "D4" then
    time "Deque4    eject" (fun () ->
      for _ = 1 to n do
        match D4.eject !d4 with
        | Some (d', _) -> d4 := d'
        | None         -> ()
      done);
  Printf.printf "\n"

let () =
  warmup_runtime ();
  if Array.length Sys.argv > 1 then
    (* Sweep mode: run at exactly the sizes given on the command line.
       Used by bench/sweep.sh. *)
    Array.iter (fun a ->
      try benchmark (int_of_string a)
      with _ -> Printf.eprintf "compare: bad size '%s'\n%!" a; exit 2
    ) (Array.sub Sys.argv 1 (Array.length Sys.argv - 1))
  else begin
    benchmark 10_000;
    benchmark 100_000;
    benchmark 1_000_000
  end
