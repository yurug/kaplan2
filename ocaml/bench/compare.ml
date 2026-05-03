(** Side-by-side benchmark: extracted KTDeque (DequePtr) vs Viennot's Deque4. *)

(* ---------- KTDeque (extracted from Coq) ---------- *)
module Kt = struct
  open Kt_deque_ptr

  type 'a t = 'a chain

  let empty : 'a t = empty_chain

  let push x t = match push_chain_rec (E.base x) t with
    | Some t' -> t'
    | None    -> failwith "Kt.push: regularity invariant violated"

  let inject t x = match inject_chain_rec t (E.base x) with
    | Some t' -> t'
    | None    -> failwith "Kt.inject: regularity invariant violated"

  let pop t = match pop_chain_rec t with
    | Some (e, t') ->
        let xs = E.to_list e in
        (match xs with
         | [x] -> Some (x, t')
         | _   -> failwith "Kt.pop: top element not a base singleton")
    | None -> None

  let eject t = match eject_chain_rec t with
    | Some (t', e) ->
        let xs = E.to_list e in
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

(* ---------- Generic timer ---------- *)
let time label f =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  Printf.printf "  %-30s : %8.3f ms\n" label ((t1 -. t0) *. 1000.0);
  r

let benchmark n =
  Printf.printf "=== Benchmark: %d operations ===\n" n;

  Printf.printf "Pushing %d items:\n" n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  time "KTDeque push" (fun () ->
    for i = 1 to n do kt := Kt.push i !kt done);
  time "Viennot   push" (fun () ->
    for i = 1 to n do vi := Vi.push i !vi done);

  Printf.printf "Popping %d items:\n" n;
  time "KTDeque pop" (fun () ->
    for _ = 1 to n do
      match Kt.pop !kt with
      | Some (_, k') -> kt := k'
      | None         -> ()
    done);
  time "Viennot   pop" (fun () ->
    for _ = 1 to n do
      match Vi.pop !vi with
      | Some (_, v') -> vi := v'
      | None         -> ()
    done);

  Printf.printf "Mixed push/pop (alternating, %d each):\n" n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  time "KTDeque mixed" (fun () ->
    for i = 1 to n do
      kt := Kt.push i !kt;
      kt := Kt.push (i+1) !kt;
      (match Kt.pop !kt with
       | Some (_, k') -> kt := k'
       | None         -> ());
    done);
  time "Viennot   mixed" (fun () ->
    for i = 1 to n do
      vi := Vi.push i !vi;
      vi := Vi.push (i+1) !vi;
      (match Vi.pop !vi with
       | Some (_, v') -> vi := v'
       | None         -> ());
    done);

  Printf.printf "Inject %d items, then eject %d:\n" n n;
  let kt = ref Kt.empty in
  let vi = ref Vi.empty in
  time "KTDeque inject" (fun () ->
    for i = 1 to n do kt := Kt.inject !kt i done);
  time "Viennot   inject" (fun () ->
    for i = 1 to n do vi := Vi.inject !vi i done);
  time "KTDeque eject" (fun () ->
    for _ = 1 to n do
      match Kt.eject !kt with
      | Some (k', _) -> kt := k'
      | None         -> ()
    done);
  time "Viennot   eject" (fun () ->
    for _ = 1 to n do
      match Vi.eject !vi with
      | Some (v', _) -> vi := v'
      | None         -> ()
    done);
  Printf.printf "\n"

let () =
  benchmark 10_000;
  benchmark 100_000;
  benchmark 1_000_000
