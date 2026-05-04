(** diff_workload.ml — generates the SAME workload as c/diff_workload.c
    using the same xorshift64 seed/sequence; runs through the extracted
    [push_kt2 / pop_kt2 / inject_kt2 / eject_kt2] (proven
    sequence-preserving in OpsKTSeq.v); emits the same text format.

    Diff against the C output to detect any divergence between the two
    implementations.

    Args:  diff_workload.exe [N] [SEED_HEX] [MODE]
      N         — operation count (default 10000)
      SEED_HEX  — 64-bit xorshift seed, hex with optional "0x" prefix
                  (default 0x123456789abcdef0)
      MODE      — "mix" (default, uniform random) or "deep"
                  (4 monotonic phases of N/4: push, inject, pop, eject;
                  drives Θ(log N) deque depth and the deepest cascades). *)

open Kt_deque_ptr

(* xorshift64 — same as c/diff_workload.c. *)
let xs_state = ref 0x123456789abcdef0L
let xorshift_next () =
  let x = !xs_state in
  let x = Int64.logxor x (Int64.shift_left x 13) in
  let x = Int64.logxor x (Int64.shift_right_logical x 7) in
  let x = Int64.logxor x (Int64.shift_left x 17) in
  xs_state := x;
  x

let next_op_mix () =
  let v = xorshift_next () in
  (* The C does (uint64 % 4); replicate via Int64.logand on UNSIGNED
   * interpretation.  Since 4 divides 2^64, low 2 bits of unsigned x
   * equal low 2 bits of signed x. *)
  Int64.to_int (Int64.logand v 3L)

(* deep mode: 4 monotonic phases of N/4 ops each. *)
let next_op_deep i n =
  let q = n / 4 in
  if i < q              then 0       (* push *)
  else if i < 2 * q     then 1       (* inject *)
  else if i < 3 * q     then 2       (* pop *)
  else                       3       (* eject *)

let push x d = match push_kt2 (Coq_E.base x) d with
  | Some d' -> d'
  | None    -> failwith "push_kt2: regularity violated"

let inject d x = match inject_kt2 d (Coq_E.base x) with
  | Some d' -> d'
  | None    -> failwith "inject_kt2: regularity violated"

let pop d = match pop_kt2 d with
  | Some (e, d') ->
      (match Coq_E.to_list e with
       | [x] -> Some (x, d')
       | _   -> failwith "pop_kt2: not a base singleton")
  | None -> None

let eject d = match eject_kt2 d with
  | Some (d', e) ->
      (match Coq_E.to_list e with
       | [x] -> Some (x, d')
       | _   -> failwith "eject_kt2: not a base singleton")
  | None -> None

(* NOTE: length is tracked incrementally as a ref counter, NOT recomputed
 * via List.length each op.  Recomputing was O(n) per op → O(n²) total at
 * large n.  The counter updates in lockstep with the C side; if either
 * implementation's actual deque length disagrees with the counter, the
 * final FINAL-line walk would diverge from C and the diff would catch
 * it.  So this optimization preserves the test's discriminating power. *)

let walk d = kchain_to_list d

(* Parse a hex string with optional "0x" prefix into Int64. *)
let parse_seed_hex s =
  let s = if String.length s >= 2
             && (s.[0] = '0')
             && (s.[1] = 'x' || s.[1] = 'X')
          then s
          else "0x" ^ s in
  Int64.of_string s

let () =
  let argc = Array.length Sys.argv in
  let n = if argc > 1 then int_of_string Sys.argv.(1) else 10000 in
  let seed = if argc > 2 then parse_seed_hex Sys.argv.(2)
                         else 0x123456789abcdef0L in
  let mode = if argc > 3 then Sys.argv.(3) else "mix" in
  let deep =
    match mode with
    | "deep" -> true
    | "mix"  -> false
    | _ -> Printf.eprintf "diff_workload: unknown mode '%s' (use 'mix' or 'deep')\n" mode;
           exit 2
  in
  if n < 0 || n > 10000000 then begin
    Printf.eprintf "diff_workload: N=%d out of range [0, 10000000]\n" n;
    exit 2
  end;
  xs_state := seed;
  let d = ref empty_kchain in
  let len = ref 0 in
  let next_val = ref 1 in
  for i = 0 to n - 1 do
    let op =
      if deep then begin
        ignore (xorshift_next ());     (* consume in lockstep with C *)
        next_op_deep i n
      end else
        next_op_mix ()
    in
    (match op with
     | 0 ->
       d := push !next_val !d;
       incr len;
       Printf.printf "push %d -> len=%d\n" !next_val !len;
       incr next_val
     | 1 ->
       d := inject !d !next_val;
       incr len;
       Printf.printf "inject %d -> len=%d\n" !next_val !len;
       incr next_val
     | 2 ->
       (match pop !d with
        | Some (v, d') ->
            d := d';
            decr len;
            Printf.printf "pop %d -> len=%d\n" v !len
        | None ->
            Printf.printf "pop NONE -> len=0\n")
     | 3 ->
       (match eject !d with
        | Some (v, d') ->
            d := d';
            decr len;
            Printf.printf "eject %d -> len=%d\n" v !len
        | None ->
            Printf.printf "eject NONE -> len=0\n")
     | _ -> assert false)
  done;
  let xs = walk !d in
  Printf.printf "FINAL %d:" (List.length xs);
  List.iter (fun x -> Printf.printf " %d" x) xs;
  Printf.printf "\n"
