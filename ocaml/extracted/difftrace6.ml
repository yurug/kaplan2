(** difftrace6.ml — per-op trace of the §6 catenable deque (KTCadeque) under a
    mulberry32-seeded workload, byte-for-byte comparable to the TypeScript port
    (ts/test/difftrace.ts).  Same PRNG, same op selection, same output format:
    one line per op = the current sequence, space-separated.

    Args:  difftrace6.exe [SEED] [N]      (defaults 12345 200) *)

open KTCadeque

(* mulberry32 — bit-exact to the JS via Int32 (32-bit wrapping mul/add, logical
   shift-right).  state holds the post-increment value (as in the JS closure). *)
let state = ref 0l
let seed_prng s = state := Int32.of_int (s land 0xFFFFFFFF)

let next_unit () =
  let a = Int32.add !state 0x6D2B79F5l in
  state := a;
  let t = Int32.mul (Int32.logxor a (Int32.shift_right_logical a 15)) (Int32.logor 1l a) in
  let t =
    Int32.logxor
      (Int32.add t (Int32.mul (Int32.logxor t (Int32.shift_right_logical t 7)) (Int32.logor 61l t)))
      t
  in
  let r = Int32.logxor t (Int32.shift_right_logical t 14) in
  let ru = Int32.to_int r land 0xFFFFFFFF in
  float_of_int ru /. 4294967296.0

let irange n = int_of_float (floor (next_unit () *. float_of_int n))

let print_chain d =
  print_string (String.concat " " (List.map string_of_int (cad_to_list d)));
  print_newline ()

let () =
  let seed = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 12345 in
  let n = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 200 in
  seed_prng seed;
  let d = ref cad_empty in
  let next = ref 1 in
  for _ = 1 to n do
    let op = irange 100 in
    if op < 28 then (
      d := cad_push !next !d;
      incr next)
    else if op < 56 then (
      d := cad_inject !d !next;
      incr next)
    else if op < 71 then (match cad_pop !d with Some (_, d') -> d := d' | None -> ())
    else if op < 86 then (match cad_eject !d with Some (d', _) -> d := d' | None -> ())
    else begin
      let cnt = irange 14 in
      let d2 = ref cad_empty in
      for _ = 1 to cnt do
        if next_unit () < 0.5 then (
          d2 := cad_push !next !d2;
          incr next)
        else (
          d2 := cad_inject !d2 !next;
          incr next)
      done;
      match cad_concat !d !d2 with Some r -> d := r | None -> failwith "concat None"
    end;
    print_chain !d
  done
