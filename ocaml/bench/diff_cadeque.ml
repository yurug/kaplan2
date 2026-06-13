(* diff_cadeque.ml — deterministic CATENABLE workload + per-slot sequences.
 *
 * The companion C driver (c/tests/diff_cadeque.c) generates the SAME
 * workload (same xorshift64 seed/sequence, same op decoding) against the
 * hand-written C catenable port, and emits the same text.  `diff` the two
 * outputs to detect any divergence between the C port and this verified
 * Coq-extracted artifact (KTFlatCadeque, keystone in
 * rocq/KTDeque/Catenable/FlatKeystone.v).
 *
 * Must stay byte-for-byte in step with the C driver: same PRNG, same
 * number of PRNG draws per step, same op decoding, same output format. *)

module C = KTFlatCadeque

let xs = ref 0L
let xnext () =
  let open Int64 in
  let x = !xs in
  let x = logxor x (shift_left x 13) in
  let x = logxor x (shift_right_logical x 7) in
  let x = logxor x (shift_left x 17) in
  xs := x; x

(* unsigned mod K of a 64-bit value *)
let umod (x : int64) (k : int) : int =
  Int64.to_int (Int64.unsigned_rem x (Int64.of_int k))

let push x d = C.cad_push_x x d
let inject d x = C.cad_inject_x d x
let pop d = match C.cad_pop_x d with Some (x, d') -> Some (x, d') | None -> None
let eject d = match C.cad_eject_x d with Some (d', x) -> Some (d', x) | None -> None
let concat a b = match C.cad_concat_x a b with
  | Some c -> c
  | None -> failwith "cad_concat_x: None on regular inputs"

let () =
  let n = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 100000 in
  let seed =
    if Array.length Sys.argv > 2 then
      Int64.of_string ("0x" ^ Sys.argv.(2))
    else 0x123456789abcdef0L in
  let k = if Array.length Sys.argv > 3 then int_of_string Sys.argv.(3) else 8 in
  let k = if k < 2 then 2 else k in
  xs := seed;

  let slot = Array.make k C.fcad_empty in
  let ctr = ref 1 in
  for _ = 1 to n do
    let op = umod (xnext ()) 5 in
    let i = umod (xnext ()) k in
    (match op with
     | 0 -> slot.(i) <- push !ctr slot.(i); incr ctr
     | 1 -> slot.(i) <- inject slot.(i) !ctr; incr ctr
     | 2 -> (match pop slot.(i) with Some (_, d') -> slot.(i) <- d' | None -> ())
     | 3 -> (match eject slot.(i) with Some (d', _) -> slot.(i) <- d' | None -> ())
     | _ ->
        (* j <> i: self-concat would double the length (exponential) *)
        let j = (i + 1 + umod (xnext ()) (k - 1)) mod k in
        slot.(i) <- concat slot.(i) slot.(j);
        slot.(j) <- C.fcad_empty)
  done;

  let buf = Buffer.create (1 lsl 20) in
  let total = ref 0 in
  for i = 0 to k - 1 do
    (* length via a pop-drain count on a copy *)
    let rec len acc d = match pop d with Some (_, d') -> len (acc+1) d' | None -> acc in
    Buffer.add_string buf (Printf.sprintf "SLOT %d [%d]:" i (len 0 slot.(i)));
    let rec drain d = match pop d with
      | Some (x, d') -> Buffer.add_string buf (Printf.sprintf " %d" x); incr total; drain d'
      | None -> () in
    drain slot.(i);
    Buffer.add_char buf '\n'
  done;
  Buffer.add_string buf (Printf.sprintf "DONE total=%d\n" !total);
  print_string (Buffer.contents buf)
