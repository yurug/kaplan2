(** k8_tt_concat_stress — checks WC O(1) on the (T+T) concat case
    which my fixes do NOT address. *)

module K = KCadeque8

let build_simple n =
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do d := K.kcad8_push i !d done;
  !d

let build_triple n =
  let half = build_simple (n / 2) in
  K.kcad8_concat half half  (* S+S → T *)

let batch_size = 1_000

let drain_stats label ~drain d0 =
  let d = ref d0 in
  let max_batch = ref 0.0 in
  let total = ref 0.0 in
  let count = ref 0 in
  let cont = ref true in
  while !cont do
    let t0 = Unix.gettimeofday () in
    let n = ref 0 in
    while !n < batch_size && !cont do
      if drain d then incr n; incr count;
      if not (drain d) then cont := false
    done;
    let t1 = Unix.gettimeofday () in
    if !n > 0 then begin
      let bt = (t1 -. t0) *. 1e9 /. float_of_int !n in
      total := !total +. (t1 -. t0);
      if bt > !max_batch then max_batch := bt
    end
  done;
  if !count > 0 then
    let avg = !total *. 1e9 /. float_of_int !count in
    Printf.printf "  %-32s avg=%6.0f  max-batch=%9.0f  ratio=%6.1fx\n"
      label avg !max_batch (!max_batch /. avg)

let () =
  Printf.printf "k8_tt_concat_stress: testing (T+T) concat then drain.\n\n";
  List.iter (fun n ->
    Printf.printf "== N = %d (each half) ==\n" n;
    let t1 = build_triple n in
    let t2 = build_triple n in
    let combined = K.kcad8_concat t1 t2 in
    (* eject drain from the right — the (T+T) boundary cell is rightmost in m *)
    drain_stats "(T+T) eject"
      ~drain:(fun d -> match K.kcad8_eject !d with None -> false | Some (d', _) -> d := d'; true)
      combined;
  ) [1_000; 10_000]
