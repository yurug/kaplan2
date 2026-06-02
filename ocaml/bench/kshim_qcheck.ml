(** kshim_qcheck -- executable refinement check for KCadequeShim.buf6.

    KCadequeShim is the hand-written extraction override for Rocq's abstract
    Buf6.  This check validates the representation against the abstract list
    semantics used by the Rocq model: mkBuf6, push, inject, pop, eject,
    size, emptiness, and persistence snapshots. *)

module S = KCadequeShim

type op =
  | Push of int
  | Inject of int
  | Pop
  | Eject
  | Reset of int list

let pp_list xs =
  "[" ^ String.concat ";" (List.map string_of_int xs) ^ "]"

let random_list max_len =
  let len = Random.int (max_len + 1) in
  List.init len (fun _ -> Random.int 10_000)

let sample_op len =
  if len > 800 then
    if Random.bool () then Pop else Eject
  else
    match Random.int 24 with
    | 0 | 1 | 2 | 3 | 4 | 5 -> Push (Random.int 10_000)
    | 6 | 7 | 8 | 9 | 10 | 11 -> Inject (Random.int 10_000)
    | 12 | 13 | 14 | 15 -> Pop
    | 16 | 17 | 18 | 19 -> Eject
    | _ -> Reset (random_list 64)

let check_buf ~seed ~step b xs =
  let elems = S.buf6_elems b in
  let size = S.buf6_size b in
  let empty = S.buf6_is_empty b in
  if elems <> xs || size <> List.length xs || empty <> (xs = []) then begin
    Printf.eprintf
      "KCadequeShim mismatch seed=%d step=%d\n  elems=%s\n  ref  =%s\n  size=%d ref_size=%d empty=%b ref_empty=%b\n%!"
      seed step (pp_list elems) (pp_list xs) size (List.length xs) empty (xs = []);
    false
  end else
    true

let apply_op ~seed ~step b xs = function
  | Push x ->
      let snapshot = S.buf6_elems b in
      let b' = S.buf6_push x b in
      if S.buf6_elems b <> snapshot then begin
        Printf.eprintf "KCadequeShim persistence mismatch after push seed=%d step=%d\n%!"
          seed step;
        None
      end else
        Some (b', x :: xs)
  | Inject x ->
      let snapshot = S.buf6_elems b in
      let b' = S.buf6_inject b x in
      if S.buf6_elems b <> snapshot then begin
        Printf.eprintf "KCadequeShim persistence mismatch after inject seed=%d step=%d\n%!"
          seed step;
        None
      end else
        Some (b', xs @ [x])
  | Pop ->
      begin match S.buf6_pop b, xs with
      | None, [] -> Some (b, xs)
      | Some (y, b'), x :: rest when x = y -> Some (b', rest)
      | got, _ ->
          let got_s =
            match got with
            | None -> "None"
            | Some (y, b') -> Printf.sprintf "Some(%d,%s)" y (pp_list (S.buf6_elems b'))
          in
          Printf.eprintf
            "KCadequeShim pop mismatch seed=%d step=%d got=%s ref=%s\n%!"
            seed step got_s (pp_list xs);
          None
      end
  | Eject ->
      begin match S.buf6_eject b, List.rev xs with
      | None, [] -> Some (b, xs)
      | Some (b', y), x :: rev_rest when x = y -> Some (b', List.rev rev_rest)
      | got, _ ->
          let got_s =
            match got with
            | None -> "None"
            | Some (b', y) -> Printf.sprintf "Some(%s,%d)" (pp_list (S.buf6_elems b')) y
          in
          Printf.eprintf
            "KCadequeShim eject mismatch seed=%d step=%d got=%s ref=%s\n%!"
            seed step got_s (pp_list xs);
          None
      end
  | Reset xs' ->
      Some (S.mkBuf6 xs', xs')

let run_once ~seed ~ops_per_run =
  Random.init seed;
  let rec loop step b xs =
    if step > ops_per_run then
      true
    else if not (check_buf ~seed ~step b xs) then
      false
    else
      let op = sample_op (List.length xs) in
      match apply_op ~seed ~step b xs op with
      | None -> false
      | Some (b', xs') -> loop (step + 1) b' xs'
  in
  loop 1 S.buf6_empty []

let () =
  let runs = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 500 in
  let ops = if Array.length Sys.argv > 2 then int_of_string Sys.argv.(2) else 1_000 in
  Printf.printf
    "KCadequeShim refinement check: %d runs x %d ops...\n%!" runs ops;
  let failed = ref 0 in
  for seed = 1 to runs do
    if not (run_once ~seed ~ops_per_run:ops) then incr failed
  done;
  if !failed <> 0 then begin
    Printf.printf "FAILED: %d/%d\n%!" !failed runs;
    exit 1
  end;
  Printf.printf "OK: %d/%d runs (%d ops total)\n%!" runs runs (runs * ops)
