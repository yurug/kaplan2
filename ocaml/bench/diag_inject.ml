(** Diagnostic: trace push 100 + step-by-step inject (KChain version) to find
    the failure shape. *)

open Kt_deque_ptr

let print_buf_size : type a. a buf5 -> string = function
  | B0 -> "B0" | B1 _ -> "B1" | B2 _ -> "B2"
  | B3 _ -> "B3" | B4 _ -> "B4" | B5 _ -> "B5"

let col_str = function
  | Green -> "G" | Yellow -> "Y" | Red -> "R"

let rec packet_str : type a. a packet -> string = function
  | Hole -> "[]"
  | PNode (pre, i, suf) ->
      Printf.sprintf "(%s %s %s)" (print_buf_size pre) (packet_str i) (print_buf_size suf)

let rec kchain_str : type a. a kChain -> string = function
  | KEnding b -> Printf.sprintf "End(%s)" (print_buf_size b)
  | KCons (col, p, c) -> Printf.sprintf "%s%s::%s" (col_str col) (packet_str p) (kchain_str c)

let push x t = match push_kt2 (E.base x) t with
  | Some t' -> t'
  | None -> failwith "push failed"

let inject t x = match inject_kt2 t (E.base x) with
  | Some t' -> Some t'
  | None -> None

let () =
  Printf.printf "Building to size 100 via push_kt2...\n%!";
  let t = ref empty_kchain in
  for i = 1 to 100 do t := push i !t done;
  Printf.printf "  after 100 pushes: %s\n%!" (kchain_str !t);
  Printf.printf "\nInjecting step by step:\n%!";
  let i = ref 0 in
  (try
    while true do
      let v = 100 + !i in
      (match inject !t v with
       | Some t' -> t := t'
       | None ->
           Printf.printf "  iter %d (inject %d): FAILED, state was: %s\n%!" !i v (kchain_str !t);
           raise Exit);
      Printf.printf "  iter %d (inject %d): ok, %s\n%!" !i v (kchain_str !t);
      incr i;
      if !i > 30 then raise Exit
    done
  with Exit -> ())
