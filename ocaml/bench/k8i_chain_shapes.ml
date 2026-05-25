(** k8i_chain_shapes — what KChain shapes does the boundary buffer
    actually carry during a steady-state push workload?  This is to
    sanity-check the hot-of-hot fast-path patterns. *)

module K = KCadeque8

let classify (k : 'a K.kCadeque8) : string =
  match k with
  | K.K8Empty -> "K8Empty"
  | K.K8Simple (KCadequeShim.Plain (_, c)) ->
      (match c with
       | KTDeque.KEnding b ->
           (match b with
            | KTDeque.B0 -> "K8Simple Plain (KEnding B0)"
            | KTDeque.B1 _ -> "K8Simple Plain (KEnding B1)"
            | KTDeque.B2 _ -> "K8Simple Plain (KEnding B2)"
            | KTDeque.B3 _ -> "K8Simple Plain (KEnding B3)"
            | KTDeque.B4 _ -> "K8Simple Plain (KEnding B4)"
            | KTDeque.B5 _ -> "K8Simple Plain (KEnding B5)")
       | KTDeque.KCons (color, KTDeque.PNode (pre, _, _), _) ->
           let col = match color with
             | KTDeque.Green -> "G" | KTDeque.Yellow -> "Y" | KTDeque.Red -> "R" in
           let pretag = match pre with
             | KTDeque.B0 -> "B0" | KTDeque.B1 _ -> "B1" | KTDeque.B2 _ -> "B2"
             | KTDeque.B3 _ -> "B3" | KTDeque.B4 _ -> "B4" | KTDeque.B5 _ -> "B5" in
           Printf.sprintf "K8Simple Plain (KCons %s PNode(%s,_,_))" col pretag
       | KTDeque.KCons (_, KTDeque.Hole, _) -> "K8Simple Plain (KCons _ Hole _)")
  | K.K8Simple (KCadequeShim.Spilled _) -> "K8Simple Spilled"
  | K.K8Triple (_, _, _) -> "K8Triple"

let () =
  let counts = Hashtbl.create 16 in
  let bump label =
    let c = try Hashtbl.find counts label with Not_found -> 0 in
    Hashtbl.replace counts label (c + 1)
  in
  let n = 1_000_000 in
  let d = ref K.kcad8_empty in
  for i = 0 to n - 1 do
    bump (classify !d);
    d := K.kcad8_push i !d
  done;
  Printf.printf "Shapes seen by kcad8_push over %d pushes:\n" n;
  let entries = Hashtbl.fold (fun k v acc -> (k,v)::acc) counts [] in
  let entries = List.sort (fun (_,a) (_,b) -> compare b a) entries in
  List.iter (fun (k, v) ->
    let pct = 100.0 *. float_of_int v /. float_of_int n in
    Printf.printf "  %6.2f%%  %7d  %s\n" pct v k) entries
