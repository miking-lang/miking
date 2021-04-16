open Ast
open Symbutils
open Ustring.Op

(* Can be used when debugging symbol maps *)
let _symbmap = ref SymbMap.empty

(* Checks if a term _may_ have a side effect. It is conservative
   and returns only false if it is _sure_ to not have a side effect.
   The 'nmap' contains information (third element of the tuple) if
   a symbol may contain a side effect. *)
let rec tm_has_side_effect nmap acc = function
  | TmVar (_, _, s) -> (
      if acc then true
      else
        match SymbMap.find_opt s nmap with
        | Some (_, _, effect) ->
            effect
        | None ->
            true )
  | TmConst (_, c) ->
      if acc then true else const_has_side_effect c
  | TmRef (_, _) | TmTensor (_, _) ->
      true
  | t ->
      if acc then true else sfold_tm_tm (tm_has_side_effect nmap) acc t

(* Help function that collects all variables in a term *)
let rec collect_vars (free : SymbSet.t) = function
  | TmVar (_, _, s) ->
      SymbSet.add s free
  | t ->
      sfold_tm_tm collect_vars free t

(* Help function that collects free variables in a body in a let *)
let collect_in_body s nmap free = function
  | TmLam (_, _, _, _, tlam) ->
      let vars = collect_vars SymbSet.empty tlam in
      ( SymbMap.add s (vars, false, tm_has_side_effect nmap false tlam) nmap
      , free )
  | body ->
      let vars = collect_vars SymbSet.empty body in
      let se = tm_has_side_effect nmap false body in
      (SymbMap.add s (vars, se, se) nmap, SymbSet.union vars free)

(* Collect all mappings for lets (mapping symbol name of the let
   to the set of variables in the let body). It also collects
   all variables that are free, not under a lambda in a let *)
let collect_lets nmap t =
  let rec work (nmap, free) = function
    | TmVar (_, _, s) ->
        (nmap, SymbSet.add s free)
    | TmLet (_, _, s, _, t1, t2) ->
        work (collect_in_body s nmap free t1) t2
    | TmRecLets (_, lst, tt) ->
        let f (nmap, free) (_, _, s, _, t) = collect_in_body s nmap free t in
        work (List.fold_left f (nmap, free) lst) tt
    | t ->
        sfold_tm_tm work (nmap, free) t
  in
  work (nmap, SymbSet.empty) t

(* Returns a new nmap, where it is marked with true everywhere we have
   a let that is used. Use depth-first search (DFS) in the graph with
   color marking. Returns the nmap. *)
let mark_used_lets (nmap, free) =
  let rec dfs s (visited, nmap) =
    if SymbSet.mem s visited then (visited, nmap)
    else
      let visited = SymbSet.add s visited in
      match SymbMap.find_opt s nmap with
      | Some (symset, _, se) ->
          let nmap = SymbMap.add s (symset, true, se) nmap in
          SymbSet.fold dfs symset (visited, nmap)
      | None ->
          (visited, nmap)
  in
  SymbSet.fold dfs free (SymbSet.empty, nmap) |> snd

(* Removes all lets that have not been marked as 'used'. *)
let rec remove_lets nmap = function
  | TmLet (fi, x, s, ty, t1, t2) -> (
    (* Is the let marked as used? *)
    match SymbMap.find s nmap with
    | _, true, _ ->
        TmLet (fi, x, s, ty, t1, remove_lets nmap t2)
    | _ ->
        remove_lets nmap t2 )
  | TmRecLets (fi, lst, tt) ->
      let f (_, _, s, _, _) = match SymbMap.find s nmap with _, b, _ -> b in
      let lst = List.filter f lst in
      if List.length lst = 0 then remove_lets nmap tt
      else TmRecLets (fi, lst, remove_lets nmap tt)
  | t ->
      smap_tm_tm (remove_lets nmap) t

(* Helper function for pretty printing a nmap *)
let pprint_nmap symbmap nmap =
  let f k (ss, used, se) acc =
    acc ^. us "let "
    ^. pprint_named_symb symbmap k
    ^. us " -> "
    ^. pprint_named_symbset symbmap ss
    ^. us " used = "
    ^. us (if used then "true" else "false")
    ^. us ", side effect = "
    ^. us (if se then "true" else "false")
    ^. us "\n"
  in
  SymbMap.fold f nmap (us "")

(* Helper that creates a nmap with side effect info for builtin constants *)
let make_builtin_nmap builtin_sym2term =
  let f acc (s, t) =
    let v = (SymbSet.empty, false, tm_has_side_effect SymbMap.empty false t) in
    SymbMap.add s v acc
  in
  List.fold_left f SymbMap.empty builtin_sym2term

(* Helper for extending the symbmap wiht built in names *)
let extend_symb_map_builtin builtin_name2sym symbmap =
  let f acc (xsid, s) =
    let x =
      match xsid with IdVar sid -> ustring_of_sid sid | _ -> failwith "error"
    in
    SymbMap.add s x acc
  in
  List.fold_left f symbmap builtin_name2sym

(* The main dead code elimination function 
   of flag utest is false, then utests are also removed
*)
let elimination builtin_sym2term builtin_name2sym t =
  if !disable_dead_code_elimination then t
  else (
    if !enable_debug_dead_code_info then
      _symbmap := extend_symb_map_builtin builtin_name2sym (symbmap t) ;
    (* Collect all lets and store a graph in 'nmap' and free variable in 'free' *)
    let nmap, free = collect_lets (make_builtin_nmap builtin_sym2term) t in
    if !enable_debug_dead_code_info then (
      print_endline "-- Dead code info: collected lets --" ;
      pprint_nmap !_symbmap nmap |> uprint_endline ;
      print_endline "-- Dead code info: free variables --" ;
      pprint_named_symbset !_symbmap free |> uprint_endline ) ;
    (* Mark all lets that are used in the graph *)
    let nmap = mark_used_lets (nmap, free) in
    if !enable_debug_dead_code_info then (
      print_endline "\n-- Dead code info: marked used lets --" ;
      pprint_nmap !_symbmap nmap |> uprint_endline ) ;
    (* Remove all lets that are not used *)
    remove_lets nmap t )
