open Ast
open Symbutils
open Ustring.Op

let _symbmap = ref SymbMap.empty

(* Help function that collects all variables in a term *)
let rec collect_vars (free : SymbSet.t) = function
  | TmVar (_, _, s) ->
      SymbSet.add s free
  | t ->
      sfold_tm_tm collect_vars free t

let collect_in_body s nmap free = function
  | TmLam (_, _, _, _, tlam) ->
      let vars = collect_vars SymbSet.empty tlam in
      (SymbMap.add s (vars, false) nmap, free)
  | body ->
      let vars = collect_vars SymbSet.empty body in
      (SymbMap.add s (vars, true) nmap, SymbSet.union vars free)

(* Collect all mappings for lets (mapping symbol name of the let
   to the set of variables in the let body). It also collects
   all variables that are free, not under a lambda in a let *)
let collect_lets t =
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
  work (SymbMap.empty, SymbSet.empty) t

(* Returns a new nmap, where it is marked with true everywhere we have
   a let that is used. Use depth-first search (DFS) in the graph with
   color marking. Returns the nmap. *)
let mark_used_lets (nmap, free) =
  let rec dfs s (visited, nmap) =
    if SymbSet.mem s visited then (visited, nmap)
    else
      let visited = SymbSet.add s visited in
      match SymbMap.find_opt s nmap with
      | Some (symset, _) ->
          let nmap = SymbMap.add s (symset, true) nmap in
          SymbSet.fold dfs symset (visited, nmap)
      | None ->
          (visited, nmap)
  in
  SymbSet.fold dfs free (SymbSet.empty, nmap) |> snd

(* Removes all lets that have not been marked as 'used'. *)
let rec remove_lets nmap = function
  | TmLet (fi, x, s, ty, t1, t2) ->
      (* Is the let marked as used? *)
      if SymbMap.find s nmap |> snd then
        TmLet (fi, x, s, ty, t1, remove_lets nmap t2)
      else remove_lets nmap t2
  | TmRecLets (fi, lst, tt) ->
      let lst =
        List.filter (fun (_, _, s, _, _) -> SymbMap.find s nmap |> snd) lst
      in
      if List.length lst = 0 then remove_lets nmap tt
      else TmRecLets (fi, lst, remove_lets nmap tt)
  | t ->
      smap_tm_tm (remove_lets nmap) t

(* Helper function for pretty printing a nmap *)
let pprint_nmap symbmap nmap =
  let f k (ss, used) acc =
    acc ^. us "let "
    ^. pprint_named_symb symbmap k
    ^. us " -> "
    ^. pprint_named_symbset symbmap ss
    ^. us " used = "
    ^. us (if used then "true" else "false")
    ^. us "\n"
  in
  SymbMap.fold f nmap (us "")

(* The main dead code elimination function 
   of flag utest is false, then utests are also removed
*)
let elimination t =
  (* Collect all lets and store a graph in 'nmap' and free variable in 'free' *)
  let nmap, free = collect_lets t in
  if !enable_debug_dead_code_info then (
    _symbmap := symbmap t ;
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
  remove_lets nmap t
