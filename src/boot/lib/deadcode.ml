open Ast
open Intrinsics

module SymbOrd = struct
  type t = Symb.t

  let compare = Symb.compare
end

module SymbSet = Set.Make (SymbOrd)
module SymbMap = Map.Make (SymbOrd)

(*
let pbool s b = Printf.printf "%s: %s\n" s (if b then "true" else "false") 

let testen =
  let s1 = Symb.gensym () in
  let s2 = Symb.gensym () in
  let s3 = s2 in
  pbool "s1 = s2" (s1 = s2) ;
  pbool "s2 = s3" (s2 = s3) ;
  let a = SymbSet.empty in
  let b = SymbSet.add s1 a in
  pbool "s1 set mem" (SymbSet.mem s1 b) ;
  pbool "s2 set mem" (SymbSet.mem s2 b) ;
  let m1 = SymbMap.empty in
  let m2 = SymbMap.add s2 a m1 in
  pbool "s1 map mem" (SymbMap.mem s1 m2) ;
  pbool "s2 map mem" (SymbMap.mem s2 m2) ;
  Printf.printf ""
 *)

(* Help function that collects all variables in a term *)
let rec collect_vars (free : SymbSet.t) = function
  | TmVar (_, _, s) ->
      SymbSet.add s free
  | t ->
      sfold_tm_tm collect_vars free t

(* Collect all mappings for lets (mapping symbol name of the let
   to the set of variables in the let body). It also collects
   all variables that are free, not under a lambda in a let *)
let collect_lets t =
  let rec work (nmap, free) = function
    | TmVar (_, _, s) ->
        (nmap, SymbSet.add s free)
    | TmLet (_, _, s, _, t1, t2) ->
        let nmap, free =
          match t1 with
          | TmLam (_, _, _, _, tlam) ->
              let vars = collect_vars SymbSet.empty tlam in
              (SymbMap.add s (vars, false) nmap, free)
          | body ->
              let vars = collect_vars SymbSet.empty body in 
              (SymbMap.add s (vars, true) nmap, SymbSet.union vars free)
               (* TODO: handle lets without side effects *)
        in
        work (nmap, free) t2
    (* TODO: add let rec *)
    | t ->
        sfold_tm_tm work (nmap, free) t
  in
  work (SymbMap.empty, SymbSet.empty) t

(* Returns a new namp, where it is marked with true everywhere we have
   a let that is used. Use depth-first search (DFS) in the graph with
   color marking.  *)
let mark_used_lets nmap free =
  let rec dfs s (visited, nmap) =
    if SymbSet.mem s visited then (visited, nmap)
    else
      let visited = SymbSet.add s visited in
      let (symset, _) = SymbMap.find s nmap in
      let nmap = SymbMap.add s (symset, true) nmap in
      SymbSet.fold dfs symset (visited, nmap) 
  in
  SymbSet.fold dfs free (SymbSet.empty, nmap) |> snd
  

(* Removes all lets which have not been marked as used *)
let rec remove_lets nmap = function
  | TmLet (fi, x, s, ty, t1, t2) ->
     (* Is the let marked as used? *)
     if SymbMap.find s nmap |> snd then
       TmLet (fi, x, s, ty, t1, remove_lets nmap t2)
     else
       remove_lets nmap t2
  | t -> smap_tm_tm (remove_lets nmap) t
  
 

let elimination t =
  
  (* Printf.printf "%s\n" "**********" ; *)
  t
