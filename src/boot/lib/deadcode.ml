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

let rec collect_vars (free : SymbSet.t) = function
  | TmVar (_, _, s) ->
      SymbSet.add s free
  | t ->
      sfold_tm_tm collect_vars free t

let collect_lets t =
  let rec work (nmap, free) = function
    | TmVar (_, _, s) ->
        (nmap, SymbSet.add s free)
    | TmLet (_, _, s, _, t1, t2) ->
        let nmap, free =
          match t1 with
          | TmLam (_, _, _, _, t) ->
              let vars = collect_vars SymbSet.empty t in
              (SymbMap.add s (vars, false) nmap, free)
          | body ->
              let nmap =
                SymbMap.add s (collect_vars SymbSet.empty t, true) nmap
              in
              work (nmap, free) body
        in
        work (nmap, free) t2
    (* TODO: add let rec *)
    | t ->
        sfold_tm_tm work (nmap, free) t
  in
  work (SymbMap.empty, SymbSet.empty) t

(*
let sfold_tm_tm (f : 'a -> tm -> 'a) (acc : 'a) = function
  | TmVar (_, _, _) ->
      acc
  | TmApp (_, t1, t2) ->
      f (f acc t1) t2
 *)

let elimination t =
  (* Printf.printf "%s\n" "**********" ; *)
  t
