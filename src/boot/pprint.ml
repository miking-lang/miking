
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ast
open Ustring.Op
open Printf


(* Debug options *)
let enable_debug_debruijn_print = true


(* Print out a variable, either in debug mode or not *)
let varDebugPrint x n =
  if enable_debug_debruijn_print
  then x ^. us(sprintf "'%d" n) else x



(* Pretty printing for precedence *)
let left inside = if inside then us"(" else us""
let right inside = if inside then us")" else us""


(* Pretty print "true" or "false" *)
let usbool x = us (if x then "true" else "false")


(* Pretty print constants *)
let rec pprint_const c =
  match c with
  (* MCore Intrinsic Booleans *)
  | CBool(b) -> if b then us"true" else us"false"
  | Cnot -> us"not"
  | Cand(None) -> us"and"
  | Cand(Some(v)) -> us"and(" ^. usbool v ^. us")"
  | Cor(None) -> us"or"
  | Cor(Some(v)) -> us"or(" ^. usbool v ^. us")"
  (* MCore Intrinsic Integers *)
  | CInt(v) -> us(sprintf "%d" v)
  | Caddi(None) -> us"addi"
  | Caddi(Some(v)) -> us(sprintf "addi(%d)" v)
  | Csubi(None) -> us"subi"
  | Csubi(Some(v)) -> us(sprintf "subi(%d)" v)
  | Cmuli(None) -> us"muli"
  | Cmuli(Some(v)) -> us(sprintf "muli(%d)" v)
  | Cdivi(None) -> us"divi"
  | Cdivi(Some(v)) -> us(sprintf "divi(%d)" v)
  | Cmodi(None) -> us"modi"
  | Cmodi(Some(v)) -> us(sprintf "modi(%d)" v)
  | Cnegi -> us"negi"
  | Clti(None) -> us"lti"
  | Clti(Some(v)) -> us(sprintf "lti(%d)" v)
  | Cleqi(None) -> us"leqi"
  | Cleqi(Some(v)) -> us(sprintf "leqi(%d)" v)
  | Cgti(None) -> us"gti"
  | Cgti(Some(v)) -> us(sprintf "gti(%d)" v)
  | Cgeqi(None) -> us"geqi"
  | Cgeqi(Some(v)) -> us(sprintf "geqi(%d)" v)
  | Ceqi(None) -> us"eqi"
  | Ceqi(Some(v)) -> us(sprintf "eqi(%d)" v)
  | Cneqi(None) -> us"neqi"
  | Cneqi(Some(v)) -> us(sprintf "neqi(%d)" v)
  | Cslli(None) -> us"slli"
  | Cslli(Some(v)) -> us(sprintf "slli(%d)" v)
  | Csrli(None) -> us"srli"
  | Csrli(Some(v)) -> us(sprintf "srli(%d)" v)
  | Csrai(None) -> us"srai"
  | Csrai(Some(v)) -> us(sprintf "srai(%d)" v)
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(v) -> us(sprintf "%f" v)
  | Caddf(None) -> us"addf"
  | Caddf(Some(v)) -> us(sprintf "addf(%f)" v)
  | Csubf(None) -> us"subf"
  | Csubf(Some(v)) -> us(sprintf "subf(%f)" v)
  | Cmulf(None) -> us"mulf"
  | Cmulf(Some(v)) -> us(sprintf "mulf(%f)" v)
  | Cdivf(None) -> us"divf"
  | Cdivf(Some(v)) -> us(sprintf "divf(%f)" v)
  | Cnegf -> us"negf"
  (* MCore debug and stdio intrinsics *)
  | CDPrint -> us"dprint"

(* Pretty print a term. *)
and pprint t =
  let rec ppt inside t =
  match t with
  | TmVar(_,x,n) -> varDebugPrint x n
  | TmLam(_,x,ty,t1) -> left inside ^.
      us"lam " ^. x ^. us":" ^. pprint_ty ty ^. us". " ^. ppt false t1 ^. right inside
  | TmClos(_,x,_,t,_) -> left inside ^. us"clos " ^. x ^. us". " ^.
       ppt false t ^. right inside
  | TmApp(_,t1,t2) ->
       left inside ^. ppt true t1  ^. us" " ^. ppt true t2 ^. right inside
  | TmConst(_,c) -> pprint_const c
  | TmFix(_) -> us"fix"
  | TmChar(_,c) -> us"'" ^. list2ustring [c] ^. us"'"
  | TmUtest(_,t1,t2,_) -> us"utest " ^. ppt false t1  ^. us" " ^. ppt false t2
  | TmNop -> us"Nop"
  in ppt false t

(* Pretty prints the environment *)
and pprint_env env =
  us"[" ^. (List.mapi (fun i t -> us(sprintf " %d -> " i) ^. pprint t) env
            |> Ustring.concat (us",")) ^. us"]"


and pprint_ty ty =
  let ppt ty =
  match ty with
  | TyDyn -> us"Dyn"
  in
    ppt ty
