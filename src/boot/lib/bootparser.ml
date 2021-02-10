(* 
 * Miking is licensed under the MIT license.
 * Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Intrinsics

(* Terms *)
let idTmVar = 100

let idTmLam = 101

let idTmLet = 102

let idTmType = 103

let idTmRecLets = 104

let idTmApp = 105

let idTmConst = 106

let idTmSeq = 107

let idTmRecord = 108

let idTmRecordUpdate = 109

let idTmCondef = 110

let idTmConapp = 111

let idTmMatch = 112

let idTmUse = 113

let idTmUtest = 114

let idTmNever = 115

let idTmClos = 116

let idTmFix = 117

(* Types *)
let idTyUnknown = 200

let idTyBool = 201

let idTyInt = 202

let idTyFloat = 203

let idTyChar = 204

let idTyArrow = 205

let idTySeq = 206

let idTyRecord = 207

let idTyVariant = 208

let idTyVar = 209

let idTyApp = 210

(* Const literals *)
let idCBool = 300

let idCInt = 301

let idCFloat = 302

let idCChar = 303

let sym = Symb.gensym ()

let parseMExprString str = Parserutils.parse_mexpr_string str

(* Returns a tuple with the following elements
   1. ID field 
   2. Info field
   3. List of list lengths
   4. List of types
   5. List of terms
   6. List of strings
   7. List of integers
   8. List of floating-point numbers
   9. List of const
*)

let getData = function
  (* Terms *)
  | PTreeTm (TmVar (fi, x, _)) ->
      (idTmVar, [fi], [], [], [], [x], [], [], [])
  | PTreeTm (TmLam (fi, x, _, ty, t)) ->
      (idTmLam, [fi], [], [ty], [t], [x], [], [], [])
  | PTreeTm (TmLet (fi, x, _, ty, t1, t2)) ->
      (idTmLet, [fi], [], [ty], [t1; t2], [x], [], [], [])
  | PTreeTm (TmType (fi, x, _, ty, t)) ->
      (idTmType, [fi], [], [ty], [t], [x], [], [], [])
  | PTreeTm (TmRecLets (fi, lst, t)) ->
      let fis = fi :: List.map (fun (fi, _, _, _, _) -> fi) lst in
      let len = List.length lst in
      let tys = List.map (fun (_, _, _, ty, _) -> ty) lst in
      let tms = List.map (fun (_, _, _, _, t) -> t) lst @ [t] in
      let strs = List.map (fun (_, s, _, _, _) -> s) lst in
      (idTmRecLets, fis, [len], tys, tms, strs, [], [], [])
  | PTreeTm (TmApp (fi, t1, t2)) ->
      (idTmApp, [fi], [], [], [t1; t2], [], [], [], [])
  | PTreeTm (TmConst (fi, c)) ->
      (idTmConst, [fi], [], [], [], [], [], [], [c])
  | PTreeTm (TmSeq (fi, ts)) ->
      let len = Mseq.length ts in
      let tms = Mseq.Helpers.to_list ts in
      (idTmSeq, [fi], [len], [], tms, [], [], [], [])
  | PTreeTm (TmRecord (fi, tmmap)) ->
      let slst, tlst = tmmap |> Record.bindings |> List.split in
      (idTmRecord, [fi], [List.length slst], [], tlst, slst, [], [], [])
  (* Const *)
  | PTreeConst (CBool v) ->
      let i = if v then 1 else 0 in
      (idCBool, [], [], [], [], [], [i], [], [])
  | PTreeConst (CInt v) ->
      (idCInt, [], [], [], [], [], [v], [], [])
  | PTreeConst (CFloat v) ->
      (idCFloat, [], [], [], [], [], [], [v], [])
  | PTreeConst (CChar v) ->
      (idCChar, [], [], [], [], [], [v], [], [])
  | _ ->
      failwith "TODO"

let getId t =
  let id, _, _, _, _, _, _, _, _ = getData t in
  id

let getTerm t n =
  let _, _, _, _, lst, _, _, _, _ = getData t in
  PTreeTm (List.nth lst n)

let getString t n =
  let _, _, _, _, _, lst, _, _, _ = getData t in
  List.nth lst n

let getInt t n =
  let _, _, _, _, _, _, lst, _, _ = getData t in
  List.nth lst n

let getFloat t n =
  let _, _, _, _, _, _, _, lst, _ = getData t in
  List.nth lst n

let getListLength t n =
  let _, _, lst, _, _, _, _, _, _ = getData t in
  List.nth lst n

let getConst t n =
  let _, _, _, _, _, _, _, _, lst = getData t in
  PTreeConst (List.nth lst n)
