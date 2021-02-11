(* 
 * Miking is licensed under the MIT license.
 * Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ustring.Op
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

(* Patterns *)
let idPatNamed = 400

let idPatSeqTot = 401

let idPatSeqEdge = 402

let idPatRecord = 403

let idPatCon = 404

let idPatInt = 405

let idPatChar = 406

let idPatBool = 407

let idPatAnd = 408

let idPatOr = 409

let idPatNot = 410

let sym = Symb.gensym ()

let patNameToStr = function NameStr (x, _) -> x | NameWildcard -> us ""

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
  10. List of patterns
*)

let getData = function
  (* Terms *)
  | PTreeTm (TmVar (fi, x, _)) ->
      (idTmVar, [fi], [], [], [], [x], [], [], [], [])
  | PTreeTm (TmLam (fi, x, _, ty, t)) ->
      (idTmLam, [fi], [], [ty], [t], [x], [], [], [], [])
  | PTreeTm (TmLet (fi, x, _, ty, t1, t2)) ->
      (idTmLet, [fi], [], [ty], [t1; t2], [x], [], [], [], [])
  | PTreeTm (TmType (fi, x, _, ty, t)) ->
      (idTmType, [fi], [], [ty], [t], [x], [], [], [], [])
  | PTreeTm (TmRecLets (fi, lst, t)) ->
      let fis = fi :: List.map (fun (fi, _, _, _, _) -> fi) lst in
      let len = List.length lst in
      let tys = List.map (fun (_, _, _, ty, _) -> ty) lst in
      let tms = List.map (fun (_, _, _, _, t) -> t) lst @ [t] in
      let strs = List.map (fun (_, s, _, _, _) -> s) lst in
      (idTmRecLets, fis, [len], tys, tms, strs, [], [], [], [])
  | PTreeTm (TmApp (fi, t1, t2)) ->
      (idTmApp, [fi], [], [], [t1; t2], [], [], [], [], [])
  | PTreeTm (TmConst (fi, c)) ->
      (idTmConst, [fi], [], [], [], [], [], [], [c], [])
  | PTreeTm (TmSeq (fi, ts)) ->
      let len = Mseq.length ts in
      let tms = Mseq.Helpers.to_list ts in
      (idTmSeq, [fi], [len], [], tms, [], [], [], [], [])
  | PTreeTm (TmRecord (fi, tmmap)) ->
      let slst, tlst = tmmap |> Record.bindings |> List.split in
      (idTmRecord, [fi], [List.length slst], [], tlst, slst, [], [], [], [])
  | PTreeTm (TmRecordUpdate (fi, t1, x, t2)) ->
      (idTmRecordUpdate, [fi], [], [], [t1; t2], [x], [], [], [], [])
  | PTreeTm (TmCondef (fi, x, _, ty, t)) ->
      (idTmCondef, [fi], [], [ty], [t], [x], [], [], [], [])
  | PTreeTm (TmConapp (fi, x, _, t)) ->
      (idTmConapp, [fi], [], [], [t], [x], [], [], [], [])
  | PTreeTm (TmMatch (fi, t1, p, t2, t3)) ->
      (idTmMatch, [fi], [], [], [t1; t2; t3], [], [], [], [], [p])
  (* Const *)
  | PTreeConst (CBool v) ->
      let i = if v then 1 else 0 in
      (idCBool, [], [], [], [], [], [i], [], [], [])
  | PTreeConst (CInt v) ->
      (idCInt, [], [], [], [], [], [v], [], [], [])
  | PTreeConst (CFloat v) ->
      (idCFloat, [], [], [], [], [], [], [v], [], [])
  | PTreeConst (CChar v) ->
      (idCChar, [], [], [], [], [], [v], [], [], [])
  (* Patterns *)
  | PTreePat (PatNamed (fi, x)) ->
      (idPatNamed, [fi], [], [], [], [patNameToStr x], [], [], [], [])
  | PTreePat (PatSeqTot (fi, pats)) ->
      let len = Mseq.length pats in
      let ps = Mseq.Helpers.to_list pats in
      (idPatSeqTot, [fi], [len], [], [], [], [], [], [], ps)
  | PTreePat (PatSeqEdge (fi, pats1, px, pats2)) ->
      let len1 = Mseq.length pats1 in
      let ps1 = Mseq.Helpers.to_list pats1 in
      let len2 = Mseq.length pats2 in
      let ps2 = Mseq.Helpers.to_list pats2 in
      let x = patNameToStr px in
      (idPatSeqEdge, [fi], [len1; len2], [], [], [x], [], [], [], ps1 @ ps2)
  | PTreePat (PatRecord (fi, pats)) ->
      let slst, plst = pats |> Record.bindings |> List.split in
      let len = List.length slst in
      (idPatRecord, [fi], [len], [], [], slst, [], [], [], plst)
  | PTreePat (PatCon (fi, x, _, p)) ->
      (idPatCon, [fi], [], [], [], [x], [], [], [], [p])
  | PTreePat (PatInt (fi, v)) ->
      (idPatInt, [fi], [], [], [], [], [v], [], [], [])
  | PTreePat (PatChar (fi, v)) ->
      (idPatChar, [fi], [], [], [], [], [v], [], [], [])
  | PTreePat (PatBool (fi, v)) ->
      let b = if v then 1 else 0 in
      (idPatBool, [fi], [], [], [], [], [b], [], [], [])
  (*
  (* Int pattern *)
  | PatInt of info * int
  (* Char pattern *)
  | PatChar of info * int
  (* Boolean pattern *)
  | PatBool of info * bool
  (* And pattern *)
  | PatAnd of info * pat * pat
  (* Or pattern *)
  | PatOr of info * pat * pat
  (* Not pattern *)
  | PatNot of info * pat
 *)
  | _ ->
      failwith "TODO2"

let getId t =
  let id, _, _, _, _, _, _, _, _, _ = getData t in
  id

let getTerm t n =
  let _, _, _, _, lst, _, _, _, _, _ = getData t in
  PTreeTm (List.nth lst n)

let getString t n =
  let _, _, _, _, _, lst, _, _, _, _ = getData t in
  List.nth lst n

let getInt t n =
  let _, _, _, _, _, _, lst, _, _, _ = getData t in
  List.nth lst n

let getFloat t n =
  let _, _, _, _, _, _, _, lst, _, _ = getData t in
  List.nth lst n

let getListLength t n =
  let _, _, lst, _, _, _, _, _, _, _ = getData t in
  List.nth lst n

let getConst t n =
  let _, _, _, _, _, _, _, _, lst, _ = getData t in
  PTreeConst (List.nth lst n)

let getPat t n =
  let _, _, _, _, _, _, _, _, _, lst = getData t in
  PTreePat (List.nth lst n)
