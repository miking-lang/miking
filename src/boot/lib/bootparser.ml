(*
 * Miking is licensed under the MIT license.
 * Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ustring.Op
open Ast
open Builtin
open Intrinsics

(* Terms *)
let idTmVar = 100

let idTmApp = 101

let idTmLam = 102

let idTmLet = 103

let idTmRecLets = 104

let idTmConst = 105

let idTmSeq = 106

let idTmRecord = 107

let idTmRecordUpdate = 108

let idTmType = 109

let idTmConDef = 110

let idTmConApp = 111

let idTmMatch = 112

let idTmUtest = 113

let idTmNever = 114

let idTmExt = 115

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

let idTyCon = 209

let idTyVar = 210

let idTyApp = 211

let idTyTensor = 212

let idTyAll = 213

(* Const literals *)
let idCBool = 300

let idCInt = 301

let idCFloat = 302

let idCChar = 303

let idCdprint = 304

let idCerror = 305

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

(* Info *)

let idInfo = 500

let idNoInfo = 501

let sym = Symb.gensym ()

let patNameToStr = function NameStr (x, _) -> x | NameWildcard -> us ""

let symbolizeEnvWithKeywords keywords =
  Mseq.Helpers.fold_left
    (fun env k ->
      if Ustring.length k > 0 && is_ascii_upper_alpha (Ustring.get k 0) then
        Symbolize.addsym
          (IdCon (sid_of_ustring k))
          (Intrinsics.Symb.gensym ())
          env
      else
        Symbolize.addsym
          (IdVar (sid_of_ustring k))
          (Intrinsics.Symb.gensym ())
          env )
    Symbolize.empty_sym_env keywords

let reportErrorAndExit err =
  let error_string = Ustring.to_utf8 (Parserutils.error_to_ustring err) in
  Printf.fprintf stderr "%s\n" error_string ;
  exit 1

let parseMExprString allow_free keywords str =
  try
    let keywords = Mseq.map Mseq.Helpers.to_ustring keywords in
    let allow_free_prev = !Symbolize.allow_free in
    Symbolize.allow_free := allow_free ;
    let r =
      PTreeTm
        ( str |> Intrinsics.Mseq.Helpers.to_ustring
        |> Parserutils.parse_mexpr_string
        |> Parserutils.raise_parse_error_on_non_unique_external_id
        |> Symbolize.symbolize
             (Symbolize.merge_sym_envs_pick_left builtin_name2sym
                (symbolizeEnvWithKeywords keywords) )
        |> Parserutils.raise_parse_error_on_partially_applied_external )
    in
    Symbolize.allow_free := allow_free_prev ;
    r
  with (Lexer.Lex_error _ | Msg.Error _ | Parsing.Parse_error) as e ->
    reportErrorAndExit e

let parseMCoreFile
    ( keep_utests
    , prune_external_utests
    , externals_exclude
    , warn
    , eliminate_deadcode
    , allow_free ) keywords filename =
  try
    let keywords = Mseq.map Mseq.Helpers.to_ustring keywords in
    let symKeywordsMap = symbolizeEnvWithKeywords keywords in
    let name2sym =
      Symbolize.merge_sym_envs_pick_left builtin_name2sym symKeywordsMap
    in
    let symKeywords =
      let getElements _ e acc = e :: acc in
      let elements = [] in
      let elements = SidMap.fold getElements symKeywordsMap.var elements in
      let elements = SidMap.fold getElements symKeywordsMap.con elements in
      let elements = SidMap.fold getElements symKeywordsMap.ty elements in
      let elements = SidMap.fold getElements symKeywordsMap.label elements in
      elements
    in
    let externals_exclude =
      Intrinsics.Mseq.Helpers.to_list
        (Mseq.map Intrinsics.Mseq.Helpers.to_ustring externals_exclude)
    in
    let deadcode_elimination =
      if eliminate_deadcode then
        Deadcode.elimination builtin_sym2term name2sym symKeywords
      else fun x -> x
    in
    let allow_free_prev = !Symbolize.allow_free in
    Symbolize.allow_free := allow_free ;
    let r =
      PTreeTm
        ( filename |> Intrinsics.Mseq.Helpers.to_ustring |> Ustring.to_utf8
        |> Utils.normalize_path |> Parserutils.parse_mcore_file
        |> Mlang.flatten |> Mlang.desugar_post_flatten
        |> Parserutils.raise_parse_error_on_non_unique_external_id
        |> Symbolize.symbolize name2sym
        |> Parserutils.raise_parse_error_on_partially_applied_external
        |> (fun t -> if keep_utests then t else Parserutils.remove_all_utests t)
        |> deadcode_elimination
        |> Parserutils.prune_external_utests
             ~enable:(keep_utests && prune_external_utests)
             ~externals_exclude ~warn
        |> deadcode_elimination )
    in
    Symbolize.allow_free := allow_free_prev ;
    r
  with (Lexer.Lex_error _ | Msg.Error _ | Parsing.Parse_error) as e ->
    reportErrorAndExit e

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
  | PTreeTm (TmVar (fi, x, _, frozen)) ->
      (idTmVar, [fi], [], [], [], [x], [(if frozen then 1 else 0)], [], [], [])
  | PTreeTm (TmApp (fi, t1, t2)) ->
      (idTmApp, [fi], [], [], [t1; t2], [], [], [], [], [])
  | PTreeTm (TmLam (fi, x, _, ty, t)) ->
      (idTmLam, [fi], [], [ty], [t], [x], [], [], [], [])
  | PTreeTm (TmLet (fi, x, _, ty, t1, t2)) ->
      (idTmLet, [fi], [], [ty], [t1; t2], [x], [], [], [], [])
  | PTreeTm (TmRecLets (fi, lst, t)) ->
      let fis = fi :: List.map (fun (fi, _, _, _, _) -> fi) lst in
      let len = List.length lst in
      let tys = List.map (fun (_, _, _, ty, _) -> ty) lst in
      let tms = List.map (fun (_, _, _, _, t) -> t) lst @ [t] in
      let strs = List.map (fun (_, s, _, _, _) -> s) lst in
      (idTmRecLets, fis, [len], tys, tms, strs, [], [], [], [])
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
  | PTreeTm (TmType (fi, x, params, ty, t)) ->
      let len = List.length params + 1 in
      (idTmType, [fi], [len], [ty], [t], x :: params, [], [], [], [])
  | PTreeTm (TmConDef (fi, x, _, ty, t)) ->
      (idTmConDef, [fi], [], [ty], [t], [x], [], [], [], [])
  | PTreeTm (TmConApp (fi, x, _, t)) ->
      (idTmConApp, [fi], [], [], [t], [x], [], [], [], [])
  | PTreeTm (TmMatch (fi, t1, p, t2, t3)) ->
      (idTmMatch, [fi], [], [], [t1; t2; t3], [], [], [], [], [p])
  | PTreeTm (TmUtest (fi, t1, t2, t4_op, t3)) -> (
    match t4_op with
    | Some t4 ->
        (idTmUtest, [fi], [4], [], [t1; t2; t3; t4], [], [], [], [], [])
    | None ->
        (idTmUtest, [fi], [3], [], [t1; t2; t3], [], [], [], [], []) )
  | PTreeTm (TmNever fi) ->
      (idTmNever, [fi], [], [], [], [], [], [], [], [])
  | PTreeTm (TmExt (fi, x, _, e, ty, t)) ->
      (idTmExt, [fi], [], [ty], [t], [x], [(if e then 1 else 0)], [], [], [])
  (* Types *)
  | PTreeTy (TyUnknown fi) ->
      (idTyUnknown, [fi], [], [], [], [], [], [], [], [])
  | PTreeTy (TyBool fi) ->
      (idTyBool, [fi], [], [], [], [], [], [], [], [])
  | PTreeTy (TyInt fi) ->
      (idTyInt, [fi], [], [], [], [], [], [], [], [])
  | PTreeTy (TyFloat fi) ->
      (idTyFloat, [fi], [], [], [], [], [], [], [], [])
  | PTreeTy (TyChar fi) ->
      (idTyChar, [fi], [], [], [], [], [], [], [], [])
  | PTreeTy (TyArrow (fi, ty1, ty2)) ->
      (idTyArrow, [fi], [], [ty1; ty2], [], [], [], [], [], [])
  | PTreeTy (TyAll (fi, var, ty)) ->
      (idTyAll, [fi], [], [ty], [], [var], [], [], [], [])
  | PTreeTy (TySeq (fi, ty)) ->
      (idTySeq, [fi], [], [ty], [], [], [], [], [], [])
  | PTreeTy (TyTensor (fi, ty)) ->
      (idTyTensor, [fi], [], [ty], [], [], [], [], [], [])
  | PTreeTy (TyRecord (fi, tymap)) ->
      let slst, tylst = List.split (Record.bindings tymap) in
      let len = List.length slst in
      (idTyRecord, [fi], [len], tylst, [], slst, [], [], [], [])
  | PTreeTy (TyVariant (fi, strs)) ->
      let len = List.length strs in
      (idTyVariant, [fi], [len], [], [], strs, [], [], [], [])
  | PTreeTy (TyCon (fi, x)) ->
      (idTyCon, [fi], [], [], [], [x], [], [], [], [])
  | PTreeTy (TyVar (fi, x)) ->
      (idTyVar, [fi], [], [], [], [x], [], [], [], [])
  | PTreeTy (TyApp (fi, ty1, ty2)) ->
      (idTyApp, [fi], [], [ty1; ty2], [], [], [], [], [], [])
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
  | PTreeConst Cdprint ->
      (idCdprint, [], [], [], [], [], [], [], [], [])
  | PTreeConst Cerror ->
      (idCerror, [], [], [], [], [], [], [], [], [])
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
  | PTreePat (PatAnd (fi, p1, p2)) ->
      (idPatAnd, [fi], [], [], [], [], [], [], [], [p1; p2])
  | PTreePat (PatOr (fi, p1, p2)) ->
      (idPatOr, [fi], [], [], [], [], [], [], [], [p1; p2])
  | PTreePat (PatNot (fi, p)) ->
      (idPatNot, [fi], [], [], [], [], [], [], [], [p])
  (* Info *)
  | PTreeInfo (Info (fn, r1, c1, r2, c2)) ->
      (idInfo, [], [], [], [], [fn], [r1; c1; r2; c2], [], [], [])
  | PTreeInfo NoInfo ->
      (idNoInfo, [], [], [], [], [], [], [], [], [])
  | _ ->
      failwith "The AST node is unknown"

let getId t =
  let id, _, _, _, _, _, _, _, _, _ = getData t in
  id

let getTerm t n =
  let _, _, _, _, lst, _, _, _, _, _ = getData t in
  PTreeTm (List.nth lst n)

let getType t n =
  let _, _, _, lst, _, _, _, _, _, _ = getData t in
  PTreeTy (List.nth lst n)

let getString t n =
  let _, _, _, _, _, lst, _, _, _, _ = getData t in
  List.nth lst n |> Intrinsics.Mseq.Helpers.of_ustring

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

let getInfo t n =
  let _, lst, _, _, _, _, _, _, _, _ = getData t in
  PTreeInfo (List.nth lst n)
