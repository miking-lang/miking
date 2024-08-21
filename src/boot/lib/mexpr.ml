(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ustring.Op
open Msg
open Ast
open Pprint
open Printf
open Intrinsics
open Builtin

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

let idTmUse = 116

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

let idTyUse = 214

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

(* Error *)

let idError = 600

(* MLang *)
let idProgram = 700

let idDeclLang = 701

let idDeclSyn = 702

let idDeclSem = 703

let idDeclLet = 704

let idDeclType = 705

let idDeclRecLets = 706

let idDeclConDef = 707

let idDeclUtest = 708

let idDeclExt = 709

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
   11. List of tops
*)

let getData = function
  (* Terms *)
  | PTreeTm (TmVar (fi, x, _, _, frozen)) ->
      ( idTmVar
      , [fi]
      , []
      , []
      , []
      , [x]
      , [(if frozen then 1 else 0)]
      , []
      , []
      , []
      , []
      , [] )
  | PTreeTm (TmApp (fi, t1, t2)) ->
      (idTmApp, [fi], [], [], [t1; t2], [], [], [], [], [], [], [])
  | PTreeTm (TmLam (fi, x, _, _, ty, t)) ->
      (idTmLam, [fi], [], [ty], [t], [x], [], [], [], [], [], [])
  | PTreeTm (TmLet (fi, x, _, ty, t1, t2)) ->
      (idTmLet, [fi], [], [ty], [t1; t2], [x], [], [], [], [], [], [])
  | PTreeTm (TmRecLets (fi, lst, t)) ->
      let fis = fi :: List.map (fun (fi, _, _, _, _) -> fi) lst in
      let len = List.length lst in
      let tys = List.map (fun (_, _, _, ty, _) -> ty) lst in
      let tms = List.map (fun (_, _, _, _, t) -> t) lst @ [t] in
      let strs = List.map (fun (_, s, _, _, _) -> s) lst in
      (idTmRecLets, fis, [len], tys, tms, strs, [], [], [], [], [], [])
  | PTreeTm (TmConst (fi, c)) ->
      (idTmConst, [fi], [], [], [], [], [], [], [c], [], [], [])
  | PTreeTm (TmUse (fi, str, tm)) ->
      (idTmUse, [fi], [], [], [tm], [str], [], [], [], [], [], [])
  | PTreeTm (TmSeq (fi, ts)) ->
      let len = Mseq.length ts in
      let tms = Mseq.Helpers.to_list ts in
      (idTmSeq, [fi], [len], [], tms, [], [], [], [], [], [], [])
  | PTreeTm (TmRecord (fi, tmmap)) ->
      let slst, tlst = tmmap |> Record.bindings |> List.split in
      ( idTmRecord
      , [fi]
      , [List.length slst]
      , []
      , tlst
      , slst
      , []
      , []
      , []
      , []
      , []
      , [] )
  | PTreeTm (TmRecordUpdate (fi, t1, x, t2)) ->
      (idTmRecordUpdate, [fi], [], [], [t1; t2], [x], [], [], [], [], [], [])
  | PTreeTm (TmType (fi, x, params, ty, t)) ->
      let len = List.length params + 1 in
      (idTmType, [fi], [len], [ty], [t], x :: params, [], [], [], [], [], [])
  | PTreeTm (TmConDef (fi, x, _, ty, t)) ->
      (idTmConDef, [fi], [], [ty], [t], [x], [], [], [], [], [], [])
  | PTreeTm (TmConApp (fi, x, _, t)) ->
      (idTmConApp, [fi], [], [], [t], [x], [], [], [], [], [], [])
  | PTreeTm (TmMatch (fi, t1, p, t2, t3)) ->
      (idTmMatch, [fi], [], [], [t1; t2; t3], [], [], [], [], [p], [], [])
  | PTreeTm (TmUtest (fi, t1, t2, t4_op, t5_op, t3)) -> (
    match (t4_op, t5_op) with
    | None, None ->
        (idTmUtest, [fi], [3], [], [t1; t2; t3], [], [], [], [], [], [], [])
    | Some t4, None ->
        (idTmUtest, [fi], [4], [], [t1; t2; t3; t4], [], [], [], [], [], [], [])
    | Some t4, Some t5 ->
        ( idTmUtest
        , [fi]
        , [5]
        , []
        , [t1; t2; t3; t4; t5]
        , []
        , []
        , []
        , []
        , []
        , []
        , [] )
    | _, _ ->
        failwith "bootparser getData undefined" )
  | PTreeTm (TmNever fi) ->
      (idTmNever, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTm (TmExt (fi, x, _, e, ty, t)) ->
      ( idTmExt
      , [fi]
      , []
      , [ty]
      , [t]
      , [x]
      , [(if e then 1 else 0)]
      , []
      , []
      , []
      , []
      , [] )
  (* Types *)
  | PTreeTy (TyUnknown fi) ->
      (idTyUnknown, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTy (TyBool fi) ->
      (idTyBool, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTy (TyInt fi) ->
      (idTyInt, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTy (TyFloat fi) ->
      (idTyFloat, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTy (TyChar fi) ->
      (idTyChar, [fi], [], [], [], [], [], [], [], [], [], [])
  | PTreeTy (TyArrow (fi, ty1, ty2)) ->
      (idTyArrow, [fi], [], [ty1; ty2], [], [], [], [], [], [], [], [])
  | PTreeTy (TyAll (fi, var, None, ty)) ->
      (idTyAll, [fi], [], [ty], [], [var], [0], [], [], [], [], [])
  | PTreeTy (TyAll (fi, var, Some data, ty)) ->
      let klens =
        List.concat_map
          (fun (_, lower, upper) ->
            let llen = List.length lower in
            Option.fold ~none:[llen; -1]
              ~some:(fun u ->
                let ulen = List.length u in
                [llen + ulen; llen] )
              upper )
          data
      in
      let ks =
        List.concat_map
          (fun (t, lower, upper) ->
            t :: (lower @ Option.value ~default:[] upper) )
          data
      in
      let dlen = List.length klens + 1 in
      ( idTyAll
      , [fi]
      , dlen :: klens
      , [ty]
      , []
      , var :: ks
      , [1]
      , []
      , []
      , []
      , []
      , [] )
  | PTreeTy (TySeq (fi, ty)) ->
      (idTySeq, [fi], [], [ty], [], [], [], [], [], [], [], [])
  | PTreeTy (TyTensor (fi, ty)) ->
      (idTyTensor, [fi], [], [ty], [], [], [], [], [], [], [], [])
  | PTreeTy (TyRecord (fi, tymap)) ->
      let slst, tylst = List.split (Record.bindings tymap) in
      let len = List.length slst in
      (idTyRecord, [fi], [len], tylst, [], slst, [], [], [], [], [], [])
  | PTreeTy (TyVariant (fi, strs)) ->
      let len = List.length strs in
      (idTyVariant, [fi], [len], [], [], strs, [], [], [], [], [], [])
  | PTreeTy (TyCon (fi, x, None)) ->
      (idTyCon, [fi], [], [], [], [x], [0], [], [], [], [], [])
  | PTreeTy (TyCon (fi, x, Some cons)) ->
      let typ, strs =
        match cons with
        | DCons cs ->
            (1, cs)
        | DNCons cs ->
            (2, cs)
        | DVar v ->
            (3, [v])
      in
      let len = List.length strs + 1 in
      (idTyCon, [fi], [len], [], [], x :: strs, [typ], [], [], [], [], [])
  | PTreeTy (TyVar (fi, x)) ->
      (idTyVar, [fi], [], [], [], [x], [], [], [], [], [], [])
  | PTreeTy (TyApp (fi, ty1, ty2)) ->
      (idTyApp, [fi], [], [ty1; ty2], [], [], [], [], [], [], [], [])
  | PTreeTy (TyUse (fi, ident, ty)) ->
      (idTyUse, [fi], [], [ty], [], [ident], [], [], [], [], [], [])
  (* Const *)
  | PTreeConst (CBool v) ->
      let i = if v then 1 else 0 in
      (idCBool, [], [], [], [], [], [i], [], [], [], [], [])
  | PTreeConst (CInt v) ->
      (idCInt, [], [], [], [], [], [v], [], [], [], [], [])
  | PTreeConst (CFloat v) ->
      (idCFloat, [], [], [], [], [], [], [v], [], [], [], [])
  | PTreeConst (CChar v) ->
      (idCChar, [], [], [], [], [], [v], [], [], [], [], [])
  | PTreeConst Cdprint ->
      (idCdprint, [], [], [], [], [], [], [], [], [], [], [])
  | PTreeConst Cerror ->
      (idCerror, [], [], [], [], [], [], [], [], [], [], [])
  (* Patterns *)
  | PTreePat (PatNamed (fi, x)) ->
      (idPatNamed, [fi], [], [], [], [patNameToStr x], [], [], [], [], [], [])
  | PTreePat (PatSeqTot (fi, pats)) ->
      let len = Mseq.length pats in
      let ps = Mseq.Helpers.to_list pats in
      (idPatSeqTot, [fi], [len], [], [], [], [], [], [], ps, [], [])
  | PTreePat (PatSeqEdge (fi, pats1, px, pats2)) ->
      let len1 = Mseq.length pats1 in
      let ps1 = Mseq.Helpers.to_list pats1 in
      let len2 = Mseq.length pats2 in
      let ps2 = Mseq.Helpers.to_list pats2 in
      let x = patNameToStr px in
      ( idPatSeqEdge
      , [fi]
      , [len1; len2]
      , []
      , []
      , [x]
      , []
      , []
      , []
      , ps1 @ ps2
      , []
      , [] )
  | PTreePat (PatRecord (fi, pats)) ->
      let slst, plst = pats |> Record.bindings |> List.split in
      let len = List.length slst in
      (idPatRecord, [fi], [len], [], [], slst, [], [], [], plst, [], [])
  | PTreePat (PatCon (fi, x, _, p)) ->
      (idPatCon, [fi], [], [], [], [x], [], [], [], [p], [], [])
  | PTreePat (PatInt (fi, v)) ->
      (idPatInt, [fi], [], [], [], [], [v], [], [], [], [], [])
  | PTreePat (PatChar (fi, v)) ->
      (idPatChar, [fi], [], [], [], [], [v], [], [], [], [], [])
  | PTreePat (PatBool (fi, v)) ->
      let b = if v then 1 else 0 in
      (idPatBool, [fi], [], [], [], [], [b], [], [], [], [], [])
  | PTreePat (PatAnd (fi, p1, p2)) ->
      (idPatAnd, [fi], [], [], [], [], [], [], [], [p1; p2], [], [])
  | PTreePat (PatOr (fi, p1, p2)) ->
      (idPatOr, [fi], [], [], [], [], [], [], [], [p1; p2], [], [])
  | PTreePat (PatNot (fi, p)) ->
      (idPatNot, [fi], [], [], [], [], [], [], [], [p], [], [])
  (* MLang *)
  | PTreeProgram (Program (includes, tops, expr)) ->
      let includeStrings =
        List.map (fun incl -> match incl with Include (_, s) -> s) includes
      in
      let includeInfos =
        List.map (fun incl -> match incl with Include (i, _) -> i) includes
      in
      ( idProgram
      , includeInfos
      , [List.length includes; List.length tops]
      , []
      , [expr]
      , includeStrings
      , []
      , []
      , []
      , []
      , tops
      , [] )
  (* Info *)
  | PTreeInfo (Info (fn, r1, c1, r2, c2)) ->
      (idInfo, [], [], [], [], [fn], [r1; c1; r2; c2], [], [], [], [], [])
  | PTreeInfo NoInfo ->
      (idNoInfo, [], [], [], [], [], [], [], [], [], [], [])
  (* Error *)
  | PTreeError es ->
      let fis, msgs = List.split es in
      (idError, fis, [List.length es], [], [], msgs, [], [], [], [], [], [])
  | PTreeTop (TopLet (Let (fi, x, ty, tm))) ->
      (idDeclLet, [fi], [], [ty], [tm], [x], [], [], [], [], [], [])
  | PTreeTop (TopType (Type (fi, x, params, ty))) ->
      ( idDeclType
      , [fi]
      , [List.length params]
      , [ty]
      , []
      , x :: params
      , []
      , []
      , []
      , []
      , []
      , [] )
  | PTreeTop (TopRecLet (RecLet (fi, lst))) ->
      let len = List.length lst in
      let fis = fi :: List.map (fun (fi, _, _, _) -> fi) lst in
      let strs = List.map (fun (_, s, _, _) -> s) lst in
      let tys = List.map (fun (_, _, ty, _) -> ty) lst in
      let tms = List.map (fun (_, _, _, t) -> t) lst in
      (idDeclRecLets, fis, [len], tys, tms, strs, [], [], [], [], [], [])
  | PTreeTop (TopCon (Con (fi, str, ty))) ->
      (idDeclConDef, [fi], [], [ty], [], [str], [], [], [], [], [], [])
  | PTreeTop (TopUtest (Utest (fi, tm1, tm2, tmUsing, tmOnFail))) -> (
    match (tmUsing, tmOnFail) with
    | None, None ->
        (idDeclUtest, [fi], [2], [], [tm1; tm2], [], [], [], [], [], [], [])
    | Some tmUsing, None ->
        ( idDeclUtest
        , [fi]
        , [3]
        , []
        , [tm1; tm2; tmUsing]
        , []
        , []
        , []
        , []
        , []
        , []
        , [] )
    | Some tmUsing, Some tmOnFail ->
        ( idDeclUtest
        , [fi]
        , [4]
        , []
        , [tm1; tm2; tmUsing; tmOnFail]
        , []
        , []
        , []
        , []
        , []
        , []
        , [] )
    | _, _ ->
        failwith "bootparser getData undefined" )
  | PTreeTop (TopExt (Ext (fi, str, effect, ty))) ->
      ( idDeclExt
      , [fi]
      , []
      , [ty]
      , []
      , [str]
      , [(if effect then 1 else 0)]
      , []
      , []
      , []
      , []
      , [] )
  (* TODO(voorberg, 03-05-2024): Add support for 'with' extensions *)
  | PTreeTop (TopLang (Lang (fi, ident, includes, _, decls))) ->
      ( idDeclLang
      , [fi]
      , [List.length includes; List.length decls]
      , []
      , []
      , ident :: includes
      , []
      , []
      , []
      , []
      , []
      , decls )
  | PTreeDecl (Data (fi, ident, nParams, decls)) ->
      let lst =
        List.map
          (fun x ->
            match x with CDecl (fi, params, con, ty) -> (fi, params, con, ty)
            )
          decls
      in
      let allStr = List.map (fun (_, _, con, _) -> con) lst in
      let fis = fi :: List.map (fun (fi, _, _, _) -> fi) lst in
      let tys = List.map (fun (_, _, _, ty) -> ty) lst in
      let tyParams =
        if List.length lst = 0 then []
        else List.hd (List.map (fun (_, params, _, _) -> params) lst)
      in
      ( idDeclSyn
      , fis
      , [List.length decls; nParams]
      , tys
      , []
      , ident :: List.concat [allStr; tyParams]
      , []
      , []
      , []
      , []
      , []
      , [] )
  | PTreeDecl (Inter (fi, ident, ty, paramListOpt, cases)) -> (
    match paramListOpt with
    | Some paramList ->
        let argIdents =
          List.map (fun x -> match x with Param (_, s, _) -> s) paramList
        in
        let argTys =
          List.map (fun x -> match x with Param (_, _, ty) -> ty) paramList
        in
        let pats = List.map fst cases in
        let tms = List.map snd cases in
        ( idDeclSem
        , [fi]
        , [List.length cases; List.length paramList]
        , ty :: argTys
        , tms
        , ident :: argIdents
        , []
        , []
        , []
        , pats
        , []
        , [] )
    | None ->
        let pats = List.map fst cases in
        let tms = List.map snd cases in
        (* NOTE(15-05-2024, voorberg): If the amount of parameters has not
           been specified by this definition, we send -1. *)
        ( idDeclSem
        , [fi]
        , [List.length cases; -1]
        , [ty]
        , tms
        , [ident]
        , []
        , []
        , []
        , pats
        , []
        , [] ) )
  | PTreeDecl (Alias (fi, ident, params, ty)) ->
      ( idDeclType
      , [fi]
      , [List.length params]
      , [ty]
      , []
      , ident :: params
      , []
      , []
      , []
      , []
      , []
      , [] )
  | _ ->
      failwith "The AST node is unknown"

let getId t =
  let id, _, _, _, _, _, _, _, _, _, _, _ = getData t in
  id

let getTerm t n =
  let _, _, _, _, lst, _, _, _, _, _, _, _ = getData t in
  PTreeTm (List.nth lst n)

let getType t n =
  let _, _, _, lst, _, _, _, _, _, _, _, _ = getData t in
  PTreeTy (List.nth lst n)

let getString t n =
  let _, _, _, _, _, lst, _, _, _, _, _, _ = getData t in
  List.nth lst n |> Intrinsics.Mseq.Helpers.of_ustring

let getInt t n =
  let _, _, _, _, _, _, lst, _, _, _, _, _ = getData t in
  List.nth lst n

let getFloat t n =
  let _, _, _, _, _, _, _, lst, _, _, _, _ = getData t in
  List.nth lst n

let getListLength t n =
  let _, _, lst, _, _, _, _, _, _, _, _, _ = getData t in
  List.nth lst n

let getConst t n =
  let _, _, _, _, _, _, _, _, lst, _, _, _ = getData t in
  PTreeConst (List.nth lst n)

let getPat t n =
  let _, _, _, _, _, _, _, _, _, lst, _, _ = getData t in
  PTreePat (List.nth lst n)

let getTop t n =
  let _, _, _, _, _, _, _, _, _, _, lst, _ = getData t in
  PTreeTop (List.nth lst n)

let getDecl t n =
  let _, _, _, _, _, _, _, _, _, _, _, lst = getData t in
  PTreeDecl (List.nth lst n)

let getInfo t n =
  let _, lst, _, _, _, _, _, _, _, _, _, _ = getData t in
  PTreeInfo (List.nth lst n)

(* This function determines how to print program output.
   It's used to redirect standard output of a program,
   for instance by the Jupyter kernel *)
let program_output = ref uprint_string

(* Returns the number of expected arguments of a constant *)
let arity = function
  | CunsafeCoerce ->
      1
  (* MCore intrinsics: Booleans *)
  | CBool _ ->
      0
  (* MCore intrinsics: Integers *)
  | CInt _ ->
      0
  | Caddi None ->
      2
  | Caddi (Some _) ->
      1
  | Csubi None ->
      2
  | Csubi (Some _) ->
      1
  | Cmuli None ->
      2
  | Cmuli (Some _) ->
      1
  | Cdivi None ->
      2
  | Cdivi (Some _) ->
      1
  | Cmodi None ->
      2
  | Cmodi (Some _) ->
      1
  | Cnegi ->
      1
  | Clti None ->
      2
  | Clti (Some _) ->
      1
  | Cleqi None ->
      2
  | Cleqi (Some _) ->
      1
  | Cgti None ->
      2
  | Cgti (Some _) ->
      1
  | Cgeqi None ->
      2
  | Cgeqi (Some _) ->
      1
  | Ceqi None ->
      2
  | Ceqi (Some _) ->
      1
  | Cneqi None ->
      2
  | Cneqi (Some _) ->
      1
  | Cslli None ->
      2
  | Cslli (Some _) ->
      1
  | Csrli None ->
      2
  | Csrli (Some _) ->
      1
  | Csrai None ->
      2
  | Csrai (Some _) ->
      1
  | Carity ->
      1
  (* MCore intrinsics: Floating-point numbers *)
  | CFloat _ ->
      0
  | Caddf None ->
      2
  | Caddf (Some _) ->
      1
  | Csubf None ->
      2
  | Csubf (Some _) ->
      1
  | Cmulf None ->
      2
  | Cmulf (Some _) ->
      1
  | Cdivf None ->
      2
  | Cdivf (Some _) ->
      1
  | Cnegf ->
      1
  | Cltf None ->
      2
  | Cltf (Some _) ->
      1
  | Cleqf None ->
      2
  | Cleqf (Some _) ->
      1
  | Cgtf None ->
      2
  | Cgtf (Some _) ->
      1
  | Cgeqf None ->
      2
  | Cgeqf (Some _) ->
      1
  | Ceqf None ->
      2
  | Ceqf (Some _) ->
      1
  | Cneqf None ->
      2
  | Cneqf (Some _) ->
      1
  | Cfloorfi ->
      1
  | Cceilfi ->
      1
  | Croundfi ->
      1
  | Cint2float ->
      1
  | CstringIsFloat ->
      1
  | Cstring2float ->
      1
  | Cfloat2string ->
      1
  (* MCore intrinsics: Characters *)
  | CChar _ ->
      0
  | Ceqc _ ->
      2
  | Cchar2int ->
      1
  | Cint2char ->
      1
  (* MCore intrinsic: sequences *)
  | Ccreate None ->
      2
  | Ccreate (Some _) ->
      1
  | CcreateList None ->
      2
  | CcreateList (Some _) ->
      1
  | CcreateRope None ->
      2
  | CcreateRope (Some _) ->
      1
  | CisList ->
      1
  | CisRope ->
      1
  | Clength ->
      1
  | Cconcat None ->
      2
  | Cconcat (Some _) ->
      1
  | Cget None ->
      2
  | Cget (Some _) ->
      1
  | Cset (None, None) ->
      3
  | Cset (Some _, None) ->
      2
  | Cset (_, Some _) ->
      1
  | Ccons None ->
      2
  | Ccons (Some _) ->
      1
  | Csnoc None ->
      2
  | Csnoc (Some _) ->
      1
  | CsplitAt None ->
      2
  | CsplitAt (Some _) ->
      1
  | Creverse ->
      1
  | Chead ->
      1
  | Ctail ->
      1
  | Cnull ->
      1
  | Cmap None ->
      2
  | Cmap (Some _) ->
      1
  | Cmapi None ->
      2
  | Cmapi (Some _) ->
      1
  | Citer None ->
      2
  | Citer (Some _) ->
      1
  | Citeri None ->
      2
  | Citeri (Some _) ->
      1
  | Cfoldl (None, None) ->
      3
  | Cfoldl (Some _, None) ->
      2
  | Cfoldl (_, Some _) ->
      1
  | Cfoldr (None, None) ->
      3
  | Cfoldr (Some _, None) ->
      2
  | Cfoldr (_, Some _) ->
      1
  | Csubsequence (None, None) ->
      3
  | Csubsequence (Some _, None) ->
      2
  | Csubsequence (_, Some _) ->
      1
  (* MCore intrinsics: Random numbers *)
  | CrandIntU None ->
      2
  | CrandIntU (Some _) ->
      1
  | CrandSetSeed ->
      1
  (* MCore intrinsics: Time *)
  | CwallTimeMs ->
      1
  | CsleepMs ->
      1
  (* MCore intrinsics: Debug and I/O *)
  | Cprint ->
      1
  | CprintError ->
      1
  | Cdprint ->
      1
  | CreadLine ->
      1
  | CreadBytesAsString ->
      1
  | CreadFile ->
      1
  | CwriteFile None ->
      2
  | CwriteFile (Some _) ->
      1
  | CfileExists ->
      1
  | CdeleteFile ->
      1
  | Ccommand ->
      1
  | Cerror ->
      1
  | Cexit ->
      1
  | CflushStdout ->
      1
  | CflushStderr ->
      1
  (* MCore intrinsics: Symbols *)
  | CSymb _ ->
      0
  | Cgensym ->
      1
  | Ceqsym None ->
      2
  | Ceqsym (Some _) ->
      1
  | Csym2hash ->
      1
  (* MCore intrinsics: Constructor tag *)
  | CconstructorTag ->
      1
  (* MCore intrinsics: References *)
  | Cref ->
      1
  | CmodRef None ->
      2
  | CmodRef (Some _) ->
      1
  | CdeRef ->
      1
  (* MCore intrinsics: Tensor *)
  | CtensorCreateDense None ->
      2
  | CtensorCreateDense (Some _) ->
      1
  | CtensorCreateUninitInt ->
      1
  | CtensorCreateUninitFloat ->
      1
  | CtensorCreateCArrayInt None ->
      2
  | CtensorCreateCArrayInt (Some _) ->
      1
  | CtensorCreateCArrayFloat None ->
      2
  | CtensorCreateCArrayFloat (Some _) ->
      1
  | CtensorGetExn None ->
      2
  | CtensorGetExn (Some _) ->
      1
  | CtensorSetExn (None, None) ->
      3
  | CtensorSetExn (_, None) ->
      2
  | CtensorSetExn (_, Some _) ->
      1
  | CtensorLinearGetExn None ->
      2
  | CtensorLinearGetExn (Some _) ->
      1
  | CtensorLinearSetExn (None, None) ->
      3
  | CtensorLinearSetExn (_, None) ->
      2
  | CtensorLinearSetExn (_, Some _) ->
      1
  | CtensorRank ->
      1
  | CtensorShape ->
      1
  | CtensorCopy ->
      1
  | CtensorTransposeExn (None, None) ->
      3
  | CtensorTransposeExn (_, None) ->
      2
  | CtensorTransposeExn (_, Some _) ->
      1
  | CtensorReshapeExn None ->
      2
  | CtensorReshapeExn (Some _) ->
      1
  | CtensorSliceExn None ->
      2
  | CtensorSliceExn (Some _) ->
      1
  | CtensorSubExn (None, None) ->
      3
  | CtensorSubExn (_, None) ->
      2
  | CtensorSubExn (_, Some _) ->
      1
  | CtensorIterSlice None ->
      2
  | CtensorIterSlice (Some _) ->
      1
  | CtensorEq (None, None) ->
      3
  | CtensorEq (_, None) ->
      2
  | CtensorEq (_, Some _) ->
      1
  | Ctensor2string None ->
      2
  | Ctensor2string (Some _) ->
      1
  (* MCore intrinsics: Boot parser *)
  | CbootParserTree _ ->
      0
  | CbootParserParseMExprString (None, None) ->
      3
  | CbootParserParseMExprString (Some _, None) ->
      2
  | CbootParserParseMExprString (_, Some _) ->
      1
  | CbootParserParseMLangString None ->
      1
  | CbootParserParseMLangString (Some _) ->
      0
  | CbootParserParseMLangFile None ->
      1
  | CbootParserParseMLangFile (Some _) ->
      0
  | CbootParserParseMCoreFile (None, None) ->
      3
  | CbootParserParseMCoreFile (Some _, None) ->
      2
  | CbootParserParseMCoreFile (_, Some _) ->
      1
  | CbootParserGetId ->
      1
  | CbootParserGetTerm None ->
      2
  | CbootParserGetTerm (Some _) ->
      1
  | CbootParserGetDecl None ->
      2
  | CbootParserGetDecl (Some _) ->
      1
  | CbootParserGetTop None ->
      2
  | CbootParserGetTop (Some _) ->
      1
  | CbootParserGetType None ->
      2
  | CbootParserGetType (Some _) ->
      1
  | CbootParserGetString None ->
      2
  | CbootParserGetString (Some _) ->
      1
  | CbootParserGetInt None ->
      2
  | CbootParserGetInt (Some _) ->
      1
  | CbootParserGetFloat None ->
      2
  | CbootParserGetFloat (Some _) ->
      1
  | CbootParserGetListLength None ->
      2
  | CbootParserGetListLength (Some _) ->
      1
  | CbootParserGetConst None ->
      2
  | CbootParserGetConst (Some _) ->
      1
  | CbootParserGetPat None ->
      2
  | CbootParserGetPat (Some _) ->
      1
  | CbootParserGetInfo None ->
      2
  | CbootParserGetInfo (Some _) ->
      1
  (* Python intrinsics *)
  | CPy v ->
      Pyffi.arity v

let fail_constapp f v fi =
  raise_error fi
    ( "Incorrect application. function: "
    ^ Ustring.to_utf8 (ustring_of_const f)
    ^ " value: "
    ^ Ustring.to_utf8 (ustring_of_tm v) )

(* Debug function used in the eval function *)
let debug_eval env t =
  if !enable_debug_eval_tm || !enable_debug_eval_env then (
    printf "-- eval step -- \n" ;
    let env_str =
      if !enable_debug_eval_env then
        us "Environment:\n" ^. ustring_of_env ~margin:80 env ^. us "\n"
      else us ""
    in
    let tm_str =
      if !enable_debug_eval_tm then
        us "Term:\n" ^. ustring_of_tm ~margin:80 t ^. us "\n"
      else us ""
    in
    uprint_endline (env_str ^. tm_str) )
  else ()

let shape_str = function
  | TmRecord (_, record) ->
      Record.bindings record |> List.map fst
      |> Ustring.concat (us ",")
      |> fun x -> us "record: {" ^. x ^. us "}"
  | TmSeq _ ->
      us "Sequence"
  | TmConApp (_, x, s, _) ->
      ustring_of_var ~symbol:!enable_debug_symbol_print x s
  | TmConst (_, CInt _) ->
      us "Int"
  | TmConst (_, CBool _) ->
      us "Bool"
  | TmConst (_, CFloat _) ->
      us "Float"
  | TmConst (_, CChar _) ->
      us "Char"
  | TmConst (_, CSymb _) ->
      us "Symbol"
  | TmConst (_, CPy _) ->
      us "Python Const"
  | TmConst (_, _) ->
      us "Other Const"
  | TmClos _ ->
      us "(closure)"
  | TmRef _ ->
      us "(ref)"
  | _ ->
      us "Other tm"

(* Default failing test message *)
let unittest_default_onfail t1 t2 =
  us " **\n    LHS: " ^. ustring_of_tm t1 ^. us "\n    RHS: "
  ^. ustring_of_tm t2

(* Print out error message when a unit test fails *)
let unittest_failed fi onfail_str using_str =
  uprint_endline
    (let using_str =
       match using_str with
       | Some using_str ->
           us "\n    Using: " ^. using_str
       | None ->
           us ""
     in
     us "\n ** Unit test FAILED: "
     ^. info2str fi ^. us " **\n    " ^. onfail_str ^. using_str )

(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match (v1, v2) with
  | TmSeq (_, s1), TmSeq (_, s2) ->
      Mseq.Helpers.equal val_equal s1 s2
  | TmRecord (_, r1), TmRecord (_, r2) ->
      Record.equal (fun t1 t2 -> val_equal t1 t2) r1 r2
  | TmConst (_, c1), TmConst (_, c2) ->
      c1 = c2
  | TmConApp (_, _, sym1, v1), TmConApp (_, _, sym2, v2) ->
      sym1 = sym2 && val_equal v1 v2
  | TmTensor (_, T.TBootInt t1), TmTensor (_, T.TBootInt t2) ->
      t1 = t2
  | TmTensor (_, T.TBootFloat t1), TmTensor (_, T.TBootFloat t2) ->
      t1 = t2
  | TmTensor (_, T.TBootGen t1), TmTensor (_, T.TBootGen t2) ->
      Tensor.Bop_generic_generic.equal val_equal t1 t2
  | TmTensor (fi, T.TBootInt t1), TmTensor (_, T.TBootGen t2) ->
      Tensor.Bop_barray_generic.equal
        (fun x -> val_equal (TmConst (fi, CInt x)))
        t1 t2
  | TmTensor (fi, T.TBootFloat t1), TmTensor (_, T.TBootGen t2) ->
      Tensor.Bop_barray_generic.equal
        (fun x -> val_equal (TmConst (fi, CFloat x)))
        t1 t2
  | TmTensor (_, T.TBootGen t1), TmTensor (fi, T.TBootInt t2) ->
      Tensor.Bop_generic_barray.equal
        (fun x y -> val_equal x (TmConst (fi, CInt y)))
        t1 t2
  | TmTensor (_, T.TBootGen t1), TmTensor (fi, T.TBootFloat t2) ->
      Tensor.Bop_generic_barray.equal
        (fun x y -> val_equal x (TmConst (fi, CFloat y)))
        t1 t2
  | _ ->
      false

let rec try_match env value pat =
  let go v p env = Option.bind env (fun env -> try_match env v p) in
  let split_nth_or_double_empty n s =
    if Mseq.length s == 0 then (Mseq.empty, Mseq.empty) else Mseq.split_at s n
  in
  let bind fi n tms env =
    match n with
    | NameStr (_, s) ->
        Option.bind env (fun env -> Some ((s, TmSeq (fi, tms)) :: env))
    | NameWildcard ->
        Option.bind env (fun env -> Some env)
  in
  match pat with
  | PatNamed (_, NameStr (_, s)) ->
      Some ((s, value) :: env)
  | PatNamed (_, NameWildcard) ->
      Some env
  | PatSeqTot (_, pats) -> (
      let npats = Mseq.length pats in
      match value with
      | TmSeq (_, vs) when npats = Mseq.length vs ->
          Mseq.Helpers.fold_right2 go vs pats (Some env)
      | _ ->
          None )
  | PatSeqEdge (_, l, x, r) -> (
      let npre = Mseq.length l in
      let npost = Mseq.length r in
      match value with
      | TmSeq (fi, vs) when npre + npost <= Mseq.length vs ->
          let pre, vs = split_nth_or_double_empty npre vs in
          let vs, post =
            split_nth_or_double_empty (Mseq.length vs - npost) vs
          in
          Mseq.Helpers.fold_right2 go post r (Some env)
          |> bind fi x vs
          |> Mseq.Helpers.fold_right2 go pre l
      | _ ->
          None )
  | PatRecord (_, pats) -> (
    match value with
    | TmRecord (_, vs) ->
        let merge_f _ v p =
          match (v, p) with
          | None, None ->
              None
          | Some _, None ->
              None
          | Some v, Some p ->
              Some (go v p)
          | None, Some _ ->
              Some (fun _ -> None)
        in
        Record.merge merge_f vs pats
        |> fun merged -> Record.fold (fun _ f env -> f env) merged (Some env)
    | _ ->
        None )
  | PatCon (_, _, s1, p) -> (
    match value with
    | TmConApp (_, _, s2, v) when s1 = s2 ->
        try_match env v p
    | _ ->
        None )
  | PatInt (_, i) -> (
    match value with TmConst (_, CInt i2) when i = i2 -> Some env | _ -> None )
  | PatChar (_, c) -> (
    match value with
    | TmConst (_, CChar c2) when c = c2 ->
        Some env
    | _ ->
        None )
  | PatBool (_, b) -> (
    match value with
    | TmConst (_, CBool b2) when b = b2 ->
        Some env
    | _ ->
        None )
  | PatAnd (_, l, r) ->
      go value r (Some env) |> go value l
  | PatOr (_, l, r) -> (
    match try_match env value l with
    | Some env ->
        Some env
    | None ->
        try_match env value r )
  | PatNot (_, p) -> (
    match try_match env value p with Some _ -> None | None -> Some env )

(* Tracks the number of calls and cumulative runtime of closures *)
let runtimes = Hashtbl.create 1024

(* Record a call to a closure *)
let add_call fi ms =
  if Hashtbl.mem runtimes fi then
    let old_count, old_time = Hashtbl.find runtimes fi in
    Hashtbl.replace runtimes fi (old_count + 1, old_time +. ms)
  else Hashtbl.add runtimes fi (1, ms)

let parseMLangString str =
  try
    let prog =
      str |> Intrinsics.Mseq.Helpers.to_ustring
      |> Parserutils.parse_mlang_string
    in
    PTreeProgram prog
  with (Lexer.Lex_error _ | Msg.Error _ | Parser.Error) as e ->
    PTreeError
      [ ( match Parserutils.error_to_error_message e with
        | Some (id, _, info, _) ->
            (info, id2str id)
        | None ->
            (NoInfo, us (Printexc.to_string e)) ) ]

let parseMLangFile filename =
  try
    let prog =
      filename |> Intrinsics.Mseq.Helpers.to_ustring |> Ustring.to_utf8
      |> Utils.normalize_path |> Parserutils.local_parse_mcore_file
    in
    PTreeProgram prog
  with (Lexer.Lex_error _ | Msg.Error _ | Parser.Error) as e ->
    PTreeError
      [ ( match Parserutils.error_to_error_message e with
        | Some (id, _, info, _) ->
            (info, id2str id)
        | None ->
            (NoInfo, us (Printexc.to_string e)) ) ]

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
  with (Lexer.Lex_error _ | Msg.Error _ | Parser.Error) as e ->
    PTreeError
      [ ( match Parserutils.error_to_error_message e with
        | Some (id, _, info, _) ->
            (info, id2str id)
        | None ->
            (NoInfo, us (Printexc.to_string e)) ) ]

let rec is_value = function
  | TmConst (_, _) ->
      true
  | TmSeq (_, tms) ->
      let _ = tms in
      true
      (*Mseq.Helpers.fold_left (fun a t -> a && (is_value t)) true tms *)
      (* TODO FIX *)
  | TmRecord (_, tms) ->
      let _ = tms in
      true
  (* Record.for_all (fun _ t -> is_value t) tms *)
  | TmConDef (_, _, _, _, t) ->
      is_value t
  | TmConApp (_, _, _, t) ->
      is_value t
  | TmNever _ ->
      true
  | TmClos (_, _, _, _, _, _) ->
      true
  | TmRef (_, _) ->
      true
  | TmTensor (_, _) ->
      true
  | _ ->
      false

let rec parseMCoreFile
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
        |> Mlang.translate_program
        |> Parserutils.raise_parse_error_on_non_unique_external_id
        |> Symbolize.symbolize name2sym
        |> Parserutils.raise_parse_error_on_partially_applied_external
        |> (fun t -> if keep_utests then t else Parserutils.remove_all_utests t)
        |> deadcode_elimination
           (* |> scan builtin_sym2term  (* TODO: Bug, cannot compile with meta programming *)*)
        |> Parserutils.prune_external_utests
             ~enable:(keep_utests && prune_external_utests)
             ~externals_exclude ~warn
        |> deadcode_elimination )
    in
    Symbolize.allow_free := allow_free_prev ;
    r
  with (Lexer.Lex_error _ | Msg.Error _ | Parser.Error) as e ->
    reportErrorAndExit e

(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
and delta (apply : info -> tm -> tm -> tm) fi c v =
  let apply = apply fi in
  let apply_args (f : tm) (args : tm list) : tm =
    List.fold_left apply f args
  in
  let index_out_of_bounds_in_seq_msg = "Out of bounds access in sequence" in
  let fail_constapp = fail_constapp c v in
  let tm_seq2int_seq fi tmseq =
    let to_int = function
      | TmConst (_, CChar n) ->
          n
      | TmConst (_, CInt n) ->
          n
      | _ ->
          fail_constapp fi
    in
    tmseq |> Mseq.map to_int
  in
  let int_seq2char_tm_seq fi intseq =
    TmSeq (fi, Mseq.map (fun n -> TmConst (fi, CChar n)) intseq)
  in
  let int_seq2int_tm_seq fi intseq =
    TmSeq (fi, Mseq.map (fun n -> TmConst (fi, CInt n)) intseq)
  in
  match (c, v) with
  | CunsafeCoerce, v ->
      v
  (* MCore intrinsics: Booleans *)
  | CBool _, _ ->
      fail_constapp fi
  (* MCore intrinsics: Integers *)
  | CInt _, _ ->
      fail_constapp fi
  | Caddi None, TmConst (fi, CInt v) ->
      TmConst (fi, Caddi (Some v))
  | Caddi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 + v2))
  | Caddi None, _ | Caddi (Some _), _ ->
      fail_constapp fi
  | Csubi None, TmConst (fi, CInt v) ->
      TmConst (fi, Csubi (Some v))
  | Csubi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 - v2))
  | Csubi None, _ | Csubi (Some _), _ ->
      fail_constapp fi
  | Cmuli None, TmConst (fi, CInt v) ->
      TmConst (fi, Cmuli (Some v))
  | Cmuli (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 * v2))
  | Cmuli None, _ | Cmuli (Some _), _ ->
      fail_constapp fi
  | Cdivi None, TmConst (fi, CInt v) ->
      TmConst (fi, Cdivi (Some v))
  | Cdivi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 / v2))
  | Cdivi None, _ | Cdivi (Some _), _ ->
      fail_constapp fi
  | Cmodi None, TmConst (fi, CInt v) ->
      TmConst (fi, Cmodi (Some v))
  | Cmodi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 mod v2))
  | Cmodi None, _ | Cmodi (Some _), _ ->
      fail_constapp fi
  | Cnegi, TmConst (fi, CInt v) ->
      TmConst (fi, CInt (-1 * v))
  | Cnegi, _ ->
      fail_constapp fi
  | Clti None, TmConst (fi, CInt v) ->
      TmConst (fi, Clti (Some v))
  | Clti (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 < v2))
  | Clti None, _ | Clti (Some _), _ ->
      fail_constapp fi
  | Cleqi None, TmConst (fi, CInt v) ->
      TmConst (fi, Cleqi (Some v))
  | Cleqi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 <= v2))
  | Cleqi None, _ | Cleqi (Some _), _ ->
      fail_constapp fi
  | Cgti None, TmConst (fi, CInt v) ->
      TmConst (fi, Cgti (Some v))
  | Cgti (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 > v2))
  | Cgti None, _ | Cgti (Some _), _ ->
      fail_constapp fi
  | Cgeqi None, TmConst (fi, CInt v) ->
      TmConst (fi, Cgeqi (Some v))
  | Cgeqi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 >= v2))
  | Cgeqi None, _ | Cgeqi (Some _), _ ->
      fail_constapp fi
  | Ceqi None, TmConst (fi, CInt v) ->
      TmConst (fi, Ceqi (Some v))
  | Ceqi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 = v2))
  | Ceqi None, _ | Ceqi (Some _), _ ->
      fail_constapp fi
  | Cneqi None, TmConst (fi, CInt v) ->
      TmConst (fi, Cneqi (Some v))
  | Cneqi (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CBool (v1 <> v2))
  | Cneqi None, _ | Cneqi (Some _), _ ->
      fail_constapp fi
  | Cslli None, TmConst (fi, CInt v) ->
      TmConst (fi, Cslli (Some v))
  | Cslli (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 lsl v2))
  | Cslli None, _ | Cslli (Some _), _ ->
      fail_constapp fi
  | Csrli None, TmConst (fi, CInt v) ->
      TmConst (fi, Csrli (Some v))
  | Csrli (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 lsr v2))
  | Csrli None, _ | Csrli (Some _), _ ->
      fail_constapp fi
  | Csrai None, TmConst (fi, CInt v) ->
      TmConst (fi, Csrai (Some v))
  | Csrai (Some v1), TmConst (fi, CInt v2) ->
      TmConst (fi, CInt (v1 asr v2))
  | Csrai None, _ | Csrai (Some _), _ ->
      fail_constapp fi
  | Carity, TmConst (fi, c) ->
      TmConst (fi, CInt (arity c))
  | Carity, _ ->
      fail_constapp fi
  (* MCore intrinsics: Floating-point numbers *)
  | CFloat _, _ ->
      fail_constapp fi
  | Caddf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Caddf (Some v))
  | Caddf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CFloat (v1 +. v2))
  | Caddf None, _ | Caddf (Some _), _ ->
      fail_constapp fi
  | Csubf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Csubf (Some v))
  | Csubf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CFloat (v1 -. v2))
  | Csubf None, _ | Csubf (Some _), _ ->
      fail_constapp fi
  | Cmulf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cmulf (Some v))
  | Cmulf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CFloat (v1 *. v2))
  | Cmulf None, _ | Cmulf (Some _), _ ->
      fail_constapp fi
  | Cdivf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cdivf (Some v))
  | Cdivf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CFloat (v1 /. v2))
  | Cdivf None, _ | Cdivf (Some _), _ ->
      fail_constapp fi
  | Cnegf, TmConst (fi, CFloat v) ->
      TmConst (fi, CFloat (-1.0 *. v))
  | Cnegf, _ ->
      fail_constapp fi
  | Cltf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cltf (Some v))
  | Cltf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 < v2))
  | Cltf None, _ | Cltf (Some _), _ ->
      fail_constapp fi
  | Cleqf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cleqf (Some v))
  | Cleqf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 <= v2))
  | Cleqf None, _ | Cleqf (Some _), _ ->
      fail_constapp fi
  | Cgtf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cgtf (Some v))
  | Cgtf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 > v2))
  | Cgtf None, _ | Cgtf (Some _), _ ->
      fail_constapp fi
  | Cgeqf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cgeqf (Some v))
  | Cgeqf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 >= v2))
  | Cgeqf None, _ | Cgeqf (Some _), _ ->
      fail_constapp fi
  | Ceqf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Ceqf (Some v))
  | Ceqf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 = v2))
  | Ceqf None, _ | Ceqf (Some _), _ ->
      fail_constapp fi
  | Cneqf None, TmConst (fi, CFloat v) ->
      TmConst (fi, Cneqf (Some v))
  | Cneqf (Some v1), TmConst (fi, CFloat v2) ->
      TmConst (fi, CBool (v1 <> v2))
  | Cneqf None, _ | Cneqf (Some _), _ ->
      fail_constapp fi
  | CstringIsFloat, TmSeq (_, s) ->
      let s = tm_seq2int_seq fi s in
      TmConst (fi, CBool (Intrinsics.FloatConversion.string_is_float s))
  | CstringIsFloat, _ ->
      fail_constapp fi
  | Cstring2float, TmSeq (fi, s) ->
      let f = tm_seq2int_seq fi s in
      TmConst (fi, CFloat (Intrinsics.FloatConversion.string2float f))
  | Cstring2float, _ ->
      fail_constapp fi
  | Cfloat2string, TmConst (fi, CFloat f) ->
      let tms = Intrinsics.FloatConversion.float2string f in
      int_seq2char_tm_seq fi tms
  | Cfloat2string, _ ->
      fail_constapp fi
  | Cfloorfi, TmConst (fi, CFloat v) ->
      TmConst (fi, CInt (Intrinsics.FloatConversion.floorfi v))
  | Cfloorfi, _ ->
      fail_constapp fi
  | Cceilfi, TmConst (fi, CFloat v) ->
      TmConst (fi, CInt (Intrinsics.FloatConversion.ceilfi v))
  | Cceilfi, _ ->
      fail_constapp fi
  | Croundfi, TmConst (fi, CFloat v) ->
      TmConst (fi, CInt (Intrinsics.FloatConversion.roundfi v))
  | Croundfi, _ ->
      fail_constapp fi
  | Cint2float, TmConst (fi, CInt v) ->
      TmConst (fi, CFloat (float_of_int v))
  | Cint2float, _ ->
      fail_constapp fi
  (* MCore intrinsics: Characters *)
  | CChar _, _ ->
      fail_constapp fi
  | Ceqc None, TmConst (fi, CChar v) ->
      TmConst (fi, Ceqc (Some v))
  | Ceqc (Some v1), TmConst (fi, CChar v2) ->
      TmConst (fi, CBool (v1 = v2))
  | Ceqc None, _ | Ceqc (Some _), _ ->
      fail_constapp fi
  | Cchar2int, TmConst (fi, CChar v) ->
      TmConst (fi, CInt v)
  | Cchar2int, _ ->
      fail_constapp fi
  | Cint2char, TmConst (fi, CInt v) ->
      TmConst (fi, CChar v)
  | Cint2char, _ ->
      fail_constapp fi
  (* MCore intrinsic: sequences *)
  | Ccreate None, TmConst (_, CInt n) ->
      TmConst (fi, Ccreate (Some n))
  | Ccreate (Some n), f ->
      let createf i = apply f (TmConst (NoInfo, CInt i)) in
      TmSeq (tm_info f, Mseq.create n createf)
  | Ccreate None, _ ->
      fail_constapp fi
  | CcreateList None, TmConst (_, CInt n) ->
      TmConst (fi, CcreateList (Some n))
  | CcreateList (Some n), f ->
      let createf i = apply f (TmConst (NoInfo, CInt i)) in
      TmSeq (tm_info f, Mseq.create_list n createf)
  | CcreateList None, _ ->
      fail_constapp fi
  | CcreateRope None, TmConst (_, CInt n) ->
      TmConst (fi, CcreateRope (Some n))
  | CcreateRope (Some n), f ->
      let createf i = apply f (TmConst (NoInfo, CInt i)) in
      TmSeq (tm_info f, Mseq.create_rope n createf)
  | CcreateRope None, _ ->
      fail_constapp fi
  | CisList, TmSeq (fi, s) ->
      TmConst (fi, CBool (Mseq.is_list s))
  | CisList, _ ->
      fail_constapp fi
  | CisRope, TmSeq (fi, s) ->
      TmConst (fi, CBool (Mseq.is_rope s))
  | CisRope, _ ->
      fail_constapp fi
  | Clength, TmSeq (fi, s) ->
      TmConst (fi, CInt (Mseq.length s))
  | Clength, _ ->
      fail_constapp fi
  | Cconcat None, TmSeq (fi, s1) ->
      TmConst (fi, Cconcat (Some s1))
  | Cconcat (Some s1), TmSeq (fi, s2) ->
      TmSeq (fi, Mseq.concat s1 s2)
  | Cconcat None, _ | Cconcat (Some _), _ ->
      fail_constapp fi
  | Cget None, TmSeq (fi, s) ->
      TmConst (fi, Cget (Some s))
  | Cget (Some s), TmConst (_, CInt n) -> (
    try Mseq.get s n with _ -> raise_error fi index_out_of_bounds_in_seq_msg )
  | Cget None, _ | Cget (Some _), _ ->
      fail_constapp fi
  | Cset (None, None), TmSeq (_, s) ->
      TmConst (fi, Cset (Some s, None))
  | Cset (Some s, None), TmConst (_, CInt n) ->
      TmConst (fi, Cset (Some s, Some n))
  | Cset (Some s, Some n), t ->
      let s =
        try Mseq.set s n t
        with _ -> raise_error fi index_out_of_bounds_in_seq_msg
      in
      TmSeq (fi, s)
  | Cset (_, _), _ ->
      fail_constapp fi
  | Ccons None, t ->
      TmConst (tm_info t, Ccons (Some t))
  | Ccons (Some t), TmSeq (fi, s) ->
      TmSeq (fi, Mseq.cons t s)
  | Ccons (Some _), _ ->
      fail_constapp fi
  | Csnoc None, TmSeq (_, s) ->
      TmConst (fi, Csnoc (Some s))
  | Csnoc (Some s), t ->
      TmSeq (fi, Mseq.snoc s t)
  | Csnoc _, _ ->
      fail_constapp fi
  | CsplitAt None, TmSeq (fi, s) ->
      TmConst (fi, CsplitAt (Some s))
  | CsplitAt (Some s), TmConst (_, CInt n) ->
      let t =
        try Mseq.split_at s n
        with _ -> raise_error fi index_out_of_bounds_in_seq_msg
      in
      tuple2record fi [TmSeq (fi, fst t); TmSeq (fi, snd t)]
  | CsplitAt None, _ | CsplitAt (Some _), _ ->
      fail_constapp fi
  | Creverse, TmSeq (fi, s) ->
      TmSeq (fi, Mseq.reverse s)
  | Creverse, _ ->
      fail_constapp fi
  | Chead, TmSeq (_, s) ->
      Mseq.head s
  | Chead, _ ->
      fail_constapp fi
  | Ctail, TmSeq (fi, s) ->
      TmSeq (fi, Mseq.tail s)
  | Ctail, _ ->
      fail_constapp fi
  | Cnull, TmSeq (fi, s) ->
      TmConst (fi, CBool (Mseq.null s))
  | Cnull, _ ->
      fail_constapp fi
  | Cmap None, f ->
      TmConst (fi, Cmap (Some (apply f)))
  | Cmap (Some f), TmSeq (fi, s) ->
      TmSeq (fi, Mseq.map f s)
  | Cmap _, _ ->
      fail_constapp fi
  | Cmapi None, f ->
      let f i x = apply_args f [TmConst (NoInfo, CInt i); x] in
      TmConst (fi, Cmapi (Some f))
  | Cmapi (Some f), TmSeq (fi, s) ->
      TmSeq (fi, Mseq.mapi f s)
  | Cmapi _, _ ->
      fail_constapp fi
  | Citer None, f ->
      let f x = apply f x |> ignore in
      TmConst (fi, Citer (Some f))
  | Citer (Some f), TmSeq (_, s) ->
      Mseq.iter f s ; tm_unit
  | Citer _, _ ->
      fail_constapp fi
  | Citeri None, f ->
      let f i x = apply_args f [TmConst (NoInfo, CInt i); x] |> ignore in
      TmConst (fi, Citeri (Some f))
  | Citeri (Some f), TmSeq (_, s) ->
      Mseq.iteri f s ; tm_unit
  | Citeri _, _ ->
      fail_constapp fi
  | Cfoldl (None, None), f ->
      let f a x = apply_args f [a; x] in
      TmConst (fi, Cfoldl (Some f, None))
  | Cfoldl (Some f, None), a ->
      TmConst (fi, Cfoldl (Some f, Some a))
  | Cfoldl (Some f, Some a), TmSeq (_, s) ->
      Mseq.Helpers.fold_left f a s
  | Cfoldl _, _ ->
      fail_constapp fi
  | Cfoldr (None, None), f ->
      let f x a = apply_args f [x; a] in
      TmConst (fi, Cfoldr (Some f, None))
  | Cfoldr (Some f, None), a ->
      TmConst (fi, Cfoldr (Some f, Some a))
  | Cfoldr (Some f, Some a), TmSeq (_, s) ->
      Mseq.Helpers.fold_right f a s
  | Cfoldr _, _ ->
      fail_constapp fi
  | Csubsequence (None, None), TmSeq (fi, s) ->
      TmConst (fi, Csubsequence (Some s, None))
  | Csubsequence (Some s, None), TmConst (_, CInt off) ->
      TmConst (fi, Csubsequence (Some s, Some off))
  | Csubsequence (Some s, Some off), TmConst (_, CInt n) ->
      TmSeq (fi, Mseq.subsequence s off n)
  | Csubsequence _, _ ->
      fail_constapp fi
  (* MCore intrinsics: Random numbers *)
  | CrandIntU None, TmConst (fi, CInt v) ->
      TmConst (fi, CrandIntU (Some v))
  | CrandIntU (Some v1), TmConst (fi, CInt v2) ->
      if v1 >= v2 then
        raise_error fi
          "Lower bound to randInt must be smaller than upper bound"
      else TmConst (fi, CInt (RNG.int_u v1 v2))
  | CrandIntU _, _ ->
      fail_constapp fi
  | CrandSetSeed, TmConst (_, CInt v) ->
      RNG.set_seed v ; tm_unit
  | CrandSetSeed, _ ->
      fail_constapp fi
  (* MCore intrinsics: Time *)
  | CwallTimeMs, TmRecord (fi, x) when Record.is_empty x ->
      TmConst (fi, CFloat (Time.get_wall_time_ms ()))
  | CwallTimeMs, _ ->
      fail_constapp fi
  | CsleepMs, TmConst (_, CInt v) ->
      Time.sleep_ms v ; tm_unit
  | CsleepMs, _ ->
      fail_constapp fi
  (* MCore intrinsics: Debug and I/O *)
  | Cprint, TmSeq (fi, lst) ->
      !program_output (tmseq2ustring fi lst) ;
      tm_unit
  | Cprint, _ ->
      raise_error fi "The argument to print must be a string"
  | CprintError, TmSeq (fi, lst) ->
      tmseq2seq_of_int fi lst |> Intrinsics.IO.print_error ;
      tm_unit
  | CprintError, _ ->
      raise_error fi "The argument to print must be a string"
  | Cdprint, t ->
      !program_output (ustring_of_tm t) ;
      tm_unit
  | CreadLine, TmRecord (_, r) when r = Record.empty ->
      let line = Intrinsics.IO.read_line () in
      let tms = Mseq.map (fun n -> TmConst (fi, CChar n)) line in
      TmSeq (fi, tms)
  | CreadLine, _ ->
      fail_constapp fi
  | CreadBytesAsString, TmConst (_, CInt v) ->
      if v < 0 then
        raise_error fi
          "The argument to readBytesAsString must be a positive integer"
      else
        let str = try really_input_string stdin v with End_of_file -> "" in
        let ustr =
          try Ustring.from_utf8 str
          with Invalid_argument _ -> raise_error fi "Received invalid UTF-8"
        in
        tuple2record fi
          [ TmSeq (fi, ustring2tmseq fi ustr)
          ; TmConst (fi, CInt (String.length str)) ]
  | CreadBytesAsString, _ ->
      fail_constapp fi
  | CreadFile, TmSeq (fi, lst) ->
      let intseq = tm_seq2int_seq fi lst in
      let str = Intrinsics.File.read intseq in
      int_seq2char_tm_seq fi str
  | CreadFile, _ ->
      fail_constapp fi
  | CwriteFile None, TmSeq (fi, l) ->
      TmConst (fi, CwriteFile (Some (tm_seq2int_seq fi l)))
  | CwriteFile (Some fname), TmSeq (fi, lst) ->
      Intrinsics.File.write fname (tm_seq2int_seq fi lst) ;
      tm_unit
  | CwriteFile (Some _), _ ->
      fail_constapp fi
  | CwriteFile None, _ ->
      fail_constapp fi
  | CfileExists, TmSeq (fi, lst) ->
      TmConst (fi, CBool (Intrinsics.File.exists (tm_seq2int_seq fi lst)))
  | CfileExists, _ ->
      fail_constapp fi
  | CdeleteFile, TmSeq (fi, lst) ->
      Intrinsics.File.delete (tm_seq2int_seq fi lst) ;
      tm_unit
  | CdeleteFile, _ ->
      fail_constapp fi
  | Ccommand, TmSeq (_, lst) ->
      TmConst (fi, CInt (Intrinsics.MSys.command (tm_seq2int_seq fi lst)))
  | Ccommand, _ ->
      fail_constapp fi
  | Cerror, TmSeq (fiseq, lst) ->
      tmseq2ustring fiseq lst |> Ustring.to_utf8 |> raise_error fi
  | Cerror, _ ->
      fail_constapp fi
  | Cexit, TmConst (_, CInt x) ->
      exit x
  | Cexit, _ ->
      fail_constapp fi
  | CflushStdout, TmRecord (_, x) when Record.is_empty x ->
      Intrinsics.IO.flush_stdout () ;
      tm_unit
  | CflushStdout, _ ->
      fail_constapp fi
  | CflushStderr, TmRecord (_, x) when Record.is_empty x ->
      Intrinsics.IO.flush_stderr () ;
      tm_unit
  | CflushStderr, _ ->
      fail_constapp fi
  (* MCore intrinsics: Symbols *)
  | CSymb _, _ ->
      fail_constapp fi
  | Cgensym, TmRecord (fi, x) when Record.is_empty x ->
      TmConst (fi, CSymb (Symb.gensym ()))
  | Cgensym, _ ->
      fail_constapp fi
  | Ceqsym None, TmConst (fi, CSymb id) ->
      TmConst (fi, Ceqsym (Some id))
  | Ceqsym (Some id), TmConst (fi, CSymb id') ->
      TmConst (fi, CBool (id == id'))
  | Ceqsym _, _ ->
      fail_constapp fi
  | Csym2hash, TmConst (fi, CSymb id) ->
      TmConst (fi, CInt (Symb.hash id))
  | Csym2hash, _ ->
      fail_constapp fi
  (* MCore intrinsics: Constructor tag *)
  | CconstructorTag, TmConApp (_, _, sym, _) ->
      TmConst (fi, CInt (Symb.hash sym))
  | CconstructorTag, _ ->
      TmConst (fi, CInt 0)
  (* MCore intrinsics: References *)
  | Cref, v ->
      TmRef (fi, ref v)
  | CmodRef None, TmRef (fi, r) ->
      TmConst (fi, CmodRef (Some r))
  | CmodRef (Some r), v ->
      r := v ;
      tm_unit
  | CmodRef None, _ ->
      fail_constapp fi
  | CdeRef, TmRef (_, r) ->
      !r
  | CdeRef, _ ->
      fail_constapp fi
  (* MCore intrinsics: Tensors *)
  | CtensorCreateUninitInt, TmSeq (_, seq) ->
      let shape = tm_seq2int_seq fi seq in
      T.uninit_int shape |> fun t -> TmTensor (fi, T.TBootInt t)
  | CtensorCreateUninitInt, _ ->
      fail_constapp fi
  | CtensorCreateUninitFloat, TmSeq (_, seq) ->
      let shape = tm_seq2int_seq fi seq in
      T.uninit_float shape |> fun t -> TmTensor (fi, T.TBootFloat t)
  | CtensorCreateUninitFloat, _ ->
      fail_constapp fi
  | CtensorCreateCArrayInt None, TmSeq (_, seq) ->
      let shape = tm_seq2int_seq fi seq in
      TmConst (fi, CtensorCreateDense (Some shape))
  | CtensorCreateCArrayInt (Some shape), tm ->
      let f is =
        let tmseq = int_seq2int_tm_seq (tm_info tm) is in
        apply tm tmseq
        |> function
        | TmConst (_, CInt n) -> n | _ -> raise_error fi "Expected integer"
      in
      T.create_int shape f |> fun t -> TmTensor (fi, T.TBootInt t)
  | CtensorCreateCArrayInt _, _ ->
      fail_constapp fi
  | CtensorCreateCArrayFloat None, TmSeq (_, seq) ->
      let shape = tm_seq2int_seq fi seq in
      TmConst (fi, CtensorCreateDense (Some shape))
  | CtensorCreateCArrayFloat (Some shape), tm ->
      let f is =
        let tmseq = int_seq2int_tm_seq (tm_info tm) is in
        apply tm tmseq
        |> function
        | TmConst (_, CFloat r) -> r | _ -> raise_error fi "Expected float"
      in
      T.create_float shape f |> fun t -> TmTensor (fi, T.TBootFloat t)
  | CtensorCreateCArrayFloat _, _ ->
      fail_constapp fi
  | CtensorCreateDense None, TmSeq (_, seq) ->
      let shape = tm_seq2int_seq fi seq in
      TmConst (fi, CtensorCreateDense (Some shape))
  | CtensorCreateDense (Some shape), tm ->
      let f is =
        let tmseq = int_seq2int_tm_seq (tm_info tm) is in
        apply tm tmseq
      in
      T.create_generic shape f |> fun t -> TmTensor (fi, T.TBootGen t)
  | CtensorCreateDense _, _ ->
      fail_constapp fi
  | CtensorGetExn None, TmTensor (_, t) ->
      TmConst (fi, CtensorGetExn (Some t))
  | CtensorGetExn (Some t), TmSeq (_, seq) -> (
      let is = tm_seq2int_seq fi seq in
      try
        t
        |> function
        | T.TBootInt t' ->
            TmConst (fi, CInt (T.Op_mseq_barray.get_exn t' is))
        | T.TBootFloat t' ->
            TmConst (fi, CFloat (T.Op_mseq_barray.get_exn t' is))
        | T.TBootGen t' ->
            T.Op_mseq_generic.get_exn t' is
      with Invalid_argument msg -> raise_error fi msg )
  | CtensorGetExn _, _ ->
      fail_constapp fi
  | CtensorSetExn (None, None), TmTensor (_, t) ->
      TmConst (fi, CtensorSetExn (Some t, None))
  | CtensorSetExn (Some t, None), TmSeq (_, seq) ->
      let idx = tm_seq2int_seq fi seq in
      TmConst (fi, CtensorSetExn (Some t, Some idx))
  | CtensorSetExn (Some (T.TBootInt t), Some idx), TmConst (_, CInt n) -> (
    try
      T.Op_mseq_barray.set_exn t idx n ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorSetExn (Some (T.TBootFloat t), Some idx), TmConst (_, CFloat r) -> (
    try
      T.Op_mseq_barray.set_exn t idx r ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorSetExn (Some (T.TBootGen t), Some idx), tm -> (
    try
      T.Op_mseq_generic.set_exn t idx tm ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorSetExn _, _ ->
      fail_constapp fi
  | CtensorLinearGetExn None, TmTensor (_, t) ->
      TmConst (fi, CtensorLinearGetExn (Some t))
  | CtensorLinearGetExn (Some t), TmConst (_, CInt idx) -> (
    try
      t
      |> function
      | T.TBootInt t' ->
          TmConst (fi, CInt (T.Op_mseq_barray.linear_get_exn t' idx))
      | T.TBootFloat t' ->
          TmConst (fi, CFloat (T.Op_mseq_barray.linear_get_exn t' idx))
      | T.TBootGen t' ->
          T.Op_mseq_generic.linear_get_exn t' idx
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorLinearGetExn _, _ ->
      fail_constapp fi
  | CtensorLinearSetExn (None, None), TmTensor (_, t) ->
      TmConst (fi, CtensorLinearSetExn (Some t, None))
  | CtensorLinearSetExn (Some t, None), TmConst (_, CInt idx) ->
      TmConst (fi, CtensorLinearSetExn (Some t, Some idx))
  | CtensorLinearSetExn (Some (T.TBootInt t), Some idx), TmConst (_, CInt n)
    -> (
    try
      T.Op_mseq_barray.linear_set_exn t idx n ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorLinearSetExn (Some (T.TBootFloat t), Some idx), TmConst (_, CFloat r)
    -> (
    try
      T.Op_mseq_barray.linear_set_exn t idx r ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorLinearSetExn (Some (T.TBootGen t), Some idx), tm -> (
    try
      T.Op_mseq_generic.linear_set_exn t idx tm ;
      tm_unit
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorLinearSetExn _, _ ->
      fail_constapp fi
  | CtensorRank, TmTensor (_, t) ->
      let n =
        t
        |> function
        | T.TBootInt t' ->
            Tensor.Barray.rank t'
        | T.TBootFloat t' ->
            Tensor.Barray.rank t'
        | T.TBootGen t' ->
            Tensor.Generic.rank t'
      in
      TmConst (fi, CInt n)
  | CtensorRank, _ ->
      fail_constapp fi
  | CtensorShape, TmTensor (_, t) ->
      let shape =
        t
        |> function
        | T.TBootInt t' ->
            T.Op_mseq_barray.shape t'
        | T.TBootFloat t' ->
            T.Op_mseq_barray.shape t'
        | T.TBootGen t' ->
            T.Op_mseq_generic.shape t'
      in
      int_seq2int_tm_seq fi shape
  | CtensorShape, _ ->
      fail_constapp fi
  | CtensorCopy, TmTensor (_, T.TBootInt t) ->
      TmTensor (fi, T.TBootInt (Tensor.Barray.copy t))
  | CtensorCopy, TmTensor (_, T.TBootFloat t) ->
      TmTensor (fi, T.TBootFloat (Tensor.Barray.copy t))
  | CtensorCopy, TmTensor (_, T.TBootGen t) ->
      TmTensor (fi, T.TBootGen (Tensor.Generic.copy t))
  | CtensorCopy, _ ->
      fail_constapp fi
  | CtensorTransposeExn (None, None), TmTensor (_, t) ->
      TmConst (fi, CtensorTransposeExn (Some t, None))
  | CtensorTransposeExn (Some t, None), TmConst (_, CInt n) ->
      TmConst (fi, CtensorTransposeExn (Some t, Some n))
  | CtensorTransposeExn (Some (T.TBootInt t), Some n1), TmConst (_, CInt n2) ->
      TmTensor (fi, T.TBootInt (Tensor.Barray.transpose_exn t n1 n2))
  | CtensorTransposeExn (Some (T.TBootFloat t), Some n1), TmConst (_, CInt n2)
    ->
      TmTensor (fi, T.TBootFloat (Tensor.Barray.transpose_exn t n1 n2))
  | CtensorTransposeExn (Some (T.TBootGen t), Some n1), TmConst (_, CInt n2) ->
      TmTensor (fi, T.TBootGen (Tensor.Generic.transpose_exn t n1 n2))
  | CtensorTransposeExn _, _ ->
      fail_constapp fi
  | CtensorReshapeExn None, TmTensor (_, t) ->
      TmConst (fi, CtensorReshapeExn (Some t))
  | CtensorReshapeExn (Some t), TmSeq (_, seq) -> (
      let is = tm_seq2int_seq fi seq in
      try
        let t' =
          t
          |> function
          | T.TBootInt t'' ->
              T.TBootInt (T.Op_mseq_barray.reshape_exn t'' is)
          | T.TBootFloat t'' ->
              T.TBootFloat (T.Op_mseq_barray.reshape_exn t'' is)
          | T.TBootGen t'' ->
              T.TBootGen (T.Op_mseq_generic.reshape_exn t'' is)
        in
        TmTensor (fi, t')
      with Invalid_argument msg -> raise_error fi msg )
  | CtensorReshapeExn _, _ ->
      fail_constapp fi
  | CtensorSliceExn None, TmTensor (_, t) ->
      TmConst (fi, CtensorSliceExn (Some t))
  | CtensorSliceExn (Some t), TmSeq (_, seq) -> (
      let is = tm_seq2int_seq fi seq in
      try
        let t' =
          t
          |> function
          | T.TBootInt t'' ->
              T.TBootInt (T.Op_mseq_barray.slice_exn t'' is)
          | T.TBootFloat t'' ->
              T.TBootFloat (T.Op_mseq_barray.slice_exn t'' is)
          | T.TBootGen t'' ->
              T.TBootGen (T.Op_mseq_generic.slice_exn t'' is)
        in
        TmTensor (fi, t')
      with Invalid_argument msg -> raise_error fi msg )
  | CtensorSliceExn _, _ ->
      fail_constapp fi
  | CtensorSubExn (None, None), TmTensor (_, t) ->
      TmConst (fi, CtensorSubExn (Some t, None))
  | CtensorSubExn (Some t, None), TmConst (_, CInt ofs) ->
      TmConst (fi, CtensorSubExn (Some t, Some ofs))
  | CtensorSubExn (Some t, Some ofs), TmConst (_, CInt len) -> (
    try
      let t' =
        t
        |> function
        | T.TBootInt t'' ->
            T.TBootInt (Tensor.Barray.sub_exn t'' ofs len)
        | T.TBootFloat t'' ->
            T.TBootFloat (Tensor.Barray.sub_exn t'' ofs len)
        | T.TBootGen t'' ->
            T.TBootGen (Tensor.Generic.sub_exn t'' ofs len)
      in
      TmTensor (fi, t')
    with Invalid_argument msg -> raise_error fi msg )
  | CtensorSubExn _, _ ->
      fail_constapp fi
  | CtensorIterSlice None, tm ->
      TmConst (fi, CtensorIterSlice (Some tm))
  | CtensorIterSlice (Some tm), TmTensor (_, t) -> (
      let iterf tkind i t =
        let _ = apply_args tm [TmConst (fi, CInt i); TmTensor (fi, tkind t)] in
        ()
      in
      try
        ( t
        |> function
        | T.TBootInt t' ->
            Tensor.Uop_barray.iter_slice (iterf (fun t -> T.TBootInt t)) t'
        | T.TBootFloat t' ->
            Tensor.Uop_barray.iter_slice (iterf (fun t -> T.TBootFloat t)) t'
        | T.TBootGen t' ->
            Tensor.Uop_generic.iter_slice (iterf (fun t -> T.TBootGen t)) t' ) ;
        tm_unit
      with Invalid_argument msg -> raise_error fi msg )
  | CtensorIterSlice _, _ ->
      fail_constapp fi
  | CtensorEq (None, None), tm ->
      TmConst (fi, CtensorEq (Some tm, None))
  | CtensorEq (Some tm, None), TmTensor (_, t1) ->
      TmConst (fi, CtensorEq (Some tm, Some t1))
  | CtensorEq (Some tm, Some t1), TmTensor (_, t2) -> (
      let eq wrapx wrapy x y =
        apply_args tm [wrapx x; wrapy y]
        |> function TmConst (_, CBool b) -> b | _ -> fail_constapp fi
      in
      let int_ x = TmConst (fi, CInt x) in
      let float_ x = TmConst (fi, CFloat x) in
      let bool_ x = TmConst (fi, CBool x) in
      match (t1, t2) with
      | T.TBootInt t1', T.TBootInt t2' ->
          let eq = eq int_ int_ in
          bool_ (Tensor.Bop_barray_barray.equal eq t1' t2')
      | T.TBootFloat t1', T.TBootFloat t2' ->
          let eq = eq float_ float_ in
          bool_ (Tensor.Bop_barray_barray.equal eq t1' t2')
      | T.TBootInt t1', T.TBootFloat t2' ->
          let eq = eq int_ float_ in
          bool_ (Tensor.Bop_barray_barray.equal eq t1' t2')
      | T.TBootFloat t1', T.TBootInt t2' ->
          let eq = eq float_ int_ in
          bool_ (Tensor.Bop_barray_barray.equal eq t1' t2')
      | T.TBootGen t1', T.TBootGen t2' ->
          let eq = eq Fun.id Fun.id in
          bool_ (Tensor.Bop_generic_generic.equal eq t1' t2')
      | T.TBootInt t1', T.TBootGen t2' ->
          let eq = eq int_ Fun.id in
          bool_ (Tensor.Bop_barray_generic.equal eq t1' t2')
      | T.TBootFloat t1', T.TBootGen t2' ->
          let eq = eq float_ Fun.id in
          bool_ (Tensor.Bop_barray_generic.equal eq t1' t2')
      | T.TBootGen t1', T.TBootInt t2' ->
          let eq = eq Fun.id int_ in
          bool_ (Tensor.Bop_generic_barray.equal eq t1' t2')
      | T.TBootGen t1', T.TBootFloat t2' ->
          let eq = eq Fun.id float_ in
          bool_ (Tensor.Bop_generic_barray.equal eq t1' t2') )
  | CtensorEq _, _ ->
      fail_constapp fi
  (* MCore intrinsics: Boot parser *)
  | CbootParserTree _, _ ->
      fail_constapp fi
  | CbootParserParseMExprString (None, None), TmRecord (_, r) -> (
    try
      match Record.find (us "0") r with
      | TmConst (_, CBool allow_free) ->
          TmConst (fi, CbootParserParseMExprString (Some allow_free, None))
      | _ ->
          fail_constapp fi
    with Not_found -> fail_constapp fi )
  | CbootParserParseMExprString (Some options, None), TmSeq (fi, seq) ->
      let keywords =
        Mseq.map
          (function
            | TmSeq (_, s) -> tmseq2seq_of_int fi s | _ -> fail_constapp fi )
          seq
      in
      TmConst (fi, CbootParserParseMExprString (Some options, Some keywords))
  | Ctensor2string None, tm ->
      TmConst (fi, Ctensor2string (Some tm))
  | Ctensor2string (Some el2str), TmTensor (_, t) ->
      let to_ustring = function
        | TmSeq (_, tms) ->
            tmseq2ustring fi tms
        | _ ->
            fail_constapp fi
      in
      let el2str x = apply el2str x |> to_ustring in
      ( match t with
      | T.TBootInt t' ->
          Tensor.Uop_barray.to_ustring
            (fun x -> TmConst (fi, CInt x) |> el2str)
            t'
      | T.TBootFloat t' ->
          Tensor.Uop_barray.to_ustring
            (fun x -> TmConst (fi, CFloat x) |> el2str)
            t'
      | T.TBootGen t' ->
          Tensor.Uop_generic.to_ustring el2str t' )
      |> fun str -> TmSeq (fi, ustring2tmseq fi str)
  | Ctensor2string _, _ ->
      fail_constapp fi
  | CbootParserParseMExprString (Some options, Some keywords), TmSeq (fi, seq)
    ->
      let t = parseMExprString options keywords (tmseq2seq_of_int fi seq) in
      TmConst (fi, CbootParserTree t)
  | CbootParserParseMExprString _, _ ->
      fail_constapp fi
  | CbootParserParseMLangString None, TmSeq (fi, seq) ->
      let s = tm_seq2int_seq fi seq in
      let t = parseMLangString s in
      TmConst (fi, CbootParserTree t)
  | CbootParserParseMLangString _, _ ->
      fail_constapp fi
  | CbootParserParseMLangFile None, TmSeq (fi, seq) ->
      let s = tm_seq2int_seq fi seq in
      let t = parseMLangFile s in
      TmConst (fi, CbootParserTree t)
  | CbootParserParseMLangFile _, _ ->
      fail_constapp fi
  | CbootParserParseMCoreFile (None, None), TmRecord (_, r) -> (
    try
      match
        ( Record.find (us "0") r
        , Record.find (us "1") r
        , Record.find (us "2") r
        , Record.find (us "3") r
        , Record.find (us "4") r
        , Record.find (us "5") r )
      with
      | ( TmConst (_, CBool keep_utests)
        , TmConst (_, CBool prune_external_utests)
        , TmSeq (_, externals_exclude)
        , TmConst (_, CBool warn)
        , TmConst (_, CBool eliminate_deadcode)
        , TmConst (_, CBool allow_free) ) ->
          let externals_exclude =
            Mseq.map
              (function
                | TmSeq (_, s) -> tmseq2seq_of_int fi s | _ -> fail_constapp fi
                )
              externals_exclude
          in
          TmConst
            ( fi
            , CbootParserParseMCoreFile
                ( Some
                    ( keep_utests
                    , prune_external_utests
                    , externals_exclude
                    , warn
                    , eliminate_deadcode
                    , allow_free )
                , None ) )
      | _ ->
          fail_constapp fi
    with Not_found -> fail_constapp fi )
  | CbootParserParseMCoreFile (Some prune_arg, None), TmSeq (fi, keywords) ->
      let keywords =
        Mseq.map
          (function
            | TmSeq (_, s) -> tmseq2seq_of_int fi s | _ -> fail_constapp fi )
          keywords
      in
      TmConst (fi, CbootParserParseMCoreFile (Some prune_arg, Some keywords))
  | ( CbootParserParseMCoreFile (Some prune_arg, Some keywords)
    , TmSeq (fi, filename) ) ->
      let filename = tmseq2seq_of_int fi filename in
      let t = parseMCoreFile prune_arg keywords filename in
      TmConst (fi, CbootParserTree t)
  | CbootParserParseMCoreFile _, _ ->
      fail_constapp fi
  | CbootParserGetId, TmConst (fi, CbootParserTree ptree) ->
      TmConst (fi, CInt (getId ptree))
  | CbootParserGetId, _ ->
      fail_constapp fi
  | CbootParserGetTerm None, t ->
      TmConst (fi, CbootParserGetTerm (Some t))
  | ( CbootParserGetTerm (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getTerm ptree n))
  | CbootParserGetTerm (Some _), _ ->
      fail_constapp fi
  | CbootParserGetDecl None, t ->
      TmConst (fi, CbootParserGetDecl (Some t))
  | ( CbootParserGetDecl (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getDecl ptree n))
  | CbootParserGetDecl _, _ ->
      fail_constapp fi
  | CbootParserGetTop None, t ->
      TmConst (fi, CbootParserGetTop (Some t))
  | ( CbootParserGetTop (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getTop ptree n))
  | CbootParserGetTop (Some _), _ ->
      fail_constapp fi
  | CbootParserGetType None, t ->
      TmConst (fi, CbootParserGetType (Some t))
  | ( CbootParserGetType (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getType ptree n))
  | CbootParserGetType (Some _), _ ->
      fail_constapp fi
  | CbootParserGetString None, t ->
      TmConst (fi, CbootParserGetString (Some t))
  | ( CbootParserGetString (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmSeq
        (fi, Mseq.map (fun x -> TmConst (NoInfo, CChar x)) (getString ptree n))
  | CbootParserGetString (Some _), _ ->
      fail_constapp fi
  | CbootParserGetInt None, t ->
      TmConst (fi, CbootParserGetInt (Some t))
  | ( CbootParserGetInt (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CInt (getInt ptree n))
  | CbootParserGetInt (Some _), _ ->
      fail_constapp fi
  | CbootParserGetFloat None, t ->
      TmConst (fi, CbootParserGetFloat (Some t))
  | ( CbootParserGetFloat (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CFloat (getFloat ptree n))
  | CbootParserGetFloat (Some _), _ ->
      fail_constapp fi
  | CbootParserGetListLength None, t ->
      TmConst (fi, CbootParserGetListLength (Some t))
  | ( CbootParserGetListLength (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CInt (getListLength ptree n))
  | CbootParserGetListLength (Some _), _ ->
      fail_constapp fi
  | CbootParserGetConst None, t ->
      TmConst (fi, CbootParserGetConst (Some t))
  | ( CbootParserGetConst (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getConst ptree n))
  | CbootParserGetConst (Some _), _ ->
      fail_constapp fi
  | CbootParserGetPat None, t ->
      TmConst (fi, CbootParserGetPat (Some t))
  | ( CbootParserGetPat (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getPat ptree n))
  | CbootParserGetPat (Some _), _ ->
      fail_constapp fi
  | CbootParserGetInfo None, t ->
      TmConst (fi, CbootParserGetInfo (Some t))
  | ( CbootParserGetInfo (Some (TmConst (fi, CbootParserTree ptree)))
    , TmConst (_, CInt n) ) ->
      TmConst (fi, CbootParserTree (getInfo ptree n))
  | CbootParserGetInfo (Some _), _ ->
      fail_constapp fi
  (* Python intrinsics *)
  | CPy v, t ->
      Pyffi.delta apply fi v t

and pt_seq env ps =
  let rec work env = function
    | h :: ts ->
        let env', h' = pat_transform env h in
        let env'', ts' = work env' ts in
        (env'', h' :: ts')
    | [] ->
        (env, [])
  in
  let env', ps_list' = work env (Mseq.Helpers.to_list ps) in
  (env', Mseq.Helpers.of_list_list ps_list')

and pat_transform (env : (Symb.t * tm) list) (p : pat) =
  let new_sym fi env s x =
    match List.assoc_opt s env with
    | Some (TmVar (_, _, s', _, _)) ->
        (env, s')
    | Some _ ->
        failwith "Should not happen"
    | None ->
        let s' = Symb.gensym () in
        let tvar = TmVar (fi, x, s', false, false) in
        ((s, tvar) :: env, s')
  in
  match p with
  | PatNamed (fi, NameStr (x, s)) ->
      let env', s' = new_sym fi env s x in
      (env', PatNamed (fi, NameStr (x, s')))
  | PatNamed (_, _) as p ->
      (env, p)
  | PatSeqTot (fi, ps) ->
      let env', ps' = pt_seq env ps in
      (env', PatSeqTot (fi, ps'))
  | PatSeqEdge (fi, ps1, NameStr (x, s), ps2) ->
      let env', ps1' = pt_seq env ps1 in
      let env'', ps2' = pt_seq env' ps2 in
      let env''', s' = new_sym fi env'' s x in
      (env''', PatSeqEdge (fi, ps1', NameStr (x, s'), ps2'))
  | PatSeqEdge (fi, ps1, n, ps2) ->
      let env', ps1' = pt_seq env ps1 in
      let env'', ps2' = pt_seq env' ps2 in
      (env'', PatSeqEdge (fi, ps1', n, ps2'))
  | PatRecord (fi, patrec) ->
      let f _ p env = pat_transform env p in
      let env', patrec' = Record.map_fold f patrec env in
      (env', PatRecord (fi, patrec'))
  | PatCon (fi, x, s, p) ->
      let env', p' = pat_transform env p in
      (env', PatCon (fi, x, s, p'))
  | (PatInt (_, _) | PatChar (_, _) | PatBool (_, _)) as t ->
      (env, t)
  | PatAnd (fi, p1, p2) ->
      let env', p1' = pat_transform env p1 in
      let env'', p2' = pat_transform env' p2 in
      (env'', PatAnd (fi, p1', p2'))
  | PatOr (fi, p1, p2) ->
      let env', p1' = pat_transform env p1 in
      let env'', p2' = pat_transform env' p2 in
      (env'', PatOr (fi, p1', p2'))
  | PatNot (fi, p) ->
      let env', p' = pat_transform env p in
      (env', PatNot (fi, p'))

(* Main evaluation loop of a term. Evaluates using big-step semantics *)
and apply (pe : peval) (fiapp : info) (f : tm) (a : tm) : tm =
  match (f, a) with
  (* Closure application *)
  | TmClos (ficlos, _, s, _, t3, env2), a -> (
      if !enable_debug_profiling then (
        let t1 = Time.get_wall_time_ms () in
        let res =
          try eval ((s, a) :: !env2) pe t3
          with e ->
            if !enable_debug_stack_trace then
              uprint_endline (us "TRACE: " ^. info2str fiapp) ;
            raise e
        in
        let t2 = Time.get_wall_time_ms () in
        add_call ficlos (t2 -. t1) ;
        res )
      else
        try eval ((s, a) :: !env2) pe t3
        with e ->
          if !enable_debug_stack_trace then
            uprint_endline (us "TRACE: " ^. info2str fiapp) ;
          raise e )
  (* Constant application using the delta function *)
  | ( TmConst (_, c)
    , ( TmConst (_, _)
      | TmSeq (_, _)
      | TmRecord (_, _)
      | TmConApp (_, _, _, _)
      | TmConDef (_, _, _, _, _)
      | TmNever _
      | TmClos (_, _, _, _, _, _)
      | TmRef (_, _)
      | TmTensor (_, _) ) ) ->
      delta (apply pe) fiapp c a
  (* Symbolic application *)
  | f, a ->
      TmApp (fiapp, f, a)

and scan (env : (Symb.t * tm) list) (t : tm) =
  match t with
  | TmLet (fi, x, s, ty, t1, t2) ->
      (*  printf "TmLet: %s \n" (Ustring.to_utf8 x); *)
      let t1' = scan env t1 in
      TmLet
        ( fi
        , x
        , s
        , ty
        , t1'
        , scan ((s, TmBox (fi, ref (t1', Some env))) :: env) t2 )
  | TmRecLets (fi, lst, t2) ->
      let env_ref = ref env in
      let peval = ref false in
      List.iter
        (fun (_, _, s1, _, t) ->
          match t with
          | TmLam (fi, str, s2, pe, _, tm) ->
              env_ref :=
                (s1, TmClos (fi, str, s2, pe, tm, env_ref)) :: !env_ref
          | _ ->
              peval := true )
        lst ;
      if false then (* if !peval then *)
        TmRecLets (fi, lst, t2) (* TODO: must be fixed *)
      else
        let lst' =
          List.map
            (fun (fi2, x, s, ty, t) -> (fi2, x, s, ty, scan !env_ref t))
            lst
        in
        TmRecLets (fi, lst', scan !env_ref t2)
  | TmMatch (fi, t1, p, t2, t3) ->
      let env', p' = pat_transform env p in
      TmMatch (fi, scan env t1, p', scan env' t2, scan env' t3)
  | TmLam (fi, x, s, pe, ty, t) ->
      (* printf "TmLam: %s \n" (Ustring.to_utf8 x); *)
      let s' = Symb.gensym () in
      let tvar = TmVar (fi, x, s', pe, false) in
      TmLam (fi, x, s', pe, ty, scan ((s, tvar) :: env) t)
  | TmVar (_, _, s, _, _) as t1 -> (
    match List.assoc_opt s env with
    | Some t2 -> (
      match t2 with TmVar (_, _, _, _, _) -> t2 | _ -> t1 )
    | None ->
        t1 )
  | TmPreRun (_, _, t) ->
      eval env pe_init t
  | t ->
      smap_tm_tm (scan env) t

and eval (env : (Symb.t * tm) list) (pe : peval) (t : tm) =
  debug_eval env t ;
  match t with
  (* Variables using symbol bindings. Need to evaluate because fix point. *)
  | TmVar (_, _, s, _, _) -> (
    match List.assoc_opt s env with
    | Some t2 -> (
      match t2 with
      | TmBox (_, b) -> (
        match !b with
        | t, None ->
            t
        | t, Some env' ->
            let t' = eval env' pe t in
            b := (t', None) ;
            t' )
      | _ ->
          t2 )
    | None ->
        t )
  (* Application *)
  | TmApp (fiapp, t1, t2) ->
      let f = eval env pe t1 in
      let a = eval env pe t2 in
      apply pe fiapp f a
  (* Lambda and closure conversions *)
  | TmLam (fi, x, s, pes, _ty, t1) ->
      TmClos (fi, x, s, pes, t1, ref env)
  (* Let *)
  | TmLet (_, _, s, _, t1, t2) ->
      eval ((s, eval env pe t1) :: env) pe t2
  (* Recursive lets *)
  | TmRecLets (fi, lst, t2) ->
      let env_ref = ref env in
      let peval = ref false in
      List.iter
        (fun (_, _, s1, _, t) ->
          match t with
          | TmLam (fi, str, s2, pe, _, tm) ->
              env_ref :=
                (s1, TmClos (fi, str, s2, pe, tm, env_ref)) :: !env_ref
          | _ ->
              peval := true )
        lst ;
      if !peval then
        let f env (fi, x, s, ty, t) =
          let s' = Symb.gensym () in
          let tvar = TmVar (fi, x, s', false, false) in
          let env' = (s, tvar) :: env in
          (env', (fi, x, s', ty, t))
        in
        let env', lst' = List.fold_left_map f env lst in
        let g (fi, x, s, ty, t) = (fi, x, s, ty, eval env' pe t) in
        let lst'' = List.map g lst' in
        TmRecLets (fi, lst'', eval env' pe t2)
      else eval !env_ref pe t2
  (* Constant *)
  | TmConst (_, _) ->
      t
  (* Sequences *)
  | TmSeq (fi, tms) ->
      TmSeq (fi, Mseq.map (eval env pe) tms)
  (* Records *)
  | TmRecord (fi, tms) ->
      TmRecord (fi, Record.map (eval env pe) tms)
  (* Records update *)
  | TmRecordUpdate (fi, t1, l, t2) -> (
    match eval env pe t1 with
    | TmRecord (fi, r) ->
        if Record.mem l r then TmRecord (fi, Record.add l (eval env pe t2) r)
        else
          raise_error fi
            ( "No label '" ^ Ustring.to_utf8 l ^ "' in record "
            ^ Ustring.to_utf8 (ustring_of_tm (TmRecord (fi, r))) )
    | v ->
        raise_error fi
          ( "Cannot update the term. The term is not a record: "
          ^ Ustring.to_utf8 (ustring_of_tm v) ) )
  (* Type (ignore) *)
  | TmType (_, _, _, _, t1) ->
      eval env pe t1
  (* Data constructors *)
  | TmConDef (_, _, _, _, t) ->
      eval env pe t
  (* Constructor application *)
  | TmConApp (fi, x, s, t) ->
      let rhs = eval env pe t in
      ( if !enable_debug_con_shape then
        let shape = shape_str rhs in
        let sym = ustring_of_var ~symbol:!enable_debug_symbol_print x s in
        let info = info2str fi in
        Printf.eprintf "%s:\t%s\t(%s)\n" (Ustring.to_utf8 sym)
          (Ustring.to_utf8 shape) (Ustring.to_utf8 info) ) ;
      TmConApp (fi, x, s, rhs)
  (* Match *)
  | TmMatch (fi, t1, p, t2, t3) -> (
      let _ = fi in
      match try_match env (eval env pe t1) p with
      | Some env ->
          eval env pe t2
      | None ->
          eval env pe t3 )
  (* try 1 --
        let t1' = eval env pe t1 in
      if is_value t1' then
       (match try_match env t1' p with
        | Some env ->
           eval env pe t2
        | None ->
           eval env pe t3 )
     else
       TmMatch(fi, t1', p, eval env pe t2, eval env pe t2)) *)
  (* try 2 --
     let t1' = eval env pe t1 in
     match try_match env t1' p with
      | Some env ->
         eval env pe t2
      | None ->
         if is_value t1' then
           TmMatch(fi, t1', p, eval env pe t2, eval env pe t2)
         else
           eval env pe t3 ) *)
  (* Dive *)
  | TmDive (_, _, t) -> (
    match eval env pe t with
    | TmClos (fi, x, s, _, t, env_ref) ->
        let s' = Symb.gensym () in
        let tvar = TmVar (fi, x, s', false, false) in
        let t' = eval ((s, tvar) :: !env_ref) pe (TmDive (fi, 0, t)) in
        TmClos (fi, x, s', false, t', env_ref)
    | t' ->
        t' )
  (* PreRun *)
  | TmPreRun (_, _, t) ->
      eval env pe t
  (* Box *)
  | TmBox (_, b) -> (
    match !b with
    | t, None ->
        t
    | t, Some env' ->
        let t' = eval env' pe t in
        b := (t', None) ;
        t' )
  (* Unit testing *)
  | TmUtest (fi, t1, t2, tusing, tonfail, tnext) ->
      if !utest then (
        let v1, v2 = (eval env pe t1, eval env pe t2) in
        let equal =
          match tusing with
          | Some t -> (
            match eval env pe (TmApp (fi, TmApp (fi, t, v1), v2)) with
            | TmConst (_, CBool b) ->
                b
            | _ ->
                raise_error fi
                  ( "Invalid equivalence function: "
                  ^ Ustring.to_utf8 (ustring_of_tm t) ) )
          | None ->
              val_equal v1 v2
        in
        if equal then (
          printf "." ;
          utest_ok := !utest_ok + 1 )
        else
          let onfail_str =
            match tonfail with
            | Some tonfail' -> (
              match eval env pe (TmApp (fi, TmApp (fi, tonfail', v1), v2)) with
              | TmSeq (_, tms) ->
                  tmseq2ustring fi tms
              | _ ->
                  raise_error fi
                    ( "Invalid failure function: "
                    ^ Ustring.to_utf8 (ustring_of_tm tonfail') ) )
            | None ->
                unittest_default_onfail v1 v2
          in
          unittest_failed fi onfail_str (Option.map ustring_of_tm tusing) ;
          utest_fail := !utest_fail + 1 ;
          utest_fail_local := !utest_fail_local + 1 ) ;
      eval env pe tnext
  (* Never term *)
  | TmNever fi ->
      raise_error fi
        "Reached a never term, which should be impossible in a well-typed \
         program."
  (* Use *)
  | TmUse (fi, _, _) ->
      raise_error fi "A 'use' of a language was not desugared"
  (* External *)
  | TmExt (_, _, _, _, _, t) ->
      eval env pe t
  (* Only at runtime *)
  | TmClos _ | TmRef _ | TmTensor _ ->
      t

(* Same as eval, but records all toplevel definitions and returns them along
   with the evaluated result *)
let rec eval_toplevel (env : (Symb.t * tm) list) (pe : peval) = function
  | TmLet (_, _, s, _ty, t1, t2) ->
      eval_toplevel ((s, eval env pe t1) :: env) pe t2
  | TmType (_, _, _, _, t1) ->
      eval_toplevel env pe t1
  | TmRecLets (_, lst, t2) ->
      let env_ref = ref env in
      List.iter
        (fun (_, _, s1, _, t) ->
          match t with
          | TmLam (fi, str, s2, pe, _, tm) ->
              env_ref :=
                (s1, TmClos (fi, str, s2, pe, tm, env_ref)) :: !env_ref
          | _ ->
              failwith "Incorrect RecLets" )
        lst ;
      eval_toplevel !env_ref pe t2
  | TmConDef (_, _, _, _, t) ->
      eval_toplevel env pe t
  | ( TmVar _
    | TmLam _
    | TmClos _
    | TmApp _
    | TmConst _
    | TmSeq _
    | TmRecord _
    | TmRecordUpdate _
    | TmConApp _
    | TmMatch _
    | TmUse _
    | TmUtest _
    | TmNever _
    | TmRef _
    | TmTensor _
    | TmDive _
    | TmPreRun _
    | TmBox _
    | TmExt _ ) as t ->
      (env, eval env pe t)
