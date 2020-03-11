
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
  (* MCore intrinsic: unit - no operation *)
  | Cunit -> us"()"
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
  | Carity -> us"arity"
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
  | Cltf(None) -> us"ltf"
  | Cltf(Some(v)) -> us(sprintf "ltf(%f)" v)
  | Cleqf(None) -> us"leqf"
  | Cleqf(Some(v)) -> us(sprintf "leqf(%f)" v)
  | Cgtf(None) -> us"gtf"
  | Cgtf(Some(v)) -> us(sprintf "gtf(%f)" v)
  | Cgeqf(None) -> us"geqf"
  | Cgeqf(Some(v)) -> us(sprintf "geqf(%f)" v)
  | Ceqf(None) -> us"eqf"
  | Ceqf(Some(v)) -> us(sprintf "eqf(%f)" v)
  | Cneqf(None) -> us"neqf"
  | Cneqf(Some(v)) -> us(sprintf "neqf(%f)" v)
  | Cfloorfi -> us"floorfi"
  | Cceilfi -> us"ceilfi"
  | Croundfi -> us"roundfi"
  | CInt2float -> us"int2float"
  | CString2float -> us"string2float"
  (* MCore intrinsic: characters *)
  | CChar(v) -> us"'" ^. list2ustring [v] ^. us"'"
  | CChar2int -> us"char2int"
  | CInt2char -> us"int2char"
  (* MCore intrinsic: sequences *)
  | CSeq(tms) ->
     if List.for_all (fun x -> match x with | TmConst(_,CChar(_)) -> true | _ -> false) tms
     then us"\"" ^. tmlist2ustring NoInfo tms ^. us"\""
     else us"[" ^. Ustring.concat (us",") (List.map pprintME tms) ^. us"]"
  | Cmakeseq(_) -> us"makeseq"
  | Clength -> us"length"
  | Cconcat(_) -> us"concat"
  | Cnth(_) -> us"nth"
  | Ccons(_) -> us"cons"
  | Cslice(_,_) -> us"slice"
  | Creverse -> us"reverse"
  (* MCore records *)
  | CRecord(r) ->
     let contents = Record.fold (fun l v ack -> (l, v)::ack) r [] in
     pprecord contents
  (* MCore debug and stdio intrinsics *)
  | Cprint -> us"print"
  | Cdprint -> us"dprint"
  | CreadFile -> us"readFile"
  | CwriteFile(_) -> us"writeFile"
  | CfileExists -> us"fileExists"
  | CdeleteFile -> us"deleteFile"
  | Cerror -> us"error"
  | CdebugShow -> us"debugShow"
  (* MCore Symbols *)
  | CSymb(id) -> us(sprintf "symb(%d)" id)
  | Cgensym -> us"gensym"
  | Ceqs(_) -> us"eqs"
  (* External pprint TODO: Should not be part of core language *)
  | CExt(v) -> Extpprint.pprint v

(* Pretty print a record *)
and pprecord contents =
  us"{" ^.
    Ustring.concat (us",")
      (List.map (function (l, v) -> l ^. us" = " ^. pprintME v) contents)
    ^. us"}"

and pplabel = function
  | LabIdx i -> Ustring.Op.ustring_of_int i
  | LabStr s -> s

(* Pretty print a term. *)
and pprintME t =
  let rec ppt inside t =
  match t with
  | TmVar(_,x,n) -> varDebugPrint x n
  | TmLam(_,x,ty,t1) -> left inside ^.
      us"lam " ^. x ^. us":" ^. pprint_ty ty ^. us". " ^. ppt false t1 ^. right inside
  | TmClos(_,x,_,t,_) -> left inside ^. us"clos " ^. x ^. us". " ^.
                           ppt false t ^. right inside
  | TmLet(_,x,t1,t2) -> left inside ^. us"let " ^. x ^. us" = " ^. ppt false t1 ^.
                          us" in " ^. ppt false t2 ^. right inside
  | TmRecLets(_,lst,t2) ->
     us"recursive" ^. Ustring.concat (us" ")
               ((List.map (fun (_,x,t) -> us"let " ^. x ^. us" = " ^. ppt false t)) lst)
              ^. us" in " ^. ppt false t2
  | TmApp(_,t1,t2) ->
       left inside ^. ppt true t1  ^. us" " ^. ppt true t2 ^. right inside
  | TmConst(_,c) -> pprint_const c
  | TmIf(_,t1,t2,t3) -> left inside ^. us"if " ^. ppt false t1 ^. us" then " ^.
                          ppt false t2 ^. us" else " ^. ppt false t3 ^.right inside
  | TmFix(_) -> us"fix"
  | TmSeq(_,tms) -> us"[" ^. Ustring.concat (us",") (List.map (ppt false) tms) ^. us"]"
  | TmTuple(_,tms) -> us"(" ^. Ustring.concat (us",") (List.map (ppt false) tms) ^. us")"
  | TmRecord(_, r) -> left inside ^. pprecord r ^. right inside
  | TmProj(_,t,l) -> left inside ^. ppt false t  ^. us"." ^. pplabel l ^. right inside
  | TmRecordUpdate(_,t1,l,t2) -> left inside ^. ppt false t1  ^. us" with " ^. l ^. us" = " ^. ppt false t2 ^. right inside
  | TmCondef(_,s,ty,t) -> left inside ^. us"data " ^. s ^. us" " ^. pprint_ty ty ^.
                        us" in" ^. ppt false t ^. right inside
  | TmConsym(_,s,sym,tmop) -> left inside ^. s ^. us"_" ^. us(sprintf "%d" sym) ^. us" " ^.
                           (match tmop with
                            | Some(t) -> ppt true t
                            | None -> us"") ^. right inside
  | TmMatch(_,t,p,then_,else_) -> left inside ^. us"match " ^. ppt false t ^.
        us" with " ^. pprintPat p ^.
        us" then " ^. ppt false then_ ^.
        us" else " ^. ppt false else_ ^. right inside
  | TmUse(_,l,t) -> us"use " ^. l ^. us" in " ^. ppt false t
  | TmUtest(_,t1,t2,_) -> us"utest " ^. ppt false t1  ^. us" " ^. ppt false t2
  in ppt false t

and pprintPat p =
  let rec ppp inside = function
    | PatNamed(_,x) -> x
    | PatTuple(_,ps) -> us"(" ^. Ustring.concat (us",") (List.map (ppp false) ps) ^. us")"
    | PatCon(_,x,n,p) ->
       left inside ^.
       varDebugPrint x n ^. ppp true p ^.
       right inside
    | PatInt(_,i) -> Ustring.Op.ustring_of_int i
    | PatChar(_,c) -> us"'" ^. list2ustring [c] ^. us"'"
    | PatBool(_,b) -> Ustring.Op.ustring_of_bool b
    | PatUnit _ -> us"()"
  in ppp false p

(* Pretty prints the environment *)
and pprint_env env =
  us"[" ^. (List.mapi (fun i t -> us(sprintf " %d -> " i) ^. pprintME t) env
            |> Ustring.concat (us",")) ^. us"]"


and pprint_ty ty =
  let ppt ty =
  match ty with
  | TyUnit -> us"()"
  | TyDyn   -> us"Dyn"
  | TyBool  -> us"Bool"
  | TyInt   -> us"Int"
  | TyFloat -> us"Float"
  | TyChar -> us"Char"
  | TyArrow(ty1,ty2) -> us"(" ^. pprint_ty ty1 ^. us"," ^. pprint_ty ty2 ^. us")"
  | TySeq(ty1) -> if ty1 = TyChar then us"String"
                  else us"[" ^. pprint_ty ty1 ^. us"]"
  | TyTuple tys ->
     us"(" ^. Ustring.concat (us",") (List.map pprint_ty tys) ^. us")"
  | TyRecord tys ->
     us"{" ^. Ustring.concat (us",") (List.map pprint_ty_label tys) ^. us"}"
  | TyCon(s) -> s
  in
    ppt ty

and pprint_ty_label = function
  | (l, ty) -> l ^. us" : " ^. pprint_ty ty

(* TODO: Print mlang part as well*)
and pprintML tml =
  match tml with
  | Program(_,_,t) -> pprintME t
