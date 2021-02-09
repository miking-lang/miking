(* 
 * Miking is licensed under the MIT license.
 * Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Intrinsics
open Ustring.Op

(* Terms *)
let idTmVar     = 100
let idTmLam     = 101
let idTmLet     = 102
let idTmType    = 103
let idTmRecLets = 104
let idTmApp     = 105
let idTmConst   = 106
let idTmSeq     = 107
let idTmRecord  = 108
let idTmRecordUpdate = 109
let idTmCondef  = 110
let idTmConapp  = 111
let idTmMatch   = 112
let idTmUse     = 113
let idTmUtest   = 114
let idTmNever   = 115
let idTmClos    = 116
let idTmFix     = 117

(* Types *)
let idTyUnknown = 200
let idTyBool    = 201
let idTyInt     = 202
let idTyFloat   = 203
let idTyChar    = 204
let idTyArrow   = 205
let idTySeq     = 206
let idTyRecord  = 207
let idTyVariant = 208
let idTyVar     = 209
let idTyApp     = 210

    
let sym = Symb.gensym() 
let parseMExprString str = TmLam(NoInfo, us"x", sym, TyUnknown(NoInfo), TmVar(NoInfo, str, sym))


(* Returns a tuple with the following elements
   1. ID field 
   2. Info field
   3. List of types
   4. List of terms
   5. List of strings
   6. List of integers
 *)
let getData = function
  | PTreeTm(TmVar(fi,x,_)) -> (idTmVar,fi,[],[],[x],[])
  | PTreeTm(TmLam(fi,x,_,ty,t)) -> (idTmLam,fi,[ty],[t],[x],[])
  | PTreeTm(TmLet(fi,x,_,ty,t1,t2)) -> (idTmLet,fi,[ty],[t1;t2],[x],[])
  | PTreeTm(TmType(fi,x,_,ty,t)) -> (idTmType,fi,[ty],[t],[x],[])
  (* | WrapTm(TmRecLets of info * (info * ustring * Symb.t * ty * tm) list * tm *)
  | PTreeTm(TmApp(fi,t1,t2)) -> (idTmApp,fi,[],[t1;t2],[],[])
  | _ -> failwith "TODO"

let getId t = let (id,_,_,_,_,_) = getData t in id

let getTerm t n =
  let (_,_,_,lst,_,_) = getData t in PTreeTm(List.nth lst n)

let getString t n =
  let (_,_,_,_,lst,_) = getData t in List.nth lst n

let getInt t n =
  let (_,_,_,_,_,lst) = getData t in List.nth lst n










