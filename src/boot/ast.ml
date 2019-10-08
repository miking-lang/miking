(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg


(* Debug options *)
let enable_debug_eval = false
let enable_debug_eval_env = false
let enable_debug_after_parse = false
let enable_debug_after_debruijn = false
let enable_debug_after_erase = false



let utest = ref false           (* Set to true if unit testing is enabled *)
let utest_ok = ref 0            (* sCounts the number of successful unit tests *)
let utest_fail = ref 0          (* Counts the number of failed unit tests *)
let utest_fail_local = ref 0    (* Counts local failed tests for one file *)


(* Evaluation environment *)
type env = tm list


and const =
(* MCore intrinsic: Boolean constant and operations *)
| CBool of bool
| Cnot
| Cand  of bool option
| Cor   of bool option
(* MCore intrinsic: Integer constant and operations *)
| CInt  of int
| Caddi of int option
| Csubi of int option
| Cmuli of int option
| Cdivi of int option
| Cmodi of int option
| Cnegi
| Clti  of int option
| Cleqi of int option
| Cgti  of int option
| Cgeqi of int option
| Ceqi  of int option
| Cneqi of int option
| Cslli of int option
| Csrli of int option
| Csrai of int option
(* MCore intrinsic: Floating-point number constant and operations *)
| CFloat of float
| Caddf  of float option
| Csubf  of float option
| Cmulf  of float option
| Cdivf  of float option
| Cnegf
(* MCore intrinsic: characters *)
| CChar  of int
| CChar2int
| CInt2char
(* MCore debug and I/O intrinsics *)
| CDPrint
(* TODO: CSeq *)
(* TODO: CData *)

(* Terms in MLang *)
and cdecl   = CDecl   of info * ustring * ty list
and param   = Param   of info * ustring * ty
and pattern = Pattern of info * const * ustring list
and decl = (* TODO: Local? *)
| Data  of info * ustring * cdecl list
| Inter of info * ustring * param list * (pattern * tm) list

and mlang   = Lang    of info * ustring * ustring list * decl list
and program = Program of info * mlang list * tm

(* Terms in MExpr *)
and tm =
| TmVar         of info * ustring * int               (* Variable *)
| TmLam         of info * ustring * ty * tm           (* Lambda abstraction *)
| TmClos        of info * ustring * ty * tm * env     (* Closure *)
| TmApp         of info * tm * tm                     (* Application *)
| TmConst       of info * const                       (* Constant *)
| TmFix         of info                               (* Fix point *)
| TmUtest       of info * tm * tm * tm
(* TODO: TmData  of info * ustring *)
(* TODO: TmCon   of info * const * tm list *)
(* TODO: TmMatch of info * tm * const * ustring list * tm * tm *)
| TmNop


(* Types *)
and ty =
| TyDyn                                               (* Dynamic type *)


(* Variable type *)
and vartype =
| VarTm         of ustring


(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1


(* Returns the info field from a term *)
let tm_info = function
  | TmVar(fi,_,_) -> fi
  | TmLam(fi,_,_,_) -> fi
  | TmClos(fi,_,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmFix(fi) -> fi
  | TmUtest(fi,_,_,_) -> fi
  | TmNop -> NoInfo



(* Returns the number of expected arguments *)
let arity = function
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_)    -> 0
  | Cnot        -> 1
  | Cand(None)  -> 2  | Cand(Some(_))  -> 1
  | Cor(None)   -> 2  | Cor(Some(_))   -> 1
  (* MCore intrinsic: Integer constant and operations *)
  | CInt(_)     -> 0
  | Caddi(None) -> 2  | Caddi(Some(_)) -> 1
  | Csubi(None) -> 2  | Csubi(Some(_)) -> 1
  | Cmuli(None) -> 2  | Cmuli(Some(_)) -> 1
  | Cdivi(None) -> 2  | Cdivi(Some(_)) -> 1
  | Cmodi(None) -> 2  | Cmodi(Some(_)) -> 1
  | Cnegi       -> 1
  | Clti(None)  -> 2  | Clti(Some(_))  -> 1
  | Cleqi(None) -> 2  | Cleqi(Some(_)) -> 1
  | Cgti(None)  -> 2  | Cgti(Some(_))  -> 1
  | Cgeqi(None) -> 2  | Cgeqi(Some(_)) -> 1
  | Ceqi(None)  -> 2  | Ceqi(Some(_))  -> 1
  | Cneqi(None) -> 2  | Cneqi(Some(_)) -> 1
  | Cslli(None) -> 2  | Cslli(Some(_)) -> 1
  | Csrli(None) -> 2  | Csrli(Some(_)) -> 1
  | Csrai(None) -> 2  | Csrai(Some(_)) -> 1
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_)   -> 0
  | Caddf(None) -> 2  | Caddf(Some(_)) -> 1
  | Csubf(None) -> 2  | Csubf(Some(_)) -> 1
  | Cmulf(None) -> 2  | Cmulf(Some(_)) -> 1
  | Cdivf(None) -> 2  | Cdivf(Some(_)) -> 1
  | Cnegf       -> 1
  (* MCore intrinsic: characters *)
  | CChar(_)    -> 0
  | CChar2int   -> 1
  | CInt2char   -> 1
  (* MCore debug and I/O intrinsics *)
  | CDPrint     -> 1



type 'a tokendata = {i:info; v:'a}
