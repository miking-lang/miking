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
(* MCore intrinsic: no operation *)
| Cnop
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
| Carity
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
(* MCore intrinsic: sequences *)
| CSeq     of tm list
| Cmakeseq of int option
| Cconcat  of (tm list) option
| Cnth     of (tm list) option
| Ccons    of tm option
| Cslice   of (tm list) option * int option
| Creverse
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
| TmLet         of info * ustring * tm * tm           (* Let *)
| TmApp         of info * tm * tm                     (* Application *)
| TmConst       of info * const                       (* Constant *)
| TmIf          of info * tm * tm * tm                (* If expression *)
| TmFix         of info                               (* Fix point *)
| TmUtest       of info * tm * tm * tm
(* TODO: TmData  of info * ustring *)
(* TODO: TmCon   of info * const * tm list *)
(* TODO: TmMatch of info * tm * const * ustring list * tm * tm *)


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
  | TmLet(fi,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmIf(fi,_,_,_) -> fi
  | TmFix(fi) -> fi
  | TmUtest(fi,_,_,_) -> fi






type 'a tokendata = {i:info; v:'a}
