(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg

(* Evaluation environment *)
type env = tm list

(* Partial evaluation environment *)
and penv_part =
| PEnvList of tm list
| PEnvElem of petm

(* Partial evaluation environment *)
and penv = penv_part list


(* Pattern used in match constructs *)
and pattern =
| PatIdent      of info * ustring
| PatChar       of info * int
| PatUC         of info * pattern list * ucOrder * ucUniqueness
| PatBool       of info * bool
| PatInt        of info * int
| PatConcat     of info * pattern * pattern

(* One pattern case *)
and case =
| Case          of info * pattern * tm


(* Tree fore representing universal collection types (UCT) *)
and ucTree =
| UCNode        of ucTree * ucTree
| UCLeaf        of tm list


(* Properties of Universal Collection types *)
and ucOrder = UCUnordered | UCOrdered | UCSorted
and ucUniqueness = UCUnique | UCMultivalued

and const =
(* MCore intrinsic: Boolean constant and operations *)
| CBool of bool
| CBNot
| CBAnd | CBAnd2 of bool
| CBOr  | CBOr2 of bool
(* MCore intrinsic: Integer constant and operations *)
| CInt of int
| CIAdd | CIAdd2 of int
| CISub | CISub2 of int
| CIMul | CIMul2 of int
| CIDiv | CIDiv2 of int
| CIMod | CIMod2 of int
| CINeg
| CILt  | CILt2  of int
| CILeq | CILeq2 of int
| CIGt  | CIGt2  of int
| CIGeq | CIGeq2 of int
| CIEq  | CIEq2  of int
| CINeq | CINeq2 of int
(* MCore control intrinsics *)
| CIF | CIF2 of bool | CIF3 of bool * tm
(* MCore debug and I/O intrinsics *)
| CDStr
| CDPrint
| CPrint
| CArgv
(* MCore unified collection type (UCT) intrinsics *)
| CConcat | CConcat2 of tm

(* Ragnar temp functions for handling polymorphic arguments *)
| CPolyEq  | CPolyEq2  of tm
| CPolyNeq | CPolyNeq2 of tm




(* Term/expression *)
and tm =
| TmVar         of info * ustring * int
| TmLam         of info * ustring * tm
| TmClos        of info * ustring * tm * env
| TmApp         of info * tm * tm
| TmConst       of info * const
| TmPEval       of info
| TmFix         of info

| TmChar        of info * int
| TmExprSeq     of info * tm * tm
| TmUC          of info * ucTree * ucOrder * ucUniqueness
| TmUtest       of info * tm * tm * tm
| TmMatch       of info * tm * case list
| TmNop


(* Term/expression during partial evaluation *)
and petm =
| PESym         of int
| PEClos        of info * ustring * petm * penv
| PEFix         of petm
| PEExp         of tm


(* Generate a constant application term for a specific constant *)
let capp c v = TmApp(NoInfo,TmConst(NoInfo,c),v)

(* Same as above, but for PE term *)
let capp c v = TmApp(NoInfo,TmConst(NoInfo,c),v)

(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1


(* Cons a normal term 't' to a PE environment 'penv' *)
let cons_env t penv = PEnvList([t])::penv

(* Cons a PE term 't' to a PE environment 'penv' *)
let cons_penv t penv = PEnvElem(t)::penv

(* Returns the nth element from a PE environment.
   Assumes that the element exists. *)
let rec nth_penv n penv =
  match penv with
  | PEnvList(t::ts)::rest ->
     if n = 0 then PEExp(t) else nth_penv (n-1) (PEnvList(ts)::rest)
  | PEnvList([])::rest -> nth_penv n rest
  | PEnvElem(t)::rest ->
    if n = 0 then t else nth_penv (n-1) rest
  | [] -> failwith "Out of bound of the penv list"

(* Returns the env version of a penv environment *)
let rec to_env penv =
  match penv with
  | PEnvList(ts)::rest -> List.append ts (to_env rest)
  | PEnvElem(PEExp(t))::rest -> t::(to_env rest)
  | PEnvElem(_)::rest -> failwith "Cannot convert penv to env"
  | [] -> []

(* Returns the penv version of an env environment *)
let to_penv env = [PEnvList(env)]


(* Returns the info field from a term *)
let tm_info t =
  match t with
  | TmVar(fi,_,_) -> fi
  | TmLam(fi,_,_) -> fi
  | TmClos(fi,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmPEval(fi) -> fi
  | TmFix(fi) -> fi

  | TmChar(fi,_) -> fi
  | TmExprSeq(fi,_,_) -> fi
  | TmUC(fi,_,_,_) -> fi
  | TmUtest(fi,_,_,_) -> fi
  | TmMatch(fi,_,_) -> fi
  | TmNop -> NoInfo


type 'a tokendata = {i:info; v:'a}


let ustring2uctm fi str =
  let lst = List.map (fun x -> TmChar(NoInfo,x)) (ustring2list str) in
  TmUC(fi,UCLeaf(lst),UCOrdered,UCMultivalued)
