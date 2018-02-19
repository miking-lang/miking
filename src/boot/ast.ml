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
| Cnot
| Cand  | Cand2  of bool
| Cor   | Cor2   of bool
(* MCore intrinsic: Integer constant and operations *)
| CInt of int
| Cadd  | Cadd2 of int
| Csub  | Csub2 of int
| Cmul  | Cmul2 of int
| Cdiv  | Cdiv2 of int
| Cmod  | Cmod2 of int
| Cneg
| Clt   | Clt2  of int
| Cleq  | Cleq2 of int
| Cgt   | Cgt2  of int
| Cgeq  | Cgeq2 of int
| Ceq   | Ceq2  of int
| Cneq  | Cneq2 of int
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

(* Tells if a variable is a pe variable or if a closure is a pe closure *)
and pemode = bool

(* Term/expression *)
and tm =
| TmVar         of info * ustring * int * pemode
| TmLam         of info * ustring * tm
| TmClos        of info * ustring * tm * env * pemode
| TmApp         of info * tm * tm
| TmConst       of info * const
| TmPEval       of info
| TmIfexp       of info * bool option * tm option
| TmFix         of info

| TmChar        of info * int
| TmExprSeq     of info * tm * tm
| TmUC          of info * ucTree * ucOrder * ucUniqueness
| TmUtest       of info * tm * tm * tm
| TmMatch       of info * tm * case list
| TmNop




(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1


(* Returns the info field from a term *)
let tm_info t =
  match t with
  | TmVar(fi,_,_,_) -> fi
  | TmLam(fi,_,_) -> fi
  | TmClos(fi,_,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmPEval(fi) -> fi
  | TmIfexp(fi,_,_) -> fi
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
