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
(* MCore debug and I/O intrinsics *)
| CDStr
| CDPrint
| CPrint
| CArgv
(* MCore unified collection type (UCT) intrinsics *)
| CConcat of tm option

(* Ragnar temp functions for handling polymorphic arguments *)
| CPolyEq  of tm option
| CPolyNeq of tm option

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
