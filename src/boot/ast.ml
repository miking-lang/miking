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

(* Operands, both unary and binary *)  
and op =
| OpAdd        (* Integer addition *)
| OpSub        (* Integer subtraction *)
| OpMul        (* Integer multiplication *)
| OpDiv        (* Integer division *)
| OpMod        (* Integer modulo *)
| OpLess       (* Less than *)
| OpLessEqual  (* Less than or equal to *)
| OpGreat      (* Greater than *)
| OpGreatEqual (* Greater than or equal to *)
| OpEqual      (* Equal to *)
| OpNotEqual   (* Not equal to *)
| OpDstr       (* Debug string *)
| OpDBstr      (* Debug string, basic *)
| OpDprint     (* Debug print *)
| OpDBprint    (* Debug print, basic *)
| OpPrint      (* Print *)
| OpArgv       (* Program Arguments *)
| OpConcat     (* Concatenation *)

    
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
(* Boolean constant and operations *)
| CBool of bool
| CBNot 
| CBAnd | CBAnd2 of bool
| CBOr  | CBOr2 of bool
(* Integer constant and operations *)
| CInt of int
| CIAdd | CIAdd2 of int
| CISub | CISub2 of int
| CIMul | CIMul2 of int
| CIDiv | CIDiv2 of int
| CIMod | CIMod2 of int
    
    
    
(* Term/expression *)    
and tm = 
| TmVar         of info * ustring * int  
| TmLam         of info * ustring * tm
| TmClos        of info * tm * env
| TmFix         of info * tm
| TmApp         of info * tm * tm
| TmConst       of info * const
   
| TmInt         of info * int
| TmChar        of info * int
| TmOp          of info * op * tm * tm
| TmIf          of info * tm * tm * tm
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
  | TmVar(fi,_,_) -> fi
  | TmLam(fi,_,_) -> fi
  | TmClos(fi,_,_) -> fi
  | TmFix(fi,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
    
  | TmInt(fi,_) -> fi
  | TmChar(fi,_) -> fi
  | TmOp(fi,_,_,_) -> fi
  | TmIf(fi,_,_,_) -> fi
  | TmExprSeq(fi,_,_) -> fi
  | TmUC(fi,_,_,_) -> fi
  | TmUtest(fi,_,_,_) -> fi
  | TmMatch(fi,_,_) -> fi
  | TmNop -> NoInfo

    
type 'a tokendata = {i:info; v:'a}


let ustring2uctm fi str =
  let lst = List.map (fun x -> TmChar(NoInfo,x)) (ustring2list str) in
  TmUC(fi,UCLeaf(lst),UCOrdered,UCMultivalued)


