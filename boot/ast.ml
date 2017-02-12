(* 
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg

type env = tm list

and op = OpAdd  | OpSub | OpMul | OpDiv | OpMod |
         OpLess | OpLessEqual   | OpGreat |
         OpGreatEqual | OpEqual | OpNotEqual |
         OpDprint | OpDBprint
          

and ucType =
  | UCList        of tm list
  | UCNode        of ucType * ucType
    

and ucOrder = UCUnordered | UCOrdered | UCSorted
and ucUniqueness = UCUnique | UCMultivalued

   
and tm = 
  | TmVar         of info * ustring * int  
  | TmLam         of info * ustring * tm
  | TmClos        of info * tm * env
  | TmFix         of info * tm
  | TmApp         of info * tm * tm
  | TmInt         of info * int
  | TmBool        of info * bool
  | TmChar        of info * int
  | TmOp          of info * op * tm * tm
  | TmIf          of info * tm * tm * tm
  | TmSeq         of info * tm * tm
  | TmUC          of info * ucType * ucOrder * ucUniqueness
  | TmUtest       of info * tm * tm * tm
  | TmNop        


let rec ucmap f uc = match uc with
  | UCList(tms) -> UCList(List.map f tms)
  | UCNode(uc1,uc2) -> UCNode(ucmap f uc1, ucmap f uc2)
      
let noidx = -1
      
let tm_info t =
  match t with
    | TmVar(fi,_,_) -> fi
    | TmLam(fi,_,_) -> fi
    | TmClos(fi,_,_) -> fi
    | TmFix(fi,_) -> fi
    | TmApp(fi,_,_) -> fi
    | TmInt(fi,_) -> fi
    | TmBool(fi,_) -> fi
    | TmChar(fi,_) -> fi
    | TmOp(fi,_,_,_) -> fi
    | TmIf(fi,_,_,_) -> fi
    | TmSeq(fi,_,_) -> fi
    | TmUC(fi,_,_,_) -> fi
    | TmUtest(fi,_,_,_) -> fi
    | TmNop -> NoInfo

type 'a tokendata = {i:info; v:'a}
