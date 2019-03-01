(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg




let utest = ref false           (* Set to true if unit testing is enabled *)
let utest_ok = ref 0            (* Counts the number of successful unit tests *)
let utest_fail = ref 0          (* Counts the number of failed unit tests *)
let utest_fail_local = ref 0    (* Counts local failed tests for one file *)


(* Either an int, a float, or none *)
type intfloatoption =
| TInt   of int
| TFloat of float
| TNone

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
(* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
| Cadd   of intfloatoption
| Csub   of intfloatoption
| Cmul   of intfloatoption
| Cdiv   of intfloatoption
| Cneg
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

(* Atom - an untyped lable that can be used to implement
   domain specific constructs *)
| CAtom of sid * tm list

(* Tells if a variable is a pe variable or if a closure is a pe closure *)
and pemode = bool



(* Terms / expressions *)
and tm =
| TmVar         of info * ustring * int * pemode              (* Variable *)
| TmLam         of info * ustring * ty * tm                   (* Lambda abstraction *)
| TmClos        of info * ustring * ty * tm * env * pemode    (* Closure *)
| TmApp         of info * tm * tm                             (* Application *)
| TmConst       of info * const                               (* Constant *)
| TmDive        of info                                       (* Dive operator *)
| TmIfexp       of info * bool option * tm option
| TmFix         of info                                       (* Fix point *)
| TmTyLam       of info * ustring * kind * tm                 (* Type abstraction *)
| TmTyApp       of info * tm * ty                             (* Type application *)

(*
| TmMatch       of info * tm * tm                             (* Match expression *)
| TmCase        of info * ustring * (ustring * int) list * tm (* Case expression *)
| TmCaseComp    of info * tm * tm                             (* Case composition *)
| TmCon         of info * ustring * tm list                   (* Data constructor term *)


| TmDefType     of info * ustring * tm                        (* Type definition *)
| TmDefCon      of info * ty * tm                             (* Data constructor definition *)
 *)

| TmChar        of info * int
| TmUC          of info * ucTree * ucOrder * ucUniqueness
| TmUtest       of info * tm * tm * tm
| TmNop

(* Ground types *)
and groundty = GBool | GInt | GFloat | GVoid

(* Types *)
and ty =
| TyGround      of info * groundty                            (* Ground types *)
| TyArrow       of info * ty * ty                             (* Function type *)
| TyVar         of info * ustring * int                       (* Type variable *)
| TyAll         of info * ustring * kind * ty                 (* Universal type *)
| TyLam         of info * ustring * kind * ty                 (* Type-level function *)
| TyApp         of info * ty * ty                             (* Type-level application *)
(*| TyCase        of info * ustring * ty list * ustring         (* Case type *) *)
| TyDyn                                                       (* Dynamic type *)


(* Kinds *)
and kind =
| KindStar      of info                                       (* Kind of proper types *)
| KindArrow     of info * kind * kind                         (* Kind of type-level functions *)


(* Variable type. Either a type variable or a term variable *)
and vartype =
| VarTy         of ustring
| VarTm         of ustring

and tyenvVar =
| TyenvTmvar    of ustring * ty
| TyenvTyvar    of ustring * kind                  (* Boolean states if it is
                                                       a forall binding *)

(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1

(* Extract the variable name from a tyenvVar type *)
let envVar tyvar =
  match tyvar with TyenvTmvar(x,_) | TyenvTyvar(x,_) -> x

(* Returns the info field from a term *)
let tm_info t =
  match t with
  | TmVar(fi,_,_,_) -> fi
  | TmLam(fi,_,_,_) -> fi
  | TmClos(fi,_,_,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmDive(fi) -> fi
  | TmIfexp(fi,_,_) -> fi
  | TmFix(fi) -> fi
  | TmTyLam(fi,_,_,_) -> fi
  | TmTyApp(fi,_,_) -> fi

  | TmChar(fi,_) -> fi
  | TmUC(fi,_,_,_) -> fi
  | TmUtest(fi,_,_,_) -> fi
  | TmNop -> NoInfo


(* Returns the info field from a type *)
let ty_info t =
  match t with
  | TyGround(fi,_) -> fi
  | TyArrow(fi,_,_) -> fi
  | TyVar(fi,_,_) -> fi
  | TyAll(fi,_,_,_) -> fi
  | TyLam(fi,_,_,_) -> fi
  | TyApp(fi,_,_) -> fi
  | TyDyn -> NoInfo         (* Used when deriving types for let-expressions *)



(* Returns the info field from a kind *)
let kind_info k =
  match k with
  | KindStar(fi) -> fi
  | KindArrow(fi,_,_) -> fi


(* Returns the number of expected arguments *)
let arity c =
  match c with
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
  (* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
  | Cadd(TNone) -> 2  | Cadd(_)        -> 1
  | Csub(TNone) -> 2  | Csub(_)        -> 1
  | Cmul(TNone) -> 2  | Cmul(_)        -> 1
  | Cdiv(TNone) -> 2  | Cdiv(_)        -> 1
  | Cneg        -> 1
  (* MCore debug and I/O intrinsics *)
  | CDStr       -> 1
  | CDPrint     -> 1
  | CPrint      -> 1
  | CArgv       -> 1
  (* MCore unified collection type (UCT) intrinsics *)
  | CConcat(None)  -> 2  | CConcat(Some(_))  -> 1
  (* Ragnar temp functions for handling polymorphic arguments *)
  | CPolyEq(None)  -> 2  | CPolyEq(Some(_))  -> 1
  | CPolyNeq(None) -> 2  | CPolyNeq(Some(_)) -> 1
  (* Atom - an untyped lable that can be used to implement
     domain specific constructs *)
  | CAtom(_,_)     -> 0


type 'a tokendata = {i:info; v:'a}


let ustring2uctm fi str =
  let lst = List.map (fun x -> TmChar(NoInfo,x)) (ustring2list str) in
  TmUC(fi,UCLeaf(lst),UCOrdered,UCMultivalued)
