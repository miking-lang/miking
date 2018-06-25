
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   boot.ml is the main entry point for first stage of the
   bootstrapped Miking compiler. The bootstapper is interpreted and
   implemented in OCaml. Note that the Miking bootstrapper
   only implements a subset of the Ragnar language.
*)

open Utils
open Ustring.Op
open Printf
open Ast
open Msg
open Pprint

(* Checks if two types are equal *)
let rec typeeq ty1 ty2 =
  match ty1,ty2 with
  | TyGround(_,g1),TyGround(_,g2) -> g1 = g2
  | TyArrow(_,ty11,ty12),TyArrow(_,ty21,ty22) ->
      typeeq ty11 ty21 &&  typeeq ty21 ty22
  | _ -> false


let type_const c =
  match c with
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_) -> TyGround(NoInfo,GBool)
  | CInt(_) -> TyGround(NoInfo,GInt)


(* -----------
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
*)

  | _ -> failwith "NOT FINISHED"


(* Returns the type of term [t] *)
let rec typeof env t =
  match t with
  | TmVar(fi,s,n,pe) -> failwith "TODO1"
  | TmLam(fi,s,t1) -> failwith "TODO2"
  | TmClos(fi,s,t1,env1,pe) -> failwith "Closure cannot happen"
  | TmApp(fi,t1,t2) -> failwith "TODO3"
  | TmConst(fi,c) -> type_const c
  | TmPEval(fi) -> failwith "TODO5"
  | TmIfexp(fi,t1op,t2op) -> failwith "TODO6"
  | TmFix(fi) -> failwith "TODO7"

  | TmChar(fi,x) -> failwith "TODO8"
  | TmExprSeq(fi,t1,t2) -> failwith "TODO9"
  | TmUC(fi,tree,ord,unique) -> failwith "TODO10"
  | TmUtest(fi,t1,t2,t3) ->
      if typeeq (typeof env t1) (typeof env t2)
      then typeof env t2
      else raise_error fi  (us"The two types " ^. pprint_ty (typeof env t1) ^. us" and " ^.
                            pprint_ty (typeof env t2) ^. us" for the two test expressions are not equal."
                            |> Ustring.to_utf8)
  | TmMatch(fi,t1,cases) -> failwith "TODO12"
  | TmNop -> failwith "TODO12"



let typecheck t =
  let _ = typeof [] t in
  t
