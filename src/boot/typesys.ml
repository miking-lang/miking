
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
let rec tyequal ty1 ty2 =
  match ty1,ty2 with
  | TyGround(_,g1),TyGround(_,g2) -> g1 = g2
  | TyArrow(_,ty11,ty12),TyArrow(_,ty21,ty22) ->
      tyequal ty11 ty21 &&  tyequal ty21 ty22
  | _ -> false

(* Returns the type of a constant value *)
let type_const c =
  let tyarr t1 t2 = TyArrow(NoInfo,t1,t2) in
  let tybool = TyGround(NoInfo,GBool) in
  let tyint =  TyGround(NoInfo,GInt) in
  let tyfloat =  TyGround(NoInfo,GFloat) in
  match c with
  (* MCore intrinsic: Boolean constant and operations *)
  | CBool(_) -> tybool
  | Cnot -> tyarr tybool tybool
  | Cand(None) | Cor(None) -> tyarr tybool (tyarr tybool tybool)
  | Cand(_) | Cor(_) -> tyarr tybool tybool
(* MCore intrinsic: Integer constant and operations *)
  | CInt(_) -> tyint
  | Caddi(None) | Csubi(None) | Cmuli(None)| Cdivi(None) | Cmodi(None)
      -> tyarr tyint (tyarr tyint tyint)
  | Caddi(_) | Csubi(_) | Cmuli(_)| Cdivi(_) | Cmodi(_) | Cnegi
      -> tyarr tyint tyint
  | Clti(None) | Cleqi(None) | Cgti(None)  | Cgeqi(None) | Ceqi(None)
               | Cneqi(None) | Cslli(None) | Csrli(None) | Csrai(None)
      -> tyarr tyint (tyarr tyint tybool)
  | Clti(_) | Cleqi(_) | Cgti(_)  | Cgeqi(_) | Ceqi(_)
            | Cneqi(_) | Cslli(_) | Csrli(_) | Csrai(_)
      -> tyarr tyint tybool
(* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_) -> tyfloat
  | Caddf(None) | Csubf(None) | Cmulf(None) | Cdivf(None)
      -> tyarr tyfloat (tyarr tyfloat tyfloat)
  | Caddf(_) | Csubf(_) | Cmulf(_) | Cdivf(_) | Cnegf
      -> tyarr tyfloat tyfloat
(* Mcore intrinsic: Polymorphic integer and floating-point numbers *)
  | Cadd(_) | Csub(_) | Cmul(_) | Cdiv(_) | Cneg
(* MCore debug and I/O intrinsics *)
  | CDStr | CDPrint | CPrint | CArgv
(* MCore unified collection type (UCT) intrinsics *)
  | CConcat(_)
(* Ragnar temp functions for handling polymorphic arguments *)
  | CPolyEq(_)
  | CPolyNeq(_)
(* Atom - an untyped lable that can be used to implement domain specific constructs *)
  | CAtom(_,_)
    -> error NoInfo (us"The constant is not supported in the current type system")


(* Returns the type of term [t] *)
let rec typeof tyenv t =
  match t with
  | TmVar(fi,s,n,pe) -> (
    try (List.find (fun (x,_) -> s =. x) tyenv) |> snd
    with Not_found -> error fi (us"Variable '" ^. s ^. us"' cannot be found."))
  | TmLam(fi,s,ty1,t1) ->
      let ty2 = typeof ((s,ty1)::tyenv) t1 in
      TyArrow(fi,ty1,ty2)
  | TmClos(fi,s,ty,t1,env1,pe) -> failwith "Closure cannot happen"
  | TmApp(fi,TmLam(fi2,s,TyUndef,t1),t2) ->
      let ty2 = typeof tyenv t2 in
      typeof ((s,ty2)::tyenv) t1
  | TmApp(fi,t1,t2) -> (
    match typeof tyenv t1,typeof tyenv t2 with
    | TyArrow(fi2,ty11,ty12),ty11' ->
        if tyequal ty11 ty11' then ty12
        else error (tm_info t2)
          (us"Type application mismatch. Applied an expression of type " ^.
           pprint_ty ty11' ^. us", but expected an expression of type " ^.
           pprint_ty ty11 ^. us".")
    | ty1,ty2 -> error (tm_info t1)
          (us"Type application mismatch. Cannot apply an expression of " ^.
           us"type " ^. pprint_ty ty2 ^. us" to an expression of type " ^.
           pprint_ty ty1 ^. us".")
  )
  | TmConst(fi,c) -> type_const c
  | TmPEval(fi) -> failwith "TODO5"
  | TmIfexp(fi,t1op,t2op) -> failwith "TODO6"
  | TmFix(fi) -> failwith "TODO7"

  | TmChar(fi,x) -> failwith "TODO8"
  | TmExprSeq(fi,t1,t2) -> failwith "TODO9"
  | TmUC(fi,tree,ord,unique) -> failwith "TODO10"
  | TmUtest(fi,t1,t2,t3) ->
      if tyequal (typeof tyenv t1) (typeof tyenv t2)
      then typeof tyenv t3
      else error fi  (us"The two test expressions have differnt types: " ^.
                        pprint_ty (typeof tyenv t1) ^. us" and " ^.
                        pprint_ty (typeof tyenv t2) ^. us".")
  | TmMatch(fi,t1,cases) -> failwith "TODO12"
  | TmNop -> TyGround(NoInfo,GVoid)


(* Main external function for type checking *)
let typecheck builtin t =
  (* Remove constant that are not supported by the type system *)
  let lst = List.filter
    (fun (x,_) ->
      match x with
      | "add" | "sub" | "div" | "mul" | "neg" |
        "dstr" | "dprint" | "print" | "argv" | "concat" -> false
      | _ -> true) builtin in
  (* Create type environment for builtins *)
  let tyenv = List.map (fun (x,c) -> (us x, type_const c)) lst in
  (* Type check *)
  let _ = typeof tyenv t in
  t
