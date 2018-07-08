
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
  | TyVar(_,_,n1),TyVar(_,_,n2) -> n1 = n2
  | TyAll(_,x1,ty1),TyAll(_,x2,ty2) -> tyequal ty1 ty2
  | TyUndef,TyUndef -> true
  | TyGround(_,_), _ | _,TyGround(_,_) -> false
  | TyArrow(_,_,_), _ | _,TyArrow(_,_,_) -> false
  | TyVar(_,_,_), _ | _,TyVar(_,_,_) -> false
  | TyAll(_,_,_), _ | _,TyAll(_,_,_) -> false

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


(* Perform index shifting, as part of the capture free type substitution *)
let rec tyShift d c ty =
  match ty with
  | TyGround(fi,gt) -> ty
  | TyArrow(fi,ty1,ty2) -> TyArrow(fi,tyShift d c ty1, tyShift d c ty2)
  | TyVar(fi,x,k) -> TyVar(fi,x,if k < c then k else k + d)
  | TyAll(fi,x,ty2) -> TyAll(fi,x, tyShift d (c+1) ty2)
  | TyUndef -> TyUndef


(* Substitutes type [tys] in ty *)
let tySubst tys ty =
  let rec subst j s ty =
    (match ty with
    | TyGround(fi,gt) -> ty
    | TyArrow(fi,ty1,ty2) -> TyArrow(fi,subst j s ty1, subst j s ty2)
    | TyVar(fi,x,k) -> if k = j then s else TyVar(fi,x,k)
    | TyAll(fi,x,ty2) ->
      let _ = if tyequal s (tyShift 1 0 s) then printf "** EQ **\n" else printf "** NOTEQ **\n" in
      TyAll(fi,x, subst (j+1) (tyShift 1 0 s) ty2)
    | TyUndef -> TyUndef)
  in
    subst 0 tys ty

(* Returns the type of term [t]
   The type environment [tyenv] is list with elements of type [tyenvVar] *)
let rec typeof tyenv t =
  match t with
  | TmVar(fi,x,n,pe) ->
      (match List.nth_opt tyenv n with
       | Some(TyenvTmvar(y,ty1)) ->
(*
       printf "------------ VAR START ------ \n";
       uprint_endline (us"** ty1: " ^. (pprint_ty ty1));
       uprint_endline (us"** ty1 after shift: " ^. (pprint_ty (tyShift (n+1) 0 ty1)));
       printf "------------ VAR END -------- \n";
*)
       tyShift (n+1) 0 ty1  (* Get types at correct index *)
       | _ -> error fi (us"Variable '" ^. x ^. us"' cannot be found."))
  | TmLam(fi,x,ty1,t1) ->
    let ty2 = typeof (TyenvTmvar(x,ty1)::tyenv) t1 in
(*
      printf "------------ LAM START ------ \n";
      uprint_endline (us"** ty2: " ^. (pprint_ty ty2));
      uprint_endline (us"** ty2subst: " ^. (pprint_ty (tyShift (-1) 0 ty2)));
      printf "------------ LAM END -------- \n";
*)
      TyArrow(fi,ty1,tyShift (-1) 0 ty2)
  | TmClos(fi,s,ty,t1,env1,pe) -> failwith "Closure cannot happen"
  | TmApp(fi,TmLam(fi2,x,TyUndef,t1),t2) ->
      let ty2 = typeof tyenv t2 in
      typeof (TyenvTmvar(x,ty2)::tyenv) t1
  | TmApp(fi,t1,t2) -> (
    match typeof tyenv t1,typeof tyenv t2 with
    | TyArrow(fi2,ty11,ty12),ty11' ->
(*
      printf "------------ APP START ------ \n";
      uprint_endline (us"** ty1: " ^. (pprint_ty (TyArrow(fi2,ty11,ty12))));
      uprint_endline (us"** ty2: " ^. (pprint_ty ty11'));
      printf "------------ APP END -------- \n";
*)
        if tyequal ty11 ty11' then ty12
        else error (tm_info t2)
          (us"Function application type mismatch. Applied an expression of type " ^.
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
  | TmTyLam(fi,x,t1) ->
      let ty2 = typeof (TyenvTyvar(x)::tyenv) t1 in
      TyAll(fi,x,ty2)
  | TmTyApp(fi,t1,ty1) ->
     (match typeof (tyenv) t1 with
      | TyAll(fi2,_,ty2) ->  tySubst ty1 ty2
(*
        uprint_endline (us"** tm: " ^. (pprint true t1));
        uprint_endline (us"** ty1: " ^. (pprint_ty ty1));
        uprint_endline (us"** ty2: " ^. (pprint_ty ty2));
        let a = tySubst ty1 ty2 in
        uprint_endline (us"** tysubst: " ^. (pprint_ty a));
          a
*)
      | ty -> error (tm_info t1)
             (us"Type application expects an universal type, but found " ^.
              pprint_ty ty ^. us"."))
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


(* Erase type abstractions and applications *)
let rec erase t =
  let eraseOp op = match op with | None -> None | Some(t) -> Some(erase t) in
  match t with
  | TmVar(fi,x,n,pe) -> t
  | TmLam(fi,x,ty1,t1) -> TmLam(fi,x,ty1,erase t1)
  | TmClos(fi,s,ty,t1,env1,pe) -> failwith "Closer should not exist during erase."
  | TmApp(fi,t1,t2) -> TmApp(fi, erase t1, erase t2)
  | TmConst(fi,c) -> t
  | TmPEval(fi) -> t
  | TmIfexp(fi,op1,t2op) -> TmIfexp(fi, op1, eraseOp t2op)
  | TmFix(fi) -> t
  | TmTyLam(fi,x,t1) -> TmLam(fi,us"_",TyGround(NoInfo,GVoid),erase t1)
  | TmTyApp(fi,t1,ty1) -> TmApp(fi,erase t1,TmNop)
  | TmChar(fi,x) -> t
  | TmExprSeq(fi,t1,t2) -> TmExprSeq(fi, erase t1, erase t2)
  | TmUC(fi,tree,ord,unique) -> t
  | TmUtest(fi,t1,t2,t3) -> TmUtest(fi, erase t1, erase t2, erase t3)
  | TmMatch(fi,t1,cases) -> t (* TODO if needed *)
  | TmNop -> t


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
  let tyenv = List.map (fun (x,c) -> TyenvTmvar(us x, type_const c)) lst in
  (* Type check *)
  let _ = typeof tyenv t in
  t
