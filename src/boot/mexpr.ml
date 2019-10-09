
(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ustring.Op
open Msg
open Ast
open Pprint
open Printf

(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  [("nop",Cnop);
   ("not",Cnot);("and",Cand(None));("or",Cor(None));
   ("addi",Caddi(None));("subi",Csubi(None));("muli",Cmuli(None));
   ("divi",Cdivi(None));("modi",Cmodi(None));("negi",Cnegi);
   ("lti",Clti(None));("leqi",Cleqi(None));("gti",Cgti(None));("geqi",Cgeqi(None));
   ("eqi",Ceqi(None));("neqi",Cneqi(None));
   ("slli",Cslli(None));("srli",Csrli(None));("srai",Csrai(None));
   ("arity",Carity);
   ("addf",Caddf(None));("subf",Csubf(None));("mulf",Cmulf(None));
   ("divf",Cdivf(None));("negf",Cnegf);
   ("char2int",CChar2int);("int2char",CInt2char);
   ("makeseq",Cmakeseq(None)); ("concat",Cconcat(None));
   ("nth",Cnth(None)); ("cons",Ccons(None));
   ("slice",Cslice(None,None)); ("reverse",Creverse)
  ]



(* Returns the number of expected arguments of a constant *)
let arity = function
  (* MCore intrinsic: no operation *)
  | Cnop        -> 0
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
  | Carity      -> 1
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(_)   -> 0
  | Caddf(None) -> 2  | Caddf(Some(_)) -> 1
  | Csubf(None) -> 2  | Csubf(Some(_)) -> 1
  | Cmulf(None) -> 2  | Cmulf(Some(_)) -> 1
  | Cdivf(None) -> 2  | Cdivf(Some(_)) -> 1
  | Cnegf       -> 1
  (* MCore intrinsic: characters *)
  | CChar(_)    -> 0
  | CChar2int   -> 1
  | CInt2char   -> 1
  (* MCore intrinsic: sequences *)
  | CSeq(_)           -> 0
  | Cmakeseq(None)    -> 2 | Cmakeseq(Some(_)) -> 1
  | Cconcat(None)     -> 2 | Cconcat(Some(_)) -> 1
  | Cnth(None)        -> 2 | Cnth(Some(_)) -> 1
  | Ccons(None)       -> 2 | Ccons(Some(_)) -> 1
  | Cslice(None,None) -> 3 | Cslice(Some(_),None) -> 2 | Cslice(_,Some(_)) -> 1
  | Creverse          -> 1
  (* MCore debug and I/O intrinsics *)
  | CDPrint     -> 1



let fail_constapp fi = raise_error fi "Incorrect application "


(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta fi c v  =
    match c,v with
    (* MCore intrinsic: no operation *)
    | Cnop,t -> fail_constapp (tm_info t)
    (* MCore boolean intrinsics *)
    | CBool(_),t -> fail_constapp (tm_info t)

    | Cnot,TmConst(fi,CBool(v)) -> TmConst(fi,CBool(not v))
    | Cnot,t -> fail_constapp (tm_info t)

    | Cand(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cand(Some(v)))
    | Cand(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 && v2))
    | Cand(None),t | Cand(Some(_)),t  -> fail_constapp (tm_info t)

    | Cor(None),TmConst(fi,CBool(v)) -> TmConst(fi,Cor(Some(v)))
    | Cor(Some(v1)),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 || v2))
    | Cor(None),t | Cor(Some(_)),t  -> fail_constapp (tm_info t)

    (* MCore integer intrinsics *)
    | CInt(_),t -> fail_constapp (tm_info t)

    | Caddi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Caddi(Some(v)))
    | Caddi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
    | Caddi(None),t | Caddi(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csubi(Some(v)))
    | Csubi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
    | Csubi(None),t | Csubi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmuli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmuli(Some(v)))
    | Cmuli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
    | Cmuli(None),t | Cmuli(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cdivi(Some(v)))
    | Cdivi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
    | Cdivi(None),t | Cdivi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmodi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmodi(Some(v)))
    | Cmodi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 mod v2))
    | Cmodi(None),t | Cmodi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegi,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
    | Cnegi,t -> fail_constapp (tm_info t)

    | Clti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Clti(Some(v)))
    | Clti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 < v2))
    | Clti(None),t | Clti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cleqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cleqi(Some(v)))
    | Cleqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <= v2))
    | Cleqi(None),t | Cleqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgti(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgti(Some(v)))
    | Cgti(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 > v2))
    | Cgti(None),t | Cgti(Some(_)),t  -> fail_constapp (tm_info t)

    | Cgeqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cgeqi(Some(v)))
    | Cgeqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 >= v2))
    | Cgeqi(None),t | Cgeqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Ceqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Ceqi(Some(v)))
    | Ceqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 = v2))
    | Ceqi(None),t | Ceqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cneqi(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cneqi(Some(v)))
    | Cneqi(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <> v2))
    | Cneqi(None),t | Cneqi(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cslli(Some(v)))
    | Cslli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsl v2))
    | Cslli(None),t | Cslli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrli(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrli(Some(v)))
    | Csrli(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 lsr v2))
    | Csrli(None),t | Csrli(Some(_)),t  -> fail_constapp (tm_info t)

    | Csrai(None),TmConst(fi,CInt(v)) -> TmConst(fi,Csrai(Some(v)))
    | Csrai(Some(v1)),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 asr v2))
    | Csrai(None),t | Csrai(Some(_)),t  -> fail_constapp (tm_info t)

    | Carity,TmConst(fi,c) -> TmConst(fi,CInt(arity c))
    | Carity,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: Floating-point number constant and operations *)
    | CFloat(_),t -> fail_constapp (tm_info t)

    | Caddf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Caddf(Some(v)))
    | Caddf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 +. v2))
    | Caddf(None),t | Caddf(Some(_)),t  -> fail_constapp (tm_info t)

    | Csubf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Csubf(Some(v)))
    | Csubf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 -. v2))
    | Csubf(None),t | Csubf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cmulf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cmulf(Some(v)))
    | Cmulf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 *. v2))
    | Cmulf(None),t | Cmulf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cdivf(None),TmConst(fi,CFloat(v)) -> TmConst(fi,Cdivf(Some(v)))
    | Cdivf(Some(v1)),TmConst(fi,CFloat(v2)) -> TmConst(fi,CFloat(v1 /. v2))
    | Cdivf(None),t | Cdivf(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnegf,TmConst(fi,CFloat(v)) -> TmConst(fi,CFloat((-1.0)*.v))
    | Cnegf,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: characters *)
    | CChar(_),t -> fail_constapp (tm_info t)

    | CChar2int,TmConst(fi,CChar(v)) -> TmConst(fi,CInt(v))
    | CChar2int,t -> fail_constapp (tm_info t)

    | CInt2char,TmConst(fi,CInt(v)) -> TmConst(fi,CChar(v))
    | CInt2char,t -> fail_constapp (tm_info t)

    (* MCore intrinsic: sequences *)
    | CSeq(_),t -> fail_constapp (tm_info t)

    | Cmakeseq(None),TmConst(fi,CInt(v)) -> TmConst(fi,Cmakeseq(Some(v)))
    | Cmakeseq(Some(v1)),t -> TmConst(tm_info t,CSeq(List.init v1 (fun _ -> t)))
    | Cmakeseq(None),t -> fail_constapp (tm_info t)

    | Cconcat(None),TmConst(fi,CSeq(lst1)) -> TmConst(fi,Cconcat(Some(lst1)))
    | Cconcat(Some(lst1)),TmConst(fi,CSeq(lst2)) ->
       TmConst(fi,CSeq(List.append lst1 lst2))
    | Cconcat(None),t | Cconcat(Some(_)),t  -> fail_constapp (tm_info t)

    | Cnth(None),TmConst(fi,CSeq(lst)) -> TmConst(fi,Cnth(Some(lst)))
    | Cnth(Some(lst)),TmConst(_,CInt(n)) ->
       (try List.nth lst n with _ -> raise_error fi "Out of bound access in sequence.")
    | Cnth(None),t | Cnth(Some(_)),t  -> fail_constapp (tm_info t)

    | Ccons(None),t -> TmConst(tm_info t,Ccons(Some(t)))
    | Ccons(Some(t)),TmConst(fi,CSeq(lst)) -> TmConst(fi,CSeq(t::lst))
    | Ccons(Some(_)),t  -> fail_constapp (tm_info t)

    | Cslice(None,None),TmConst(fi,CSeq(lst)) -> TmConst(fi,Cslice(Some(lst),None))
    | Cslice(Some(lst),None),TmConst(fi,CInt(s)) -> TmConst(fi,Cslice(Some(lst),Some(s)))
    | Cslice(Some(lst),Some(s)),TmConst(fi,CInt(l)) ->
       let lst2 = List.fold_left (fun (acc,n) x -> if n >= s && n < s + l
                                                   then (x::acc,n+1) else (acc,n+1))
                  ([],0) lst |> fst |> List.rev in TmConst(fi,CSeq(lst2))
    | Cslice(_,_),t -> fail_constapp (tm_info t)

    | Creverse,TmConst(fi,CSeq(lst)) -> TmConst(fi,CSeq(List.rev lst))
    | Creverse,t -> fail_constapp (tm_info t)

    (* MCore debug and stdio intrinsics *)
    | CDPrint, t -> uprint_endline (pprintME t);TmConst(NoInfo,Cnop)


(* Debug function used in the eval function *)
let debug_eval env t =
  if enable_debug_eval then
    (printf "\n-- eval -- \n";
     uprint_endline (pprintME t);
     if enable_debug_eval_env then
        uprint_endline (pprint_env env))
  else ()

(* Print out error message when a unit test fails *)
let unittest_failed fi t1 t2=
  uprint_endline
    (match fi with
    | Info(_,l1,_,_,_) -> us"\n ** Unit test FAILED on line " ^.
        us(string_of_int l1) ^. us" **\n    LHS: " ^. (pprintME t1) ^.
        us"\n    RHS: " ^. (pprintME t2)
    | NoInfo -> us"Unit test FAILED ")



(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match v1,v2 with
  | TmConst(_,CSeq(lst1)), TmConst(_,CSeq(lst2)) -> (
     List.length lst1 = List.length lst2 &&
     List.for_all (fun (x,y) -> val_equal x y) (List.combine lst1 lst2))
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | _ -> false


(* Convert a term into de Bruijn indices. Note that both type variables
   and term variables are converted. The environment [env] is a list
   type [vartype], indicating if it is a type variable (VarTy(x)) or
   a term variable (VarTm(x)). *)
let rec debruijn env t =
  match t with
  | TmVar(fi,x,_) ->
    let rec find env n =
      (match env with
       | VarTm(y)::ee -> if y =. x then n else find ee (n+1)
       | [] -> raise_error fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'"))
    in TmVar(fi,x,find env 0)
  | TmLam(fi,x,ty,t1) -> TmLam(fi,x,ty,debruijn (VarTm(x)::env) t1)
  | TmClos(_,_,_,_,_) -> failwith "Closures should not be available."
  | TmLet(fi,x,t1,t2) -> TmLet(fi,x,debruijn env t1,debruijn (VarTm(x)::env) t2)
  | TmApp(fi,t1,t2) -> TmApp(fi,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmUtest(fi,t1,t2,tnext)
      -> TmUtest(fi,debruijn env t1,debruijn env t2,debruijn env tnext)



(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval env t =
  debug_eval env t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(_,_,n) -> eval env  (List.nth env n)
  (* Lambda and closure conversions *)
  | TmLam(fi,x,ty,t1) -> TmClos(fi,x,ty,t1,env)
  | TmClos(_,_,_,_,_) -> t
  (* Let *)
  | TmLet(_,_,t1,t2) -> eval ((eval env t1)::env) t2
  (* Application *)
  | TmApp(fiapp,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
       | TmClos(_,_,_,t3,env2) -> eval ((eval env t2)::env2) t3
       (* Constant application using the delta function *)
       | TmConst(_,c) -> delta fiapp c (eval env t2)
       (* Fix *)
       | TmFix(_) ->
         (match eval env t2 with
         | TmClos(fi,_,_,t3,env2) as tt -> eval ((TmApp(fi,TmFix(fi),tt))::env2) t3
         | _ -> failwith "Incorrect CFix")
       | _ -> failwith "Incorrect application")
  (* Constant *)
  | TmConst(_,_) | TmFix(_) -> t
  (* The rest *)
  | TmUtest(fi,t1,t2,tnext) ->
    if !utest then begin
      let (v1,v2) = ((eval env t1),(eval env t2)) in
        if val_equal v1 v2 then
         (printf "."; utest_ok := !utest_ok + 1)
       else (
        unittest_failed fi v1 v2;
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
     end;
    eval env tnext
