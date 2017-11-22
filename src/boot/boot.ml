
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

      

let utest = ref false           (* Set to true if unit testing is enabled *)
let utest_ok = ref 0            (* Counts the number of successful unit tests *)
let utest_fail = ref 0          (* Counts the number of failed unit tests *)
let utest_fail_local = ref 0    (* Counts local failed tests for one file *)
let prog_argv = ref []          (* Argv for the program that is executed *)
  
(* Pretty prints operands *)   
let pprintop op =
  us(match op with
  | OpDstr -> "dstr"       
  | OpDBstr -> "dbstr"
  | OpDprint -> "dprint"            (* Debug printing of any value *)
  | OpDBprint -> "dbprint"          (* Debug basic printing "dbprint". 
                                       Use e.g. Set(1,2) instead of {1,2} *)
  | OpPrint -> "print"
  | OpArgv -> "argv"
  | OpConcat -> "++"  
  )

    
(* Print the kind of unified collection (UC) type. *)    
let pprintUCKind ordered uniqueness =
  match ordered, uniqueness with
  | UCUnordered, UCUnique      -> us"Set"      (* Set *)
  | UCUnordered, UCMultivalued -> us"MSet"     (* Multivalued Set *)
  | UCOrdered,   UCUnique      -> us"USeq"     (* Unique Sequence *)
  | UCOrdered,   UCMultivalued -> us"Seq"      (* Sequence *)
  | UCSorted,    UCUnique      -> us"SSet"     (* Sorted Set *)
  | UCSorted,    UCMultivalued -> us"SMSet"    (* Sorted Multivalued Set *)

    
(* Traditional map function on unified collection (UC) types *)      
let rec ucmap f uc = match uc with
  | UCLeaf(tms) -> UCLeaf(List.map f tms)
  | UCNode(uc1,uc2) -> UCNode(ucmap f uc1, ucmap f uc2)

    
(* Collapses the UC structure into a revered ordered list *)    
let uct2revlist uc =
  let rec apprev lst acc =
    match lst with
    | l::ls -> apprev ls (l::acc)
    | [] -> acc
  in
  let rec work uc acc = 
    match uc with
    | UCLeaf(lst) -> apprev lst acc
    | UCNode(uc1,uc2) -> work uc2 (work uc1 acc)
  in work uc []


(* Translate a unified collection (UC) structure into a list *)  
let uct2list uct = uct2revlist uct |> List.rev

(* Pretty print a pattern *)
let rec pprint_pat pat =
  match pat with
  | PatIdent(_,s) -> s
  | PatChar(_,c) -> us"'" ^. list2ustring [c] ^. us"'"
  | PatUC(_,plst,_,_)      
      -> us"[" ^. (Ustring.concat (us",") (List.map pprint_pat plst)) ^. us"]"
  | PatBool(_,b) -> us(if b then "true" else "false")
  | PatInt(_,i) -> us(sprintf "%d" i)
  | PatConcat(_,p1,p2) -> (pprint_pat p1) ^. us"++" ^. (pprint_pat p2)

(* Converts a UC to a ustring *)     
let uc2ustring uclst =
    List.map
      (fun x -> match x with
      |TmChar(_,i) -> i
      | _ -> failwith "Not a string list") uclst 

         
(* Pretty print match cases *)
let rec pprint_cases basic cases = 
   Ustring.concat (us" else ") (List.map
    (fun (Case(_,p,t)) -> pprint_pat p ^. us" => " ^. pprint basic t) cases)

(* Pretty print constants *)
and pprint_const c =
  match c with
  (* MCore Intrinsic Booleans *)
  | CBool(b) -> if b then us"true" else us"false"
  | CBNot -> us"bnot"
  | CBAnd | CBAnd2(_) -> us"band"
  | CBOr | CBOr2(_) -> us"bor"
  (* MCore Intrinsic Integers *)
  | CInt(v) -> us(sprintf "%d" v)
  | CIAdd | CIAdd2(_) -> us"iadd"
  | CISub | CISub2(_) -> us"isub"
  | CIMul | CIMul2(_) -> us"imul"
  | CIDiv | CIDiv2(_) -> us"idiv"
  | CIMod | CIMod2(_) -> us"imod"
  | CINeg             -> us"imod"
  | CILt  | CILt2(_)  -> us"ilt"
  | CILeq | CILeq2(_) -> us"ileq"
  | CIGt  | CIGt2(_)  -> us"igt"
  | CIGeq | CIGeq2(_) -> us"igeq"
  | CIEq  | CIEq2(_)  -> us"ieq"
  | CINeq | CINeq2(_) -> us"neq"
  (* Ragnar polymorpic temps *)
  | CPolyEq | CPolyEq2(_) -> us"polyeq"
     
(* Pretty print a term. The boolean parameter 'basic' is true when
   the pretty printing should be done in basic form. Use e.g. Set(1,2) instead of {1,2} *)
and pprint basic t =
  let pprint = pprint basic in
  match t with
  | TmVar(_,x,_) -> x
  | TmLam(_,x,t1) -> us"(fun x " ^. x ^. us" " ^.  pprint t1 ^. us")"
  | TmClos(_,_,_) -> us"closure"
  | TmFix(_,_) -> us"fix"
  | TmApp(_,t1,t2) -> pprint t1 ^. us" " ^. pprint t2
  | TmConst(_,c) -> pprint_const c
  | TmChar(fi,c) -> us"'" ^. list2ustring [c] ^. us"'"
  | TmOp(fi,op,t1,t2) -> us"(" ^. pprint t1 ^. us" " ^. pprintop op ^.
                         us" " ^. pprint t2 ^. us")"
  | TmIf(fi,t1,t2,t3) -> us"if " ^. pprint t1 ^. us" then " ^. pprint t2 ^.
                         us" else " ^. pprint t3
  | TmExprSeq(fi,t1,t2) -> pprint t1 ^. us"\n" ^. pprint t2
  | TmUC(fi,uct,ordered,uniqueness) -> (
    match ordered, uniqueness with
    | UCOrdered,UCMultivalued when not basic ->
      let lst = uct2list uct in
      (match lst with       
      | TmChar(_,_)::_ ->
        let intlst = uc2ustring lst in
        us"\"" ^. list2ustring intlst ^.  us"\""
      | _ -> us"[" ^. (Ustring.concat (us",") (List.map pprint lst)) ^. us"]")
    | _,_ -> 
        (pprintUCKind ordered uniqueness) ^. us"(" ^.
          (Ustring.concat (us",") (List.map pprint (uct2list uct))) ^. us")")
  | TmUtest(fi,t1,t2,tnext) -> us"utest " ^. pprint t1 ^. us" " ^. pprint t2
  | TmMatch(fi,t1,cases)
    ->  us"match " ^. pprint t1 ^. us" {" ^. pprint_cases basic cases ^. us"}"
  | TmNop -> us"Nop"
 
    
(* Print out error message when a unit test fails *)    
let unittest_failed fi t1 t2=
  uprint_endline
    (match fi with
    | Info(filename,l1,_,_,_) -> us"\n ** Unit test FAILED on line " ^.
        us(string_of_int l1) ^. us" **\n    LHS: " ^. (pprint false t1) ^.
        us"\n    RHS: " ^. (pprint false t2)          
    | NoInfo -> us"Unit test FAILED ")

(* Add pattern variables to environment. Used in the debruijn function *)
let rec patvars env pat =
  match pat with
  | PatIdent(_,x) -> x::env    
  | PatChar(_,_) -> env
  | PatUC(fi,p::ps,o,u) -> patvars (patvars env p) (PatUC(fi,ps,o,u))      
  | PatUC(fi,[],o,u) -> env
  | PatBool(_,_) -> env
  | PatInt(_,_) -> env
  | PatConcat(_,p1,p2) -> patvars (patvars env p1) p2

    
(* Convert a term into de Bruijn indices *)  
let rec debruijn env t =
  match t with
  | TmVar(fi,x,_) ->
    let rec find env n = match env with
      | y::ee -> if y =. x then n else find ee (n+1)
      | [] -> raise_error fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'") 
    in TmVar(fi,x,find env 0)
  | TmLam(fi,x,t1) -> TmLam(fi,x,debruijn (x::env) t1)
  | TmClos(fi,t1,env1) -> failwith "Closures should not be available."
  | TmFix(fi,t1) -> TmFix(fi,debruijn env t1)
  | TmApp(fi,t1,t2) -> TmApp(fi,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmChar(_,_) -> t
  | TmOp(fi,op,t1,t2) -> TmOp(fi,op,debruijn env t1,debruijn env t2)
  | TmIf(fi,t1,t2,t3) -> TmIf(fi,debruijn env t1,debruijn env t2,debruijn env t3)
  | TmExprSeq(fi,t1,t2) -> TmExprSeq(fi,debruijn env t1,debruijn env t2)
  | TmUC(fi,uct,o,u) -> TmUC(fi, UCLeaf(List.map (debruijn env) (uct2list uct)),o,u)
  | TmUtest(fi,t1,t2,tnext)
      -> TmUtest(fi,debruijn env t1,debruijn env t2,debruijn env tnext)
  | TmMatch(fi,t1,cases) ->
      TmMatch(fi,debruijn env t1,
               List.map (fun (Case(fi,pat,tm)) ->
                 Case(fi,pat,debruijn (patvars env pat) tm)) cases)
  | TmNop -> t  

    
(* Check if two value terms are equal *)
let rec val_equal v1 v2 =
  match v1,v2 with
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
  | TmConst(_,c1),TmConst(_,c2) -> c1 = c2
  | TmUC(_,t1,o1,u1),TmUC(_,t2,o2,u2) ->
      let rec eql lst1 lst2 = match lst1,lst2 with
        | l1::ls1,l2::ls2 when val_equal l1 l2 -> eql ls1 ls2
        | [],[] -> true
        | _ -> false
      in o1 = o2 && u1 = u2 && eql (uct2revlist t1) (uct2revlist t2)
  | TmNop,TmNop -> true
  | _ -> false

let ustring2uctstring s =
  let ls = List.map (fun i -> TmChar(NoInfo,i)) (ustring2list s) in
  TmUC(NoInfo,UCLeaf(ls),UCOrdered,UCMultivalued)

(* Evaluate a binary or unary operation *)    
let evalop op t1 t2 =
  match op,t1,t2 with
  | OpDstr,t1,_ -> ustring2uctstring (pprint false t1)
  | OpDBstr,t1,_ -> ustring2uctstring (pprint true t1)
  | OpDprint,t1,_ -> uprint_endline (pprint false t1);TmNop
  | OpDBprint,t1,_ -> uprint_endline (pprint true t1);TmNop
  | OpPrint,t1,_ -> (match t1 with
    | TmUC(_,uct,_,_) ->
        uct2list uct |> uc2ustring |> list2ustring |> Ustring.to_utf8
        |> printf "%s"; TmNop
    | _ -> raise_error (tm_info t1) "Cannot print value with this type")
  | OpArgv,_,_ ->
    let lst = List.map (fun x -> ustring2uctm NoInfo (us x)) (!prog_argv) 
    in TmUC(NoInfo,UCLeaf(lst),UCOrdered,UCMultivalued)
  | OpConcat,TmUC(l,t1,o1,u1),TmUC(_,t2,o2,u2)
       when o1 = o2 && u1 = u2 -> TmUC(l,UCNode(t1,t2),o1,u1)
  | OpConcat,tm1,TmUC(l,t2,o2,u2) -> TmUC(l,UCNode(UCLeaf([tm1]),t2),o2,u2)
  | OpConcat,TmUC(l,t1,o1,u1),tm2 -> TmUC(l,UCNode(t1,UCLeaf([tm2])),o1,u1)
  | _ -> failwith "Error evaluation values."


(* Update all UC to have the form of lists *)
let rec make_tm_for_match tm =
  let rec mklist uc acc =
    match uc with
    | UCNode(uc1,uc2) -> (mklist uc2 (mklist uc1 acc))
    | UCLeaf(lst) -> (List.map make_tm_for_match lst)::acc
  in
  let rec mkuclist lst acc =
    match lst with
    | x::xs -> mkuclist xs (UCNode(UCLeaf(x),acc))
    | [] -> acc
  in
  match tm with
  | TmUC(fi,uc,o,u) ->
    TmUC(fi,mkuclist (mklist uc []) (UCLeaf([])),o,u)
  | _ -> tm

(* Check if a UC struct has zero length *)    
let rec uctzero uct =
  match uct with
  | UCNode(n1,n2) -> (uctzero n1) && (uctzero n2)
  | UCLeaf([]) -> true
  | UCLeaf(_) -> false
    
    
(* Matches a pattern against a value and returns a new environment
   Notes:
    - final is used to detect if a sequence be checked to be complete or not *)
let rec eval_match env pat t final =
    match pat,t with
  | PatIdent(_,x1),v -> Some(v::env,TmNop)
  | PatChar(_,c1),TmChar(_,c2) -> if c1 = c2 then Some(env,TmNop) else None
  | PatChar(_,_),_ -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCLeaf(t::ts),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1)) (TmUC(fi2,UCLeaf(ts),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCLeaf([]),o2,u2) -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf(t::ts),t2),o2,u2) ->
    (match eval_match env p t true with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1))
        (TmUC(fi2,UCNode(UCLeaf(ts),t2),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf([]),t2),o2,u2) ->
      eval_match env pat (TmUC(fi2,t2,o2,u2)) final
  | PatUC(fi1,[],o1,u1),TmUC(fi2,uct,_,_) when uctzero uct && final -> Some(env,TmNop)  
  | PatUC(fi1,[],o1,u1),t when not final-> Some(env,t)
  | PatUC(fi1,lst,o1,u2),t -> None
  | PatBool(_,b1),TmConst(_,CBool(b2)) -> if b1 = b2 then Some(env,TmNop) else None
  | PatBool(_,_),_ -> None
  | PatInt(fi,i1),TmConst(_,CInt(i2)) -> if i1 = i2 then Some(env,TmNop) else None
  | PatInt(_,_),_ -> None
  | PatConcat(_,PatIdent(_,x),p2),_ ->
      failwith "Pattern variable first is not part of Ragnar--"
  | PatConcat(_,p1,p2),t1 -> 
    (match eval_match env p1 t1 false with
    | Some(env,t2) -> eval_match env p2 t2 (final && true) 
    | None -> None)

let fail_constapp fi = raise_error fi "Incorrect application "
      
(* Evaluate a constant application. This is the traditional delta function delta(c,v) *)
let delta c v =
  match c,v with
  (* MCore boolean intrinsics *)
  | CBool(_),t -> fail_constapp (tm_info t)

  | CBNot,TmConst(fi,CBool(v)) -> TmConst(fi,CBool(not v))
  | CBNot,t -> fail_constapp (tm_info t)

  | CBAnd,TmConst(fi,CBool(v)) -> TmConst(fi,CBAnd2(v))
  | CBAnd2(v1),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 && v2))
  | CBAnd,t | CBAnd2(_),t  -> fail_constapp (tm_info t)

  | CBOr,TmConst(fi,CBool(v)) -> TmConst(fi,CBOr2(v))
  | CBOr2(v1),TmConst(fi,CBool(v2)) -> TmConst(fi,CBool(v1 || v2))
  | CBOr,t | CBOr2(_),t  -> fail_constapp (tm_info t)

  (* MCore integer intrinsics *)
  | CInt(_),t -> fail_constapp (tm_info t)
    
  | CIAdd,TmConst(fi,CInt(v)) -> TmConst(fi,CIAdd2(v))
  | CIAdd2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 + v2))
  | CIAdd,t | CIAdd2(_),t  -> fail_constapp (tm_info t)

  | CISub,TmConst(fi,CInt(v)) -> TmConst(fi,CISub2(v))
  | CISub2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 - v2))
  | CISub,t | CISub2(_),t  -> fail_constapp (tm_info t)

  | CIMul,TmConst(fi,CInt(v)) -> TmConst(fi,CIMul2(v))
  | CIMul2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 * v2))
  | CIMul,t | CIMul2(_),t  -> fail_constapp (tm_info t)

  | CIDiv,TmConst(fi,CInt(v)) -> TmConst(fi,CIDiv2(v))
  | CIDiv2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 / v2))
  | CIDiv,t | CIDiv2(_),t  -> fail_constapp (tm_info t)

  | CIMod,TmConst(fi,CInt(v)) -> TmConst(fi,CIMod2(v))
  | CIMod2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CInt(v1 mod v2))
  | CIMod,t | CIMod2(_),t  -> fail_constapp (tm_info t)

  | CINeg,TmConst(fi,CInt(v)) -> TmConst(fi,CInt((-1)*v))
  | CINeg,t -> fail_constapp (tm_info t)
    
  | CILt,TmConst(fi,CInt(v)) -> TmConst(fi,CILt2(v))
  | CILt2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 < v2))
  | CILt,t | CILt2(_),t  -> fail_constapp (tm_info t)
    
  | CILeq,TmConst(fi,CInt(v)) -> TmConst(fi,CILeq2(v))
  | CILeq2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <= v2))
  | CILeq,t | CILeq2(_),t  -> fail_constapp (tm_info t)
    
  | CIGt,TmConst(fi,CInt(v)) -> TmConst(fi,CIGt2(v))
  | CIGt2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 > v2))
  | CIGt,t | CIGt2(_),t  -> fail_constapp (tm_info t)
    
  | CIGeq,TmConst(fi,CInt(v)) -> TmConst(fi,CIGeq2(v))
  | CIGeq2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 >= v2))
  | CIGeq,t | CIGeq2(_),t  -> fail_constapp (tm_info t)
    
  | CIEq,TmConst(fi,CInt(v)) -> TmConst(fi,CIEq2(v))
  | CIEq2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 = v2))
  | CIEq,t | CIEq2(_),t  -> fail_constapp (tm_info t)
    
  | CINeq,TmConst(fi,CInt(v)) -> TmConst(fi,CINeq2(v))
  | CINeq2(v1),TmConst(fi,CInt(v2)) -> TmConst(fi,CBool(v1 <> v2))
  | CINeq,t | CINeq2(_),t  -> fail_constapp (tm_info t)

  (* Polymorphic functions, special case for Ragnar in the boot interpreter. 
     These functions should be defined using well-defined ad-hoc polymorphism
     in the real Ragnar compiler. *)
  | CPolyEq,t -> TmConst(NoInfo,CPolyEq2(t))
  | CPolyEq2(TmConst(_,CInt(v1))),TmConst(_,CInt(v2)) -> TmConst(NoInfo,CBool(v1 = v2))
  | CPolyEq2(TmConst(_,CBool(v1))),TmConst(_,CBool(v2)) -> TmConst(NoInfo,CBool(v1 = v2))
  | CPolyEq2(_),t  -> fail_constapp (tm_info t)
   
    
    
(* Mapping between named builtin functions (intrinsics) and the 
   correspond constats *)
let builtin =
  [("bnot",CBNot);("band",CBAnd);("bor",CBOr);
   ("iadd",CIAdd);("isub",CISub);("imul",CIMul);("idiv",CIDiv);("imod",CIMod);("ineg",CINeg);
   ("ilt",CILt);("ileq",CILeq);("igt",CIGt);("igeq",CIGeq);("ieq",CIEq);("ineq",CINeq)]

    
  
(* Main evaluation loop of a term. Evaluates using big-step semantics *)    
let rec eval env t = 
  match t with
  | TmVar(fi,x,n) ->
          (match List.nth env n with
             | TmFix(_,t) as tt -> eval env tt
             | t -> t) 
  | TmLam(fi,x,t1) -> TmClos(fi,t1,env)
  | TmClos(fi,t1,env2) -> t
  | TmFix(fi,t1) ->
        (match eval env t1 with
         | TmClos(fi,t2,env2) as tt -> eval (TmFix(fi,tt)::env2) t2 
         | _ -> TmFix(fi,t1))
  | TmApp(fi,t1,t2) ->
      (match eval env t1 with
       | TmClos(fi,t3,env2) -> eval ((eval env t2)::env2) t3
       | TmConst(fi,c) -> delta c (eval env t2)
       | _ -> raise_error fi "Application to a non closure value.")
  | TmConst(_,_) -> t
  | TmChar(_,_) -> t
  | TmOp(_,op,t1,t2) -> evalop op (eval env t1) (eval env t2)
  | TmIf(fi,t1,t2,t3) ->
      (match eval env t1 with
      | TmConst(_,CBool(v)) -> eval env (if v then t2 else t3)
      | t -> raise_error (tm_info t) "Incorrect if-expression")
  | TmExprSeq(_,t1,t2) -> let _ = eval env t1 in eval env t2
  | TmUC(fi,uct,o,u) -> TmUC(fi,ucmap (eval env) uct,o,u)
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
  | TmMatch(fi,t1,cases) -> (
     let v1 = make_tm_for_match (eval env t1) in
     let rec appcases cases =
       match cases with
       | Case(_,p,t)::cs ->
          (match eval_match env p v1 true with
         | Some(env,_) -> eval env t 
         | None -> appcases cs)
       | [] -> raise_error fi  "Match error"
     in
      appcases cases)
  | TmNop -> t  


(* Main function for evaluation a function. Performs lexing, parsing
   and evaluation. Does not perform any type checking *)
let evalprog filename  =
  if !utest then printf "%s: " filename;
  utest_fail_local := 0;
  let fs1 = open_in filename in
  let tablength = 8 in
  begin try
    Lexer.init (us filename) tablength;
    fs1 |> Ustring.lexing_from_channel
        |> Parser.main Lexer.main
        |> debruijn (builtin |> List.split |> fst |> List.map us)
        |> eval (builtin |> List.split |> snd |> List.map (fun x -> TmConst(NoInfo,x)))
        |> fun _ -> ()

    with
    | Lexer.Lex_error m ->
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else 
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m))
    | Error m -> 
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str m));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else 
        fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m)) 
    | Parsing.Parse_error ->
      if !utest then (
        printf "\n ** %s" (Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())));
        utest_fail := !utest_fail + 1;
        utest_fail_local := !utest_fail_local + 1)
      else
        fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"

(*      
  | Lexer.Lex_error m -> fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str m))
  | Error m ->
    if !utest then
      printf (" ** " ^ (Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message()))) ^ " ** ")
      else fprintf stderr "%s\n" (Ustring.to_utf8 (Msg.message2str m)) 
  | Parsing.Parse_error -> fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"
*)
    
    
    
(* Print out main menu *)    
let menu() =
  printf "Usage: boot [run|test] <files>\n";
  printf "\n"


(* Main function. Checks arguments and reads file names *)
let main =
  (* Check command  *)
  (match Array.to_list Sys.argv |> List.tl with

  (* Run tests on one or more files *)
  | "test"::lst | "t"::lst -> (
    utest := true;
    List.iter evalprog (files_of_folders lst);
    if !utest_fail = 0 then
      printf "\nUnit testing SUCCESSFUL after executing %d tests.\n"
        (!utest_ok)
            else 
      printf "\nERROR! %d successful tests and %d failed tests.\n"
        (!utest_ok) (!utest_fail))

  (* Run one program with program arguments *)
  | "run"::name::lst | name::lst -> (
    prog_argv := lst;
    evalprog name)

  (* Show the menu *)
  | _ -> menu())

     
    





      
