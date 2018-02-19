
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

(* Debug options *)
let enable_debug_normalize = false
let enable_debug_normalize_env = false
let enable_debug_readback = false
let enable_debug_readback_env = false
let enable_debug_eval = false
let enable_debug_eval_env = false
let enable_debug_after_peval = false


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
  | CIAdd -> us"iadd"
  | CIAdd2(v) -> us(sprintf "iadd(%d)" v)
  | CISub -> us"isub"
  | CISub2(v) -> us(sprintf "isub(%d)" v)
  | CIMul -> us"imul"
  | CIMul2(v) -> us(sprintf "imul(%d)" v)
  | CIDiv -> us"idiv"
  | CIDiv2(v) -> us(sprintf "idiv(%d)" v)
  | CIMod | CIMod2(_) -> us"imod"
  | CINeg             -> us"imod"
  | CILt  | CILt2(_)  -> us"ilt"
  | CILeq | CILeq2(_) -> us"ileq"
  | CIGt  | CIGt2(_)  -> us"igt"
  | CIGeq | CIGeq2(_) -> us"igeq"
  | CIEq  | CIEq2(_)  -> us"ieq"
  | CINeq | CINeq2(_) -> us"neq"
  (* MCore control intrinsics *)
  | CIF | CIF2(_) | CIF3(_,_) -> us"if"
  (* MCore debug and stdio intrinsics *)
  | CDStr -> us"dstr"
  | CDPrint -> us"dprint"
  | CPrint -> us"print"
  | CArgv  -> us"argv"
  (* MCore unified collection type (UCT) intrinsics *)
  | CConcat | CConcat2(_) -> us"concat"
  (* Ragnar polymorpic temps *)
  | CPolyEq  | CPolyEq2(_)  -> us"polyeq"
  | CPolyNeq | CPolyNeq2(_) -> us"polyneq"


(* Pretty print a term. The boolean parameter 'basic' is true when
   the pretty printing should be done in basic form. Use e.g. Set(1,2) instead of {1,2} *)
and pprint basic t =
  let pprint = pprint basic in
  match t with
  | TmVar(_,x,n,false) -> x ^. us"#" ^. us(string_of_int n)
  | TmVar(_,x,n,true) -> us"$" ^. us(string_of_int n)
  | TmLam(_,x,t1) -> us"(lam " ^. x ^. us". " ^. pprint t1 ^. us")"
  | TmClos(_,x,t,_,false) -> us"(clos " ^. x ^. us". " ^. pprint t ^. us")"
  | TmClos(_,x,t,_,true) -> us"(peclos " ^. x ^. us". " ^. pprint t ^. us")"
  | TmApp(_,t1,t2) -> pprint t1 ^. us" " ^. pprint t2
  | TmConst(_,c) -> pprint_const c
  | TmFix(_) -> us"fix"
  | TmPEval(_) -> us"peval"
  | TmChar(fi,c) -> us"'" ^. list2ustring [c] ^. us"'"
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

(* Pretty prints the environment *)
let pprint_env env =
  us"[" ^. (List.mapi (fun i t -> us(sprintf " %d -> " i) ^. pprint true t) env
            |> Ustring.concat (us",")) ^. us"]"

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
  | TmVar(fi,x,_,_) ->
    let rec find env n = match env with
      | y::ee -> if y =. x then n else find ee (n+1)
      | [] -> raise_error fi ("Unknown variable '" ^ Ustring.to_utf8 x ^ "'")
    in TmVar(fi,x,find env 0,false)
  | TmLam(fi,x,t1) -> TmLam(fi,x,debruijn (x::env) t1)
  | TmClos(fi,x,t1,env1,_) -> failwith "Closures should not be available."
  | TmApp(fi,t1,t2) -> TmApp(fi,debruijn env t1,debruijn env t2)
  | TmConst(_,_) -> t
  | TmFix(_) -> t
  | TmPEval(_) -> t
  | TmChar(_,_) -> t
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

(* Debug function used in the PE readback function *)
let debug_readback env n t =
  if enable_debug_readback then
    (printf "\n-- readback --   n=%d  \n" n;
     uprint_endline (pprint true t);
     if enable_debug_readback_env then
        uprint_endline (pprint_env env))
  else ()

(* Debug function used in the PE normalize function *)
let debug_normalize env n t =
  if enable_debug_normalize then
    (printf "\n-- normalize --   n=%d" n;
     uprint_endline (pprint true t);
     if enable_debug_normalize_env then
        uprint_endline (pprint_env env))
  else ()

(* Debug function used in the eval function *)
let debug_eval env t =
  if enable_debug_eval then
    (printf "\n-- eval -- \n";
     uprint_endline (pprint true t);
     if enable_debug_eval_env then
        uprint_endline (pprint_env env))
  else ()

(* Debug function used after partial evaluation *)
let debug_after_peval t =
  if enable_debug_after_peval then
    (printf "\n-- after peval --  \n";
     uprint_endline (pprint true t);
     t)
  else t


(* Mapping between named builtin functions (intrinsics) and the
   correspond constants *)
let builtin =
  [("bnot",CBNot);("band",CBAnd);("bor",CBOr);
   ("iadd",CIAdd);("isub",CISub);("imul",CIMul);("idiv",CIDiv);("imod",CIMod);("ineg",CINeg);
   ("ilt",CILt);("ileq",CILeq);("igt",CIGt);("igeq",CIGeq);("ieq",CIEq);("ineq",CINeq);
   ("ifexp",CIF);
   ("dstr",CDStr);("dprint",CDPrint);("print",CPrint);("argv",CArgv);
   ("concat",CConcat)]



(* Evaluates a constant application. This is the standard delta function
   delta(c,v) with the exception that it returns an expression and not
   a value. This is why the returned value is evaluated in the eval() function.
   The reason for this is that if-expressions return expressions
   and not values. *)
let delta c v  =
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

    (* MCore control intrinsics *)
    | CIF,TmConst(fi,CBool(v)) -> TmConst(NoInfo,CIF2(v))
    | CIF2(guard),leftbranch -> TmConst(NoInfo,CIF3(guard,leftbranch))
    | CIF3(true,leftbranch),_ -> TmApp(NoInfo,leftbranch,TmNop)
    | CIF3(false,_),rightbranch -> TmApp(NoInfo,rightbranch,TmNop)
    | CIF,t -> fail_constapp (tm_info t)

    (* MCore debug and stdio intrinsics *)
    | CDStr, t -> ustring2uctstring (pprint true t)
    | CDPrint, t -> uprint_endline (pprint true t);TmNop
    | CPrint, t ->
      (match t with
      | TmUC(_,uct,_,_) ->
        uct2list uct |> uc2ustring |> list2ustring |> Ustring.to_utf8
      |> printf "%s"; TmNop
      | _ -> raise_error (tm_info t) "Cannot print value with this type")
    | CArgv,_ ->
      let lst = List.map (fun x -> ustring2uctm NoInfo (us x)) (!prog_argv)
      in TmUC(NoInfo,UCLeaf(lst),UCOrdered,UCMultivalued)
    | CConcat,t -> TmConst(NoInfo,CConcat2(t))
    | CConcat2(TmUC(l,t1,o1,u1)),TmUC(_,t2,o2,u2)
      when o1 = o2 && u1 = u2 -> TmUC(l,UCNode(t1,t2),o1,u1)
    | CConcat2(tm1),TmUC(l,t2,o2,u2) -> TmUC(l,UCNode(UCLeaf([tm1]),t2),o2,u2)
    | CConcat2(TmUC(l,t1,o1,u1)),tm2 -> TmUC(l,UCNode(t1,UCLeaf([tm2])),o1,u1)
    | CConcat2(_),t -> fail_constapp (tm_info t)

    (* Ragnar polymorphic functions, special case for Ragnar in the boot interpreter.
       These functions should be defined using well-defined ad-hoc polymorphism
       in the real Ragnar compiler. *)
    | CPolyEq,t -> TmConst(NoInfo,CPolyEq2(t))
    | CPolyEq2(TmConst(_,c1)),TmConst(_,c2) -> TmConst(NoInfo,CBool(c1 = c2))
    | CPolyEq2(TmChar(_,v1)),TmChar(_,v2) -> TmConst(NoInfo,CBool(v1 = v2))
    | CPolyEq2(TmUC(_,_,_,_) as v1),(TmUC(_,_,_,_) as v2) -> TmConst(NoInfo,CBool(val_equal v1 v2))
    | CPolyEq2(_),t  -> fail_constapp (tm_info t)

    | CPolyNeq,t -> TmConst(NoInfo,CPolyNeq2(t))
    | CPolyNeq2(TmConst(_,c1)),TmConst(_,c2) -> TmConst(NoInfo,CBool(c1 <> c2))
    | CPolyNeq2(TmChar(_,v1)),TmChar(_,v2) -> TmConst(NoInfo,CBool(v1 <> v2))
    | CPolyNeq2(TmUC(_,_,_,_) as v1),(TmUC(_,_,_,_) as v2) -> TmConst(NoInfo,CBool(not (val_equal v1 v2)))
    | CPolyNeq2(_),t  -> fail_constapp (tm_info t)


(* The readback function is the second pass of the partial evaluation.
   It removes symbols for the term. If this is the complete version,
   this is the final pass before JIT *)
let rec readback env n t =
  debug_readback env n t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(fi,x,k,false) -> readback env n (List.nth env k)
  (* Variables as PE symbol. Convert symbol to de bruijn index. *)
  | TmVar(fi,x,k,true) -> TmVar(fi,x,n-k,false)
  (* Lambda *)
  | TmLam(fi,x,t1) -> TmLam(fi,x,readback (TmVar(fi,x,n+1,true)::env) (n+1) t1)
  (* Normal closure *)
  | TmClos(fi,x,t1,env2,false) -> t
  (* PE closure *)
  | TmClos(fi,x,t1,env2,true) ->
      TmLam(fi,x,readback (TmVar(fi,x,n+1,true)::env2) (n+1) t1)
  (* Application *)
  | TmApp(fi,t1,t2) -> TmApp(fi,readback env n t1,readback env n t2)
  (* Constant, fix, and PEval  *)
  | TmConst(_,_) | TmFix(_) | TmPEval(_) -> t
  (* Other old, to remove *)
  | TmChar(_,_) -> t
  | TmExprSeq(fi,t1,t2) ->
      TmExprSeq(fi,readback env n t1, readback env n t2)
  | TmUC(fi,uct,o,u) -> t
  | TmUtest(fi,t1,t2,tnext) ->
      TmUtest(fi,readback env n t1, readback env n t2,tnext)
  | TmMatch(fi,t1,cases) ->
      TmMatch(fi,readback env n t1,cases)
  | TmNop -> t



(* The function normalization function that leaves symbols in the
   term. These symbols are then removed using the readback function.
   'env' is the environment, 'n' the lambda depth number, 'm'
   the number of lambdas that we can go under, and
   't' the term. *)
let rec normalize env n t =
  debug_normalize env n t;
  match t with
  (* Variables using debruijn indices. *)
  | TmVar(fi,x,n,false) -> normalize env n (List.nth env n)
  (* PEMode variable (symbol) *)
  | TmVar(fi,x,n,true) -> t
  (* Lambda and closure conversions to PE closure *)
  | TmLam(fi,x,t1) -> TmClos(fi,x,t1,env,true)
  (* Closures, both PE and non PE *)
  | TmClos(fi,x,t2,env2,pemode) -> t
  (* Application: closures and delta  *)
  | TmApp(fi,t1,t2) ->
    (match normalize env n t1 with
    (* Closure application (PE on non PE) TODO: use affine lamba check *)
    | TmClos(fi,x,t3,env2,_) ->
         normalize ((normalize env n t2)::env2) n t3
    (* Constant application using the delta function *)
    | TmConst(fi1,c1) ->
        (match normalize env n t2 with
        | TmConst(fi2,c2) as tt-> normalize env n (delta c1 tt)
        | nf -> TmApp(fi,TmConst(fi1,c1),nf))
    (* Partial evaluation *)
    | TmPEval(fi) ->
      (match normalize env n t2 with
      | TmClos(fi2,x,t2,env2,pemode) ->
          let pesym = TmVar(NoInfo,us"",n+1,true) in
          let t2' = (TmApp(fi,TmPEval(fi),t2)) in
          TmClos(fi2,x,normalize (pesym::env2) (n+1) t2',env2,true)
      | v2 -> v2)
    (* Fix *)
    | TmFix(fi2) ->
       (match normalize env n t2 with
       | TmClos(fi,x,t3,env2,_) as tt ->
           normalize ((TmApp(fi,TmFix(fi2),tt))::env2) n t3
       | v2 -> TmApp(fi,TmFix(fi2),v2))
    (* Stay in normalized form *)
    | v1 -> TmApp(fi,v1,normalize env n t2))
  (* Constant, fix, and Peval  *)
  | TmConst(_,_) | TmFix(_) | TmPEval(_) -> t
  (* Other old, to remove *)
  | TmChar(_,_) -> t
  | TmExprSeq(fi,t1,t2) ->
      TmExprSeq(fi,normalize env n t1, normalize env n t2)
  | TmUC(fi,uct,o,u) -> t
  | TmUtest(fi,t1,t2,tnext) ->
      TmUtest(fi,normalize env n t1,normalize env n t2,tnext)
  | TmMatch(fi,t1,cases) ->
      TmMatch(fi,normalize env n t1,cases)
  | TmNop -> t



(* Main evaluation loop of a term. Evaluates using big-step semantics *)
let rec eval env t =
  debug_eval env t;
  match t with
  (* Variables using debruijn indices. Need to evaluate because fix point. *)
  | TmVar(fi,x,n,_) -> eval env  (List.nth env n)
  (* Lambda and closure conversions *)
  | TmLam(fi,x,t1) -> TmClos(fi,x,t1,env,false)
  | TmClos(fi,x,t1,env2,_) -> t
  (* Application *)
  | TmApp(fi,t1,t2) ->
      (match eval env t1 with
       (* Closure application *)
       | TmClos(fi,x,t3,env2,_) -> eval ((eval env t2)::env2) t3
       (* Constant application using the delta function *)
       | TmConst(fi,c) -> eval env (delta c (eval env t2))
       (* Partial evaluation *)
       | TmPEval(fi2) -> normalize env 0 (TmApp(fi,TmPEval(fi2),t2))
           |> readback env 0 |> debug_after_peval |> eval env
       (* Fix *)
       | TmFix(fi) ->
         (match eval env t2 with
         | TmClos(fi,x,t3,env2,_) as tt -> eval ((TmApp(fi,TmFix(fi),tt))::env2) t3
         | _ -> failwith "Incorrect CFix")
       | _ -> raise_error fi "Application to a non closure value.")
  (* Constant *)
  | TmConst(_,_) | TmFix(_) | TmPEval(_) -> t
  | TmChar(_,_) -> t
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
