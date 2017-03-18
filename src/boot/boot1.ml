(* 
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt

   mb1.ml is the main entry point for the bootstrapping
   interpreter that is implemented in OCaml. Note that the Modelyze
   bootstrapper only implements a subset of the language mcore
   (Modelyze core).
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

  
(* Pretty prints operands *)   
let pprintop op =
  us(match op with
  | OpAdd -> "+"
  | OpSub -> "-"
  | OpMul -> "*"
  | OpDiv -> "/"
  | OpMod -> "%"
  | OpBoolNot -> "!"
  | OpBoolAnd -> "&&"
  | OpBoolOr -> "||"
  | OpLess -> "<"
  | OpLessEqual -> "<="
  | OpGreat -> ">"
  | OpGreatEqual -> ">="
  | OpEqual -> "=="
  | OpNotEqual -> "!="
  | OpDstr -> "dstr"       
  | OpDBstr -> "dbstr"
  | OpDprint -> "dprint"            (* Debug printing of any value *)
  | OpDBprint -> "dbprint"          (* Debug basic printing "dbprint". 
                                       Use e.g. Set(1,2) instead of {1,2} *)
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

(* Pretty print match cases *)
let rec pprint_cases basic cases = 
   Ustring.concat (us" else ") (List.map
    (fun (Case(_,p,t)) -> pprint_pat p ^. us" => " ^. pprint basic t) cases)
     
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
  | TmInt(fi,i) -> us(sprintf "%d" i)
  | TmBool(fi,b) -> us(if b then "true" else "false")
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
        let intlst = List.map
          (fun x -> match x with TmChar(_,i) -> i | _ -> failwith "Not a string list") lst in
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
  | TmInt(_,_) -> t
  | TmBool(_,_) -> t
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
  | TmInt(_,n1),TmInt(_,n2) -> n1 = n2
  | TmBool(_,b1),TmBool(_,b2) -> b1 = b2
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
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
  | OpAdd,TmInt(l,v1),TmInt(_,v2) -> TmInt(l,v1 + v2)
  | OpSub,TmInt(l,v1),TmInt(_,v2) -> TmInt(l,v1 - v2)
  | OpMul,TmInt(l,v1),TmInt(_,v2) -> TmInt(l,v1 * v2)
  | OpDiv,TmInt(l,v1),TmInt(_,v2) -> TmInt(l,v1 / v2)
  | OpMod,TmInt(l,v1),TmInt(_,v2) -> TmInt(l,v1 mod v2)
  | OpBoolNot,TmBool(l,v1),_ -> TmBool(l,not v1)
  | OpBoolAnd,TmBool(l,v1),TmBool(_,v2) -> TmBool(l,v1 && v2)
  | OpBoolOr,TmBool(l,v1),TmBool(_,v2) -> TmBool(l,v1 || v2)
  | OpLess,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 < v2)
  | OpLessEqual,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 <= v2)
  | OpGreat,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 > v2)
  | OpGreatEqual,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 >= v2)
  | OpEqual,v1,v2 -> TmBool(tm_info v1,val_equal v1 v2)
  | OpNotEqual,v1,v2 -> TmBool(tm_info v1,not (val_equal v1 v2))
  | OpDstr,t1,_ -> ustring2uctstring (pprint false t1)
  | OpDBstr,t1,_ -> ustring2uctstring (pprint true t1)
  | OpDprint,t1,_ -> uprint_endline (pprint false t1);TmNop
  | OpDBprint,t1,_ -> uprint_endline (pprint true t1);TmNop
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
    (match eval_match env p t final with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1)) (TmUC(fi2,UCLeaf(ts),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCLeaf([]),o2,u2) -> None
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf(t::ts),t2),o2,u2) ->
    (match eval_match env p t final with
    | Some(env,_) ->
      eval_match env (PatUC(fi1,ps,o1,u1))
        (TmUC(fi2,UCNode(UCLeaf(ts),t2),o2,u2)) final
    | None -> None)
  | PatUC(fi1,p::ps,o1,u1),TmUC(fi2,UCNode(UCLeaf([]),t2),o2,u2) ->
      eval_match env pat (TmUC(fi2,t2,o2,u2)) final
  | PatUC(fi1,[],o1,u1),TmUC(fi2,uct,_,_) when uctzero uct && final -> Some(env,TmNop)  
  | PatUC(fi1,[],o1,u1),t when not final-> Some(env,t)
  | PatUC(fi1,lst,o1,u2),t -> None
  | PatBool(_,b1),TmBool(_,b2) -> if b1 = b2 then Some(env,TmNop) else None
  | PatBool(_,_),_ -> None
  | PatInt(fi,i1),TmInt(_,i2) -> if i1 = i2 then Some(env,TmNop) else None
  | PatInt(_,_),_ -> None
  | PatConcat(_,PatIdent(_,x),p2),_ ->
      failwith "Pattern variable first is not part of Miking--"
  | PatConcat(_,p1,p2),t1 -> 
    (match eval_match env p1 t1 false with
    | Some(env,t2) -> eval_match env p2 t2 (final && true) 
    | None -> None)
      

  
(* Main evaluation loop of a term. Evaluates using big-step semantics *)    
let rec eval env t = 
  match t with
  | TmVar(fi,x,n) ->
     (* let rec index env k = match env with
      | t::ee -> if k = 0 then t else index ee (k-1)
      | [] -> failwith "Cannot find index"
        in index env n *)
          (match List.nth env n with
             | TmFix(_,t) as tt -> eval env tt
             | t -> t) 
  | TmLam(fi,x,t1) -> TmClos(fi,t1,env)
  | TmClos(fi,t1,env2) -> t
  | TmFix(fi,t1) ->
        (match eval env t1 with
         | TmClos(fi,t2,env2) as tt ->                  
              eval (TmFix(fi,tt)::env2) t2 
         | _ -> TmFix(fi,t1))
  | TmApp(fi,t1,t2) ->
      (match eval env t1 with
       | TmClos(fi,t3,env2) -> eval ((eval env t2)::env2) t3  
       | _ ->
         raise_error fi "Runtime error. Application to a non closure value.")
  | TmInt(_,_) -> t
  | TmBool(_,_) -> t
  | TmChar(_,_) -> t
  | TmOp(_,op,t1,t2) -> evalop op (eval env t1) (eval env t2)
  | TmIf(fi,t1,t2,t3) ->
      (match eval env t1 with
      | TmBool(_,true) -> eval env t2
      | TmBool(_,false) -> eval env t3
      | _ -> failwith "Incorrect if-expression")
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
        |> debruijn []
        |> eval []
        |> fun _ -> ()

  with
    | Lexer.Lex_error m -> fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str m))
    | Error m -> fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str m))
    | Parsing.Parse_error -> fprintf stderr "%s\n"
	(Ustring.to_utf8 (Msg.message2str (Lexer.parse_error_message())))
  end; close_in fs1;
  if !utest && !utest_fail_local = 0 then printf " OK\n" else printf "\n"

    
(* Define the file slash, to make it platform independent *)    
let sl = if Sys.win32 then "\\" else "/"

    
(* Add a slash at the end "\\" or "/" if not already available *)
let add_slash s =
  if String.length s = 0 || (String.sub s (String.length s - 1) 1) <> sl
  then s ^ sl else s

    
(* Print out main menu *)    
let menu() =
  printf "Usage: boot1 [test] <files>\n";
  printf "\n"


(* Main function. Checks arguments and reads file names *)
let main =
  if Array.length Sys.argv < 2 then menu()
  else
    (* Check if we should run the test suite *)
    let args = Array.to_list Sys.argv |> List.tl in
    let args =
      if List.hd args = "test" then (utest := true; List.tl args) else args
    in
    (* Expand folders to file names *)
    let files = List.fold_left (fun a v ->
      if Sys.is_directory v then
        (Sys.readdir v
         |> Array.to_list
         |> List.filter (fun x -> not (String.length x >= 1 && String.get x 0 = '.'))
         |> List.map (fun x -> (add_slash v) ^ x) 
         |> List.filter (fun x -> not (Sys.is_directory x))
        ) @ a  
      else v::a
    ) [] args in
    
    (* Run all programs given as program arguments *)
    List.iter evalprog files;

    (* Print out the unit test results *)
    if !utest && !utest_fail = 0 then
      printf "\nUnit testing SUCCESSFUL after executing %d tests.\n"
        (!utest_ok)
    else if !utest then
      printf "\nERROR! %d successful tests and %d failed tests.\n"
        (!utest_ok) (!utest_fail)
    else ()
     
    





      
