(* 
   Modelyze II is licensed under the MIT license.  
   Copyright (C) David Broman. See file LICENSE.txt

   mozboot.ml is the main entry point for the bootstrapping
   interpreter that is implemented in OCaml. Note that the Modelyze
   bootstrapper only implements a subset of the language mcore
   (Modelyze core).
*)

open Utils
open Ustring.Op
open Printf
open Ast
open Msg

type options = { op_steps : bool; op_cbn : bool; op_speed : bool }
  

let sl = if Sys.win32 then "\\" else "/"

module StrSet = Set.Make(Ustring)

let utest = ref false
let utest_ok = ref 0
let utest_fail = ref 0
let utest_fail_local = ref 0
  
  
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
  | OpDprint -> "dprint"            (* Debug printing of any value *)
  | OpDBprint -> "dbprint"          (* Debug basic printing "dbprint". 
                                       Use e.g. Set(1,2) instead of {1,2} *)
  )

let pprintUCKind ordered uniqueness =
  match ordered, uniqueness with
  | UCUnordered, UCUnique      -> us"Set"
  | UCUnordered, UCMultivalued -> us"MultiSet"
  | UCOrdered,   UCUnique      -> us"UniqueList"
  | UCOrdered,   UCMultivalued -> us"List"
  | UCSorted,    UCUnique      -> us"SortedSet"
  | UCSorted,    UCMultivalued -> us"SortedMultiSet"


let uct2list uct =
  let rec work uct acc =
    match uct with
    | UCList(t::ts) -> work (UCList(ts)) (t::acc)
    | UCList([]) -> acc
    | UCNode(uc1,uc2) -> work uc2 (work uc1 acc)
  in List.rev (work uct [])
    
let rec pprint basic t =
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
  | TmSeq(fi,t1,t2) -> pprint t1 ^. us"\n" ^. pprint t2
  | TmUC(fi,uct,ordered,uniqueness) -> (
    match ordered, uniqueness with
    | UCOrdered,UCMultivalued when not basic ->
        us"[" ^. (Ustring.concat (us",") (List.map pprint (uct2list uct))) ^. us"]"
    | _,_ -> 
        (pprintUCKind ordered uniqueness) ^. us"(" ^.
          (Ustring.concat (us",") (List.map pprint (uct2list uct))) ^. us")")
  | TmUtest(fi,t1,t2,tnext) -> us"utest " ^. pprint t1 ^. us" " ^. pprint t2 
  | TmNop -> us"Nop"



  
let rec debruijn env t =
  match t with
  | TmVar(fi,x,_) ->
    let rec find env n = match env with
      | y::ee -> if y =. x then n else find ee (n+1)
      | [] -> raise_error fi "Unknown variable."
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
  | TmSeq(fi,t1,t2) -> TmSeq(fi,debruijn env t1,debruijn env t2)
  | TmUC(fi,uct,o,u) -> TmUC(fi, UCList(List.map (debruijn env) (uct2list uct)),o,u)
  | TmUtest(fo,t1,t2,tnext)
      -> TmUtest(fo,debruijn env t1,debruijn env t2,debruijn env tnext)
  | TmNop -> t  


  
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
  | OpEqual,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 == v2)
  | OpNotEqual,TmInt(l,v1),TmInt(_,v2) -> TmBool(l,v1 != v2)
  | OpDprint,t1,_ -> uprint_endline (pprint false t1);TmNop
  | OpDBprint,t1,_ -> uprint_endline (pprint true t1);TmNop  
  | _ -> failwith "Error evaluation values."
    

let rec val_equal v1 v2 =
  match v1,v2 with
  | TmInt(_,n1),TmInt(_,n2) -> n1 = n2
  | TmBool(_,b1),TmBool(_,b2) -> b1 = b2
  | TmChar(_,n1),TmChar(_,n2) -> n1 = n2
  | TmNop,TmNop -> true
  | _ -> false

    
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
  | TmSeq(_,t1,t2) -> let _ = eval env t1 in eval env t2
  | TmUC(fi,uct,o,u) -> TmUC(fi,ucmap (eval env) uct,o,u)
  | TmUtest(fi,t1,t2,tnext) -> 
     if !utest then begin
       if val_equal (eval env t1) (eval env t2) then
         (printf "."; utest_ok := !utest_ok + 1)
       else (
        unittest_failed fi;
        utest_fail := !utest_fail + 1;  
        utest_fail_local := !utest_fail_local + 1)
     end;
     eval env tnext
  | TmNop -> t  

    
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

(* Add a slash at the end "\\" or "/" if not already available *)
let add_slash s =
  if String.length s = 0 || (String.sub s (String.length s - 1) 1) <> sl
  then s ^ sl else s

let menu() =
  printf "Usage: mozboot [test] <files>\n";
  printf "\n"


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
     
    





      
