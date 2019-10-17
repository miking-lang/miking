(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg


(* Debug options *)
let enable_debug_eval = false
let enable_debug_eval_env = false
let enable_debug_after_parse = false
let enable_debug_after_debruijn = false
let enable_debug_after_erase = false



let utest = ref false           (* Set to true if unit testing is enabled *)
let utest_ok = ref 0            (* sCounts the number of successful unit tests *)
let utest_fail = ref 0          (* Counts the number of failed unit tests *)
let utest_fail_local = ref 0    (* Counts local failed tests for one file *)


(* Evaluation environment *)
type env = tm list


and const =
(* MCore intrinsic: unit - no operation *)
| Cunit
(* MCore intrinsic: Boolean constant and operations *)
| CBool    of bool
| Cnot
| Cand     of bool option
| Cor      of bool option
(* MCore intrinsic: Integer constant and operations *)
| CInt     of int
| Caddi    of int option
| Csubi    of int option
| Cmuli    of int option
| Cdivi    of int option
| Cmodi    of int option
| Cnegi
| Clti     of int option
| Cleqi    of int option
| Cgti     of int option
| Cgeqi    of int option
| Ceqi     of int option
| Cneqi    of int option
| Cslli    of int option
| Csrli    of int option
| Csrai    of int option
| Carity
(* MCore intrinsic: Floating-point number constant and operations *)
| CFloat   of float
| Caddf    of float option
| Csubf    of float option
| Cmulf    of float option
| Cdivf    of float option
| Cnegf
| Cltf     of float option
| Cleqf    of float option
| Cgtf     of float option
| Cgeqf    of float option
| Ceqf     of float option
| Cneqf    of float option
| Cfloorfi
| Cceilfi
| Croundfi
| CInt2float
(* MCore intrinsic: characters *)
| CChar    of int
| CChar2int
| CInt2char
(* MCore intrinsic: sequences *)
| CSeq     of tm list
| Cmakeseq of int option
| Clength
| Cconcat  of (tm list) option
| Cnth     of (tm list) option
| Ccons    of tm option
| Cslice   of (tm list) option * int option
| Creverse
(* MCore debug and I/O intrinsics *)
| Cprint
| Cdprint
| CreadFile
| CwriteFile of ustring option
| CfileExists
| CdeleteFile
| Cerror


(* Names *)
and sym = int

(* Terms in MLang *)
and cdecl   = CDecl   of info * ustring * ty
and param   = Param   of info * ustring * ty
and pattern = Pattern of info * ustring * ustring
and decl = (* TODO: Local? *)
| Data     of info * ustring * cdecl list
| Inter    of info * ustring * param list * (pattern * tm) list

and mlang   = Lang    of info * ustring * ustring list * decl list
and program = Program of info * mlang list * tm

(* Terms in MExpr *)
and tm =
| TmVar    of info * ustring * int                          (* Variable *)
| TmLam    of info * ustring * ty * tm                      (* Lambda abstraction *)
| TmClos   of info * ustring * ty * tm * env                (* Closure *)
| TmLet    of info * ustring * tm * tm                      (* Let *)
| TmApp    of info * tm * tm                                (* Application *)
| TmConst  of info * const                                  (* Constant *)
| TmIf     of info * tm * tm * tm                           (* If expression *)
| TmFix    of info                                          (* Fix point *)
| TmSeq    of info * tm list                                (* Sequence *)
| TmTuple  of info * tm list                                (* Tuple *)
| TmProj   of info * tm * int                               (* Projection of tuple *)
| TmData   of info * ustring * ty * tm                      (* Data constructor definition *)
| TmCon    of info * ustring * sym * tm option              (* Constructed data *)
| TmMatch  of info * tm * ustring * int * ustring * tm * tm (* Match data *)
| TmUse    of info * ustring * tm                           (* Use a language *)
| TmUtest  of info * tm * tm * tm                           (* Unit testing *)


(* Types *)
and ty =
| TyDyn                                           (* Dynamic type *)
| TyProd   of ty list                             (* Product type *)
| TyUnit                                          (* Unit type *)


(* Variable type *)
and vartype =
| VarTm    of ustring


(* No index -1 means that de Bruijn index has not yet been assigned *)
let noidx = -1

(* Creation and handling of constructors and symbol generation *)
let symno = ref 0
let gencon fi x = symno := !symno + 1; TmCon(fi,x,!symno,None)

(* General map over terms *)
let rec map_tm f = function
  | TmVar (_,_,_) as t -> f t
  | TmLam(fi,x,ty,t1) -> f (TmLam(fi,x,ty,map_tm f t1))
  | TmClos(fi,x,ty,t1,env) -> f (TmClos(fi,x,ty,map_tm f t1,env))
  | TmLet(fi,x,t1,t2) -> f (TmLet(fi,x,map_tm f t1,map_tm f t2))
  | TmApp(fi,t1,t2) -> f (TmApp(fi,map_tm f t1,map_tm f t2))
  | TmConst(_,_) as t -> f t
  | TmFix(_) as t -> f t
  | TmSeq(fi, tms) -> f (TmSeq(fi, List.map (map_tm f) tms))
  | TmIf(fi,t1,t2,t3) -> f (TmIf(fi,map_tm f t1,map_tm f t2,map_tm f t3))
  | TmTuple(fi,tms) -> f (TmTuple(fi,List.map (map_tm f) tms))
  | TmProj(fi,t1,n) -> f (TmProj(fi,map_tm f t1,n))
  | TmData(fi,x,ty,t1) -> f (TmData(fi,x,ty,map_tm f t1))
  | TmCon(fi,k,s,ot) -> f (TmCon(fi,k,s,Option.map (map_tm f) ot))
  | TmMatch(fi,t1,k,n,x,t2,t3) ->
    f (TmMatch(fi,map_tm f t1,k,n,x,map_tm f t2,map_tm f t3))
  | TmUse(fi,l,t1) -> f (TmUse(fi,l,map_tm f t1))
  | TmUtest(fi,t1,t2,tnext) -> f (TmUtest(fi,map_tm f t1,map_tm f t2,tnext))


(* Returns the info field from a term *)
let tm_info = function
  | TmVar(fi,_,_) -> fi
  | TmLam(fi,_,_,_) -> fi
  | TmClos(fi,_,_,_,_) -> fi
  | TmLet(fi,_,_,_) -> fi
  | TmApp(fi,_,_) -> fi
  | TmConst(fi,_) -> fi
  | TmIf(fi,_,_,_) -> fi
  | TmFix(fi) -> fi
  | TmSeq(fi,_) -> fi
  | TmTuple(fi,_) -> fi
  | TmProj(fi,_,_) -> fi
  | TmData(fi,_,_,_) -> fi
  | TmCon(fi,_,_,_) -> fi
  | TmMatch(fi,_,_,_,_,_,_) -> fi
  | TmUse(fi,_,_) -> fi
  | TmUtest(fi,_,_,_) -> fi


(* Converts a list of terms (typically from CSeq) to a ustring *)
let tmlist2ustring fi lst =
  List.map (fun x ->
      match x with | TmConst(_,CChar(i)) -> i
                   | _ -> raise_error fi "The term is not a string") lst
  |> list2ustring

(* Converts a ustring to a list of terms *)
let ustring2tmlist fi s =
   s |> ustring2list |> List.map (fun x -> TmConst(fi,CChar(x)))


type 'a tokendata = {i:info; v:'a}
