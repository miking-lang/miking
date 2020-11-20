(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt

   File ast.ml includes the types and definitions for the abstract
   syntax tree (AST) of the bootstrap interpreter.
*)

open Ustring.Op
open Msg
open Intrinsics

(* Debug options *)
let enable_debug_eval_tm = ref false

let enable_debug_eval_env = ref false

let enable_debug_after_parse = ref false

let enable_debug_after_symbolize = ref false

let enable_debug_after_mlang = ref false

let enable_debug_symbol_print = ref false

let utest = ref false (* Set to true if unit testing is enabled *)

let utest_ok = ref 0 (* Counts the number of successful unit tests *)

let utest_fail = ref 0 (* Counts the number of failed unit tests *)

let utest_fail_local = ref 0 (* Counts local failed tests for one file *)

(* Map type for record implementation *)
module Record = Map.Make (Ustring)

(* Evaluation environment *)
type env = (Symb.t * tm) list

and const =
  (* MCore intrinsic: Boolean constant and operations. See test/mexpr/bool.mc *)
  | CBool of bool
  (* MCore intrinsic: Integer constant and operations *)
  | CInt of int
  | Caddi of int option
  | Csubi of int option
  | Cmuli of int option
  | Cdivi of int option
  | Cmodi of int option
  | Cnegi
  | Clti of int option
  | Cleqi of int option
  | Cgti of int option
  | Cgeqi of int option
  | Ceqi of int option
  | Cneqi of int option
  | Cslli of int option
  | Csrli of int option
  | Csrai of int option
  | Carity
  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat of float
  | Caddf of float option
  | Csubf of float option
  | Cmulf of float option
  | Cdivf of float option
  | Cnegf
  | Cltf of float option
  | Cleqf of float option
  | Cgtf of float option
  | Cgeqf of float option
  | Ceqf of float option
  | Cneqf of float option
  | Cfloorfi
  | Cceilfi
  | Croundfi
  | Cint2float
  | Cstring2float
  (* MCore intrinsic: characters *)
  | CChar of int
  | Ceqc of int option
  | Cchar2int
  | Cint2char
  (* MCore intrinsic: sequences *)
  | CmakeSeq of int option
  | Clength
  | Cconcat of tm Mseq.t option
  | Cget of tm Mseq.t option
  | Cset of tm Mseq.t option * int option
  | Ccons of tm option
  | Csnoc of tm Mseq.t option
  | CsplitAt of tm Mseq.t option
  | Creverse
  (* MCore intrinsic: random numbers *)
  | CrandIntU of int option
  | CrandSetSeed
  (* MCore intrinsic: time *)
  | CwallTimeMs
  | CsleepMs
  (* MCore debug and I/O intrinsics *)
  | Cprint
  | Cdprint
  | CreadLine
  | CreadBytesAsString
  | CreadFile
  | CwriteFile of ustring option
  | CfileExists
  | CdeleteFile
  | Cerror
  | Cexit
  (* MCore Symbols *)
  | CSymb of Symb.t
  | Cgensym
  | Ceqsym of Symb.t option
  | Csym2hash
  (* External functions TODO(?,?): Should not be part of core language *)
  | CExt of Extast.ext
  | CSd of Sdast.ext
  | CPy of tm Pyast.ext

(* Terms in MLang *)
and cdecl = CDecl of info * ustring * ty

and param = Param of info * ustring * ty

and decl =
  (* TODO(?,?): Local? *)
  | Data of info * ustring * cdecl list
  | Inter of info * ustring * param list * (pat * tm) list

and mlang = Lang of info * ustring * ustring list * decl list

and let_decl = Let of info * ustring * ty * tm

and rec_let_decl = RecLet of info * (info * ustring * ty * tm) list

and con_decl = Con of info * ustring * ty

and utest_top = Utest of info * tm * tm * tm option

and top =
  | TopLang of mlang
  | TopLet of let_decl
  | TopRecLet of rec_let_decl
  | TopCon of con_decl
  | TopUtest of utest_top

and include_ = Include of info * ustring

and program = Program of include_ list * top list * tm

(* Terms in MExpr *)
and tm =
  | TmVar of info * ustring * Symb.t (* Variable *)
  | TmLam of info * ustring * Symb.t * ty * tm (* Lambda abstraction *)
  | TmLet of info * ustring * Symb.t * ty * tm * tm (* Let *)
  | TmRecLets of info * (info * ustring * Symb.t * ty * tm) list * tm (* Recursive lets *)
  | TmApp of info * tm * tm (* Application *)
  | TmConst of info * const (* Constant *)
  | TmSeq of info * tm Mseq.t (* Sequence *)
  | TmRecord of info * tm Record.t (* Record *)
  | TmRecordUpdate of info * tm * ustring * tm (* Record update *)
  | TmCondef of info * ustring * Symb.t * ty * tm (* Constructor definition *)
  | TmConapp of info * ustring * Symb.t * tm (* Constructor application *)
  | TmMatch of info * tm * pat * tm * tm (* Match data *)
  | TmUse of info * ustring * tm (* Use a language *)
  | TmUtest of info * tm * tm * tm option * tm (* Unit testing *)
  | TmNever of info (* Never term *)
  (* Only part of the runtime system *)
  | TmClos of info * ustring * Symb.t * tm * env Lazy.t (* Closure *)
  | TmFix of info

(* Fix point *)

(* Kind of pattern name *)
and patName =
  | NameStr of ustring * Symb.t (* A normal pattern name *)
  | NameWildcard

(* Pattern wildcard *)

(* Patterns *)
and pat =
  | PatNamed of info * patName (* Named, capturing wildcard *)
  | PatSeqTot of info * pat Mseq.t (* Exact sequence patterns *)
  | PatSeqEdge of info * pat Mseq.t * patName * pat Mseq.t (* Sequence edge patterns *)
  | PatRecord of info * pat Record.t (* Record pattern *)
  | PatCon of info * ustring * Symb.t * pat (* Constructor pattern *)
  | PatInt of info * int (* Int pattern *)
  | PatChar of info * int (* Char pattern *)
  | PatBool of info * bool (* Boolean pattern *)
  | PatAnd of info * pat * pat (* And pattern *)
  | PatOr of info * pat * pat (* Or pattern *)
  | PatNot of info * pat

(* Not pattern *)

(* Types *)
and ty =
  | TyUnit (* Unit type *)
  | TyUnknown (* Unknown type *)
  | TyBool (* Boolean type *)
  | TyInt (* Int type *)
  | TyFloat (* Floating-point type *)
  | TyChar (* Character type *)
  | TyArrow of ty * ty (* Function type *)
  | TySeq of ty (* Sequence type *)
  | TyTuple of ty list (* Tuple type *) (* TODO: Remove? Subsumed by record *)
  | TyRecord of (ustring * ty) list (* Record type *)
  | TyCon of ustring (* Type constructor *) (* TODO: TyVar + TyLam instead? *)
  | TyApp of (ty * ty)
  (* TODO: Add TyVariant, so that the meaning of "type Type in" can be parsed as "type Type = TyVariant { types = []} in" *)

(* Type constructor application *)

(* Kind of identifier *)
and ident =
  | IdVar of sid (* A variable identifier *)
  | IdCon of sid (* A constructor identifier *)
  | IdType of sid (* A type identifier *)
  | IdLabel of sid

(* A label identifier *)

let tmUnit = TmRecord (NoInfo, Record.empty)

module Option = BatOption

(* General (bottom-up) map over terms *)
let rec map_tm f = function
  | TmVar (_, _, _) as t ->
      f t
  | TmLam (fi, x, s, ty, t1) ->
      f (TmLam (fi, x, s, ty, map_tm f t1))
  | TmClos (fi, x, s, t1, env) ->
      f (TmClos (fi, x, s, map_tm f t1, env))
  | TmLet (fi, x, s, ty, t1, t2) ->
      f (TmLet (fi, x, s, ty, map_tm f t1, map_tm f t2))
  | TmRecLets (fi, lst, tm) ->
      f
        (TmRecLets
           ( fi
           , List.map (fun (fi, x, s, ty, t) -> (fi, x, s, ty, map_tm f t)) lst
           , map_tm f tm ))
  | TmApp (fi, t1, t2) ->
      f (TmApp (fi, map_tm f t1, map_tm f t2))
  | TmConst (_, _) as t ->
      f t
  | TmFix _ as t ->
      f t
  | TmSeq (fi, tms) ->
      f (TmSeq (fi, Mseq.Helpers.map (map_tm f) tms))
  | TmRecord (fi, r) ->
      f (TmRecord (fi, Record.map (map_tm f) r))
  | TmRecordUpdate (fi, r, l, t) ->
      f (TmRecordUpdate (fi, map_tm f r, l, map_tm f t))
  | TmCondef (fi, x, s, ty, t1) ->
      f (TmCondef (fi, x, s, ty, map_tm f t1))
  | TmConapp (fi, k, s, t) ->
      f (TmConapp (fi, k, s, t))
  | TmMatch (fi, t1, p, t2, t3) ->
      f (TmMatch (fi, map_tm f t1, p, map_tm f t2, map_tm f t3))
  | TmUse (fi, l, t1) ->
      f (TmUse (fi, l, map_tm f t1))
  | TmUtest (fi, t1, t2, tusing, tnext) ->
      let tusing_mapped = Option.map (map_tm f) tusing in
      f (TmUtest (fi, map_tm f t1, map_tm f t2, tusing_mapped, map_tm f tnext))
  | TmNever _ as t ->
      f t

(* Returns the info field from a term *)
let tm_info = function
  | TmVar (fi, _, _) ->
      fi
  | TmLam (fi, _, _, _, _) ->
      fi
  | TmClos (fi, _, _, _, _) ->
      fi
  | TmLet (fi, _, _, _, _, _) ->
      fi
  | TmRecLets (fi, _, _) ->
      fi
  | TmApp (fi, _, _) ->
      fi
  | TmConst (fi, _) ->
      fi
  | TmFix fi ->
      fi
  | TmSeq (fi, _) ->
      fi
  | TmRecord (fi, _) ->
      fi
  | TmRecordUpdate (fi, _, _, _) ->
      fi
  | TmCondef (fi, _, _, _, _) ->
      fi
  | TmConapp (fi, _, _, _) ->
      fi
  | TmMatch (fi, _, _, _, _) ->
      fi
  | TmUse (fi, _, _) ->
      fi
  | TmUtest (fi, _, _, _, _) ->
      fi
  | TmNever fi ->
      fi

let pat_info = function
  | PatNamed (fi, _) ->
      fi
  | PatSeqTot (fi, _) ->
      fi
  | PatSeqEdge (fi, _, _, _) ->
      fi
  | PatRecord (fi, _) ->
      fi
  | PatCon (fi, _, _, _) ->
      fi
  | PatInt (fi, _) ->
      fi
  | PatChar (fi, _) ->
      fi
  | PatBool (fi, _) ->
      fi
  | PatAnd (fi, _, _) ->
      fi
  | PatOr (fi, _, _) ->
      fi
  | PatNot (fi, _) ->
      fi

(* Converts a sequence of terms to a ustring *)
let tmseq2ustring fi s =
  Mseq.Helpers.map
    (fun x ->
      match x with
      | TmConst (_, CChar i) ->
          i
      | _ ->
          raise_error fi "The term is not a string")
    s
  |> Mseq.Helpers.to_ustring

(* Converts a ustring to a sequence of terms *)
let ustring2tmseq fi s =
  s |> Mseq.Helpers.of_ustring
  |> Mseq.Helpers.map (fun x -> TmConst (fi, CChar x))

(* Converts a list of terms (for a tuple) to a record term *)
let tuple2record fi lst =
  let r =
    List.fold_left
      (fun (i, a) x -> (i + 1, Record.add (ustring_of_int i) x a))
      (0, Record.empty) lst
  in
  TmRecord (fi, snd r)

(* Converts a record map to an optional list of terms. Returns Some list if
   the record represents a tuple, None otherwise. *)
let record2tuple (r : tm Record.t) =
  let match_tuple_item (a, k) (i, tm) =
    match a with
    | Some _ when try int_of_ustring i != k with _ -> true ->
        (None, 0)
    | Some lst ->
        (Some (tm :: lst), k + 1)
    | None ->
        (None, 0)
  in
  List.fold_left match_tuple_item (Some [], 0) (Record.bindings r) |> fst

type 'a tokendata = {i: info; v: 'a}
