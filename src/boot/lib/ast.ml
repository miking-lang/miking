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

let enable_debug_after_dead_code_elimination = ref false

let enable_debug_after_prune_external_utests = ref false

let enable_debug_dead_code_info = ref false

let enable_debug_after_mlang = ref false

let enable_debug_symbol_print = ref false

let enable_debug_con_shape = ref false

let enable_debug_stack_trace = ref false

let enable_debug_profiling = ref false

let disable_dead_code_elimination = ref false

let disable_prune_external_utests_summary = ref false

let disable_prune_external_utests = ref false

let disable_prune_external_utests_warning = ref false

let utest = ref false (* Set to true if unit testing is enabled *)

let utest_ok = ref 0 (* Counts the number of successful unit tests *)

let utest_fail = ref 0 (* Counts the number of failed unit tests *)

let utest_fail_local = ref 0 (* Counts local failed tests for one file *)

type side_effect = bool

type frozen = bool

(* Map type for record implementation *)
module Record = struct
  include Map.Make (Ustring)

  let map_fold (f : Ustring.t -> 'a -> 'b -> 'b * 'a) (s : 'a t) (init : 'b) :
      'b * 'a t =
    (* [map_fold] is a combination of [Record.mapi] and [Record.fold] that
       threads an accumulator through calls to [f].*)
    let acc = ref init in
    let s' =
      mapi
        (fun k v ->
          let acc', v' = f k v !acc in
          acc := acc' ;
          v' )
        s
    in
    (!acc, s')
end

(* Evaluation environment *)
type env = (Symb.t * tm) list

and const =
  | CunsafeCoerce
  (* MCore intrinsics: Booleans *)
  | CBool of bool
  (* MCore intrinsics: Integers *)
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
  (* MCore intrinsics: Floating-point numbers *)
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
  | CstringIsFloat
  | Cstring2float
  | Cfloat2string
  (* MCore intrinsics: Characters *)
  | CChar of int
  | Ceqc of int option
  | Cchar2int
  | Cint2char
  (* MCore intrinsic: sequences *)
  | Ccreate of int option
  | CcreateList of int option
  | CcreateRope of int option
  | CisList
  | CisRope
  | Clength
  | Cconcat of tm Mseq.t option
  | Cget of tm Mseq.t option
  | Cset of tm Mseq.t option * int option
  | Ccons of tm option
  | Csnoc of tm Mseq.t option
  | CsplitAt of tm Mseq.t option
  | Creverse
  | Chead
  | Ctail
  | Cnull
  | Cmap of (tm -> tm) option
  | Cmapi of (int -> tm -> tm) option
  | Citer of (tm -> unit) option
  | Citeri of (int -> tm -> unit) option
  | Cfoldl of (tm -> tm -> tm) option * tm option
  | Cfoldr of (tm -> tm -> tm) option * tm option
  | Csubsequence of tm Mseq.t option * int option
  (* MCore intrinsics: Random numbers *)
  | CrandIntU of int option
  | CrandSetSeed
  (* MCore intrinsics: Time *)
  | CwallTimeMs
  | CsleepMs
  (* MCore intrinsics: Debug and I/O *)
  | Cprint
  | CprintError
  | Cdprint
  | CreadLine
  | CreadBytesAsString
  | CreadFile
  | CwriteFile of int Mseq.t option
  | CfileExists
  | CdeleteFile
  | Ccommand
  | Cerror
  | Cexit
  | CflushStdout
  | CflushStderr
  (* MCore intrinsics: Symbols *)
  | CSymb of Symb.t
  | Cgensym
  | Ceqsym of Symb.t option
  | Csym2hash
  (* MCore intrinsics: Constructor tag *)
  | CconstructorTag
  (* MCore intrinsics: References *)
  | Cref
  | CmodRef of tm ref option
  | CdeRef
  (* MCore intrinsics: Maps *)
  (* NOTE(Linnea, 2021-01-27): Obj.t denotes the type of the internal map (I was so far unable to express it properly) *)
  | CMap of tm * Obj.t
  | CmapEmpty
  | CmapSize
  | CmapGetCmpFun
  | CmapInsert of tm option * tm option
  | CmapRemove of tm option
  | CmapFindExn of tm option
  | CmapFindOrElse of tm option * tm option
  | CmapFindApplyOrElse of tm option * tm option * tm option
  | CmapMem of tm option
  | CmapAny of (tm -> tm -> bool) option
  | CmapMap of (tm -> tm) option
  | CmapMapWithKey of (tm -> tm -> tm) option
  | CmapFoldWithKey of (tm -> tm -> tm -> tm) option * tm option
  | CmapBindings
  | CmapChooseExn
  | CmapChooseOrElse of tm option
  | CmapEq of (tm -> tm -> bool) option * (tm * Obj.t) option
  | CmapCmp of (tm -> tm -> int) option * (tm * Obj.t) option
  (* MCore intrinsics: Tensors *)
  | CtensorCreateDense of int Mseq.t option
  | CtensorCreateUninitInt
  | CtensorCreateUninitFloat
  | CtensorCreateCArrayInt of int Mseq.t option
  | CtensorCreateCArrayFloat of int Mseq.t option
  | CtensorGetExn of tm T.t option
  | CtensorSetExn of tm T.t option * int Mseq.t option
  | CtensorLinearGetExn of tm T.t option
  | CtensorLinearSetExn of tm T.t option * int option
  | CtensorRank
  | CtensorShape
  | CtensorCopy
  | CtensorTransposeExn of tm T.t option * int option
  | CtensorReshapeExn of tm T.t option
  | CtensorSliceExn of tm T.t option
  | CtensorSubExn of tm T.t option * int option
  | CtensorIterSlice of tm option
  | CtensorEq of tm option * tm T.t option
  | Ctensor2string of tm option
  (* MCore intrinsics: Boot parser *)
  | CbootParserTree of ptree
  | CbootParserParseMExprString of int Mseq.t Mseq.t option
  | CbootParserParseMCoreFile of
      (bool * bool * int Mseq.t Mseq.t * bool * bool * bool) option
      * int Mseq.t Mseq.t option
  | CbootParserGetId
  | CbootParserGetTerm of tm option
  | CbootParserGetType of tm option
  | CbootParserGetString of tm option
  | CbootParserGetInt of tm option
  | CbootParserGetFloat of tm option
  | CbootParserGetListLength of tm option
  | CbootParserGetConst of tm option
  | CbootParserGetPat of tm option
  | CbootParserGetInfo of tm option
  (* External functions *)
  | CPy of tm Pyast.ext

(* Parser tree. Used by the boot parser intrinsics *)
and ptree =
  | PTreeTm of tm
  | PTreeTy of ty
  | PTreePat of pat
  | PTreeConst of const
  | PTreeInfo of info

(* Terms in MLang *)
and cdecl = CDecl of info * ustring * ty

and param = Param of info * ustring * ty

and decl =
  (* TODO(?,?): Local? *)
  | Data of info * ustring * cdecl list
  | Inter of info * ustring * ty * param list option * (pat * tm) list
  | Alias of info * ustring * ustring list * ty

and mlang = Lang of info * ustring * ustring list * decl list

and let_decl = Let of info * ustring * ty * tm

and type_decl = Type of info * ustring * ustring list * ty

and rec_let_decl = RecLet of info * (info * ustring * ty * tm) list

and con_decl = Con of info * ustring * ty

and utest_top = Utest of info * tm * tm * tm option

and ext_decl = Ext of info * ustring * bool * ty

and top =
  | TopLang of mlang
  | TopLet of let_decl
  | TopType of type_decl
  | TopRecLet of rec_let_decl
  | TopCon of con_decl
  | TopUtest of utest_top
  | TopExt of ext_decl

and include_ = Include of info * ustring

and program = Program of include_ list * top list * tm

(* Terms in MExpr *)
and tm =
  (* Variable *)
  | TmVar of info * ustring * Symb.t * frozen
  (* Application *)
  | TmApp of info * tm * tm
  (* Lambda abstraction *)
  | TmLam of info * ustring * Symb.t * ty * tm
  (* Let *)
  | TmLet of info * ustring * Symb.t * ty * tm * tm
  (* Recursive lets *)
  | TmRecLets of info * (info * ustring * Symb.t * ty * tm) list * tm
  (* Constant *)
  | TmConst of info * const
  (* Sequence *)
  | TmSeq of info * tm Mseq.t
  (* Record *)
  | TmRecord of info * tm Record.t
  (* Record update *)
  | TmRecordUpdate of info * tm * ustring * tm
  (* Type let *)
  (* NOTE(aathn, 2022-03-02): Type parameters are not symbolized currently *)
  | TmType of info * ustring * Symb.t * ustring list * ty * tm
  (* Constructor definition *)
  | TmConDef of info * ustring * Symb.t * ty * tm
  (* Constructor application *)
  | TmConApp of info * ustring * Symb.t * tm
  (* Match data *)
  | TmMatch of info * tm * pat * tm * tm
  (* Unit testing *)
  | TmUtest of info * tm * tm * tm option * tm
  (* Never term *)
  | TmNever of info
  (* -- The following term is removed during MLang desugaring *)
  (* Use a language *)
  | TmUse of info * ustring * tm
  (* External *)
  | TmExt of info * ustring * Symb.t * side_effect * ty * tm
  (* -- The rest is ONLY part of the runtime system *)
  (* Closure *)
  | TmClos of info * ustring * Symb.t * tm * env Lazy.t (* Closure *)
  (* Fix point *)
  | TmFix of info
  (* Reference *)
  | TmRef of info * tm ref
  (* Tensor *)
  | TmTensor of info * tm T.t

(* Kind of pattern name *)
and patName =
  | NameStr of ustring * Symb.t (* A normal pattern name *)
  | NameWildcard

(* Pattern wildcard *)

(* Patterns *)
and pat =
  (* Named, capturing wildcard *)
  | PatNamed of info * patName
  (* Exact sequence patterns *)
  | PatSeqTot of info * pat Mseq.t
  (* Sequence edge patterns *)
  | PatSeqEdge of info * pat Mseq.t * patName * pat Mseq.t
  (* Record pattern *)
  | PatRecord of info * pat Record.t
  (* Constructor pattern *)
  | PatCon of info * ustring * Symb.t * pat
  (* Int pattern *)
  | PatInt of info * int
  (* Char pattern *)
  | PatChar of info * int
  (* Boolean pattern *)
  | PatBool of info * bool
  (* And pattern *)
  | PatAnd of info * pat * pat
  (* Or pattern *)
  | PatOr of info * pat * pat
  (* Not pattern *)
  | PatNot of info * pat

(* Types *)
and ty =
  (* Unknown type *)
  | TyUnknown of info
  (* Boolean type *)
  | TyBool of info
  (* Int type *)
  | TyInt of info
  (* Floating-point type *)
  | TyFloat of info
  (* Character type *)
  | TyChar of info
  (* Function type *)
  | TyArrow of info * ty * ty
  (* Forall quantifier *)
  (* NOTE(aathn, 2022-03-02): Type variables are not symbolized currently *)
  | TyAll of info * ustring * ty
  (* Sequence type *)
  | TySeq of info * ty
  (* Tensor type *)
  | TyTensor of info * ty
  (* Record type *)
  | TyRecord of info * ty Record.t
  (* Variant type *)
  | TyVariant of info * (ustring * Symb.t) list
  (* Type constructors *)
  | TyCon of info * ustring * Symb.t
  (* Type variables *)
  (* NOTE(aathn, 2022-03-02): Type variables are not symbolized currently *)
  | TyVar of info * ustring
  (* Type application *)
  | TyApp of info * ty * ty

(* Kind of identifier *)
and ident =
  (* A variable identifier *)
  | IdVar of sid
  (* A constructor identifier *)
  | IdCon of sid
  (* A type identifier *)
  | IdType of sid
  (* A label identifier *)
  | IdLabel of sid

let tm_unit = TmRecord (NoInfo, Record.empty)

let ty_unit fi = TyRecord (fi, Record.empty)

(* smap accumulate left for terms *)
let smap_accum_left_tm_tm (f : 'a -> tm -> 'a * tm) (acc : 'a) : tm -> 'a * tm
    = function
  | TmApp (fi, t1, t2) ->
      f acc t1
      |> fun (acc, t1') ->
      f acc t2 |> fun (acc, t2') -> (acc, TmApp (fi, t1', t2'))
  | TmLam (fi, x, s, ty, t) ->
      f acc t |> fun (acc, t') -> (acc, TmLam (fi, x, s, ty, t'))
  | TmLet (fi, x, s, ty, t1, t2) ->
      f acc t1
      |> fun (acc, t1') ->
      f acc t2 |> fun (acc, t2') -> (acc, TmLet (fi, x, s, ty, t1', t2'))
  | TmRecLets (fi, lst, t) ->
      List.fold_left_map
        (fun acc (fi, x, s, ty, t) ->
          f acc t |> fun (acc, t') -> (acc, (fi, x, s, ty, t')) )
        acc lst
      |> fun (acc, lst') ->
      f acc t |> fun (acc, t') -> (acc, TmRecLets (fi, lst', t'))
  | TmSeq (fi, ts) ->
      let acc, ts' = Mseq.Helpers.map_accum_left f acc ts in
      (acc, TmSeq (fi, ts'))
  | TmRecord (fi, r) ->
      let acc, r' = Record.map_fold (fun _ t acc -> f acc t) r acc in
      (acc, TmRecord (fi, r'))
  | TmRecordUpdate (fi, r, l, t) ->
      f acc r
      |> fun (acc, r') ->
      f acc t |> fun (acc, t') -> (acc, TmRecordUpdate (fi, r', l, t'))
  | TmType (fi, x, s, params, ty, t) ->
      f acc t |> fun (acc, t') -> (acc, TmType (fi, x, s, params, ty, t'))
  | TmConDef (fi, x, s, ty, t) ->
      f acc t |> fun (acc, t') -> (acc, TmConDef (fi, x, s, ty, t'))
  | TmConApp (fi, k, s, t) ->
      f acc t |> fun (acc, t') -> (acc, TmConApp (fi, k, s, t'))
  | TmMatch (fi, t1, p, t2, t3) ->
      f acc t1
      |> fun (acc, t1') ->
      f acc t2
      |> fun (acc, t2') ->
      f acc t3 |> fun (acc, t3') -> (acc, TmMatch (fi, t1', p, t2', t3'))
  | TmUtest (fi, t1, t2, tusing, tnext) ->
      f acc t1
      |> fun (acc, t1') ->
      f acc t2
      |> fun (acc, t2') ->
      ( match tusing with
      | Some tusing' ->
          f acc tusing' |> fun (acc, tusing'') -> (acc, Some tusing'')
      | None ->
          (acc, tusing) )
      |> fun (acc, tusing') ->
      f acc tnext
      |> fun (acc, tnext') -> (acc, TmUtest (fi, t1', t2', tusing', tnext'))
  | TmUse (fi, l, t) ->
      f acc t |> fun (acc, t') -> (acc, TmUse (fi, l, t'))
  | TmExt (fi, x, s, ty, e, t) ->
      f acc t |> fun (acc, t') -> (acc, TmExt (fi, x, s, ty, e, t'))
  | TmClos (fi, x, s, t, env) ->
      f acc t |> fun (acc, t') -> (acc, TmClos (fi, x, s, t', env))
  | (TmVar _ | TmConst _ | TmNever _ | TmFix _ | TmRef _ | TmTensor _) as t ->
      (acc, t)

(* smap for terms *)
let smap_tm_tm (f : tm -> tm) (t : tm) : tm =
  let _, t' = smap_accum_left_tm_tm (fun _ t -> ((), f t)) () t in
  t'

(* sfold over terms *)
let sfold_tm_tm (f : 'a -> tm -> 'a) (acc : 'a) (t : tm) : 'a =
  let acc', _ = smap_accum_left_tm_tm (fun acc t -> (f acc t, t)) acc t in
  acc'

(* Returns arity given an type *)
let rec ty_arity = function TyArrow (_, _, ty) -> 1 + ty_arity ty | _ -> 0

(* Returns the info field from a term *)
let tm_info = function
  | TmVar (fi, _, _, _)
  | TmApp (fi, _, _)
  | TmLam (fi, _, _, _, _)
  | TmLet (fi, _, _, _, _, _)
  | TmRecLets (fi, _, _)
  | TmConst (fi, _)
  | TmSeq (fi, _)
  | TmRecord (fi, _)
  | TmRecordUpdate (fi, _, _, _)
  | TmType (fi, _, _, _, _, _)
  | TmConDef (fi, _, _, _, _)
  | TmConApp (fi, _, _, _)
  | TmMatch (fi, _, _, _, _)
  | TmUtest (fi, _, _, _, _)
  | TmNever fi
  | TmUse (fi, _, _)
  | TmClos (fi, _, _, _, _)
  | TmFix fi
  | TmRef (fi, _)
  | TmTensor (fi, _)
  | TmExt (fi, _, _, _, _, _) ->
      fi

let pat_info = function
  | PatNamed (fi, _)
  | PatSeqTot (fi, _)
  | PatSeqEdge (fi, _, _, _)
  | PatRecord (fi, _)
  | PatCon (fi, _, _, _)
  | PatInt (fi, _)
  | PatChar (fi, _)
  | PatBool (fi, _)
  | PatAnd (fi, _, _)
  | PatOr (fi, _, _)
  | PatNot (fi, _) ->
      fi

let ty_info = function
  | TyUnknown fi
  | TyBool fi
  | TyInt fi
  | TyFloat fi
  | TyChar fi
  | TyArrow (fi, _, _)
  | TyAll (fi, _, _)
  | TySeq (fi, _)
  | TyTensor (fi, _)
  | TyRecord (fi, _)
  | TyVariant (fi, _)
  | TyCon (fi, _, _)
  | TyVar (fi, _)
  | TyApp (fi, _, _) ->
      fi

(* Checks if a constant _may_ have a side effect. It is conservative
   and returns only false if it is _sure_ to not have a side effect *)
let const_has_side_effect = function
  | CunsafeCoerce
  | CBool _
  | CInt _
  | Caddi _
  | Csubi _
  | Cmuli _
  | Cdivi _
  | Cmodi _
  | Cnegi
  | Clti _
  | Cleqi _
  | Cgti _
  | Cgeqi _
  | Ceqi _
  | Cneqi _
  | Cslli _
  | Csrli _
  | Csrai _
  | Carity ->
      false
  (* MCore intrinsics: Floating-point numbers *)
  | CFloat _
  | Caddf _
  | Csubf _
  | Cmulf _
  | Cdivf _
  | Cnegf
  | Cltf _
  | Cleqf _
  | Cgtf _
  | Cgeqf _
  | Ceqf _
  | Cneqf _
  | Cfloorfi
  | Cceilfi
  | Croundfi
  | Cint2float
  | CstringIsFloat
  | Cstring2float
  | Cfloat2string ->
      false
  (* MCore intrinsics: Characters *)
  | CChar _ | Ceqc _ | Cchar2int | Cint2char ->
      false
  (* MCore intrinsic: sequences *)
  | Ccreate _
  | CcreateList _
  | CcreateRope _
  | CisList
  | CisRope
  | Clength
  | Cconcat _
  | Cget _
  | Cset _
  | Ccons _
  | Csnoc _
  | CsplitAt _
  | Creverse
  | Chead
  | Ctail
  | Cnull
  | Cmap _
  | Cmapi _
  | Citer _
  | Citeri _
  | Cfoldl _
  | Cfoldr _
  | Csubsequence _ ->
      false
  (* MCore intrinsics: Random numbers *)
  | CrandIntU _ ->
      true
  | CrandSetSeed ->
      true
  (* MCore intrinsics: Time *)
  | CwallTimeMs ->
      true
  | CsleepMs ->
      true
  (* MCore intrinsics: Debug and I/O *)
  | Cprint
  | CprintError
  | Cdprint
  | CreadLine
  | CreadBytesAsString
  | CreadFile
  | CwriteFile _
  | CfileExists
  | CdeleteFile
  | Ccommand
  | Cerror
  | Cexit
  | CflushStdout
  | CflushStderr ->
      true
  (* MCore intrinsics: Symbols *)
  | CSymb _ | Cgensym | Ceqsym _ | Csym2hash ->
      true
  (* MCore intrinsics: Constructor tag *)
  | CconstructorTag ->
      true
  (* MCore intrinsics: References *)
  | Cref | CmodRef _ | CdeRef ->
      true
  (* MCore intrinsics: Maps *)
  (* NOTE(Linnea, 2021-01-27): Obj.t denotes the type of the internal map (I was so far unable to express it properly) *)
  | CMap _
  | CmapEmpty
  | CmapSize
  | CmapGetCmpFun
  | CmapInsert _
  | CmapRemove _
  | CmapFindExn _
  | CmapFindOrElse _
  | CmapFindApplyOrElse _
  | CmapMem _
  | CmapAny _
  | CmapMap _
  | CmapMapWithKey _
  | CmapFoldWithKey _
  | CmapBindings
  | CmapChooseExn
  | CmapChooseOrElse _
  | CmapEq _
  | CmapCmp _ ->
      false
  (* MCore intrinsics: Tensors *)
  | CtensorCreateDense _
  | CtensorCreateUninitInt
  | CtensorCreateUninitFloat
  | CtensorCreateCArrayInt _
  | CtensorCreateCArrayFloat _
  | CtensorGetExn _
  | CtensorSetExn _
  | CtensorLinearGetExn _
  | CtensorLinearSetExn _
  | CtensorRank
  | CtensorShape
  | CtensorCopy
  | CtensorTransposeExn _
  | CtensorReshapeExn _
  | CtensorSliceExn _
  | CtensorSubExn _
  | CtensorIterSlice _
  | CtensorEq _
  | Ctensor2string _ ->
      true
  (* MCore Boot parser *)
  | CbootParserTree _
  | CbootParserParseMExprString _
  | CbootParserParseMCoreFile _
  | CbootParserGetId
  | CbootParserGetTerm _
  | CbootParserGetType _
  | CbootParserGetString _
  | CbootParserGetInt _
  | CbootParserGetFloat _
  | CbootParserGetListLength _
  | CbootParserGetConst _
  | CbootParserGetPat _
  | CbootParserGetInfo _ ->
      true
  (* External functions *)
  | CPy _ ->
      true

(* Converts a sequence of terms to a sequence of integers *)
let tmseq2seq_of_int fi s =
  Mseq.map
    (fun x ->
      match x with
      | TmConst (_, CChar i) ->
          i
      | _ ->
          raise_error fi "The term is not a string" )
    s

(* Converts a sequence of terms to a ustring *)
let tmseq2ustring fi s = tmseq2seq_of_int fi s |> Mseq.Helpers.to_ustring

(* Converts a ustring to a sequence of terms *)
let ustring2tmseq fi s =
  s |> Mseq.Helpers.of_ustring |> Mseq.map (fun x -> TmConst (fi, CChar x))

(* Converts a list of terms (for a tuple) to a record term *)
let tuple2record fi lst =
  let r =
    List.fold_left
      (fun (i, a) x -> (i + 1, Record.add (ustring_of_int i) x a))
      (0, Record.empty) lst
  in
  TmRecord (fi, snd r)

(* Converts a list of types (for a tuple type) to a record type *)
let tuplety2recordty fi lst =
  let _, r =
    List.fold_left
      (fun (i, a) x -> (i + 1, Record.add (ustring_of_int i) x a))
      (0, Record.empty) lst
  in
  TyRecord (fi, r)

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
