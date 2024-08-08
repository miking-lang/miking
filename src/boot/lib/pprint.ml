(** Pretty-printing for data types in Miking.
 *
 *  The main functions that should be used outside of this module is
 *  - ustring_of_tm
 *  - ustring_of_const
 *  - ustring_of_env
 *
 *  Miking is licensed under the MIT license.
 *  Copyright (C) David Broman. See file LICENSE.txt *)

open Ast
open Format
open Ustring.Op
open Intrinsics

(** Global configuration for symbol printing. Needed because of the unwieldy
 *  interface to the Format module *)
let ref_symbol = ref false

(** Global configuration for indentation size. Needed because of the unwieldy
 *  interface to the Format module *)
let ref_indent = ref 2

(** Alias for converting from ustring to string *)
let string_of_ustring = Ustring.to_utf8

(** Ensure strings can be parsed *)
let parser_str s prefix cond =
  match Ustring.length s with
  | 0 ->
      prefix ^. us "\"\""
  | _ when cond s ->
      s
  | _ ->
      prefix ^. us "\"" ^. s ^. us "\""

(** Variable string parser translation *)
let pprint_var_str s =
  parser_str s (us "#var") (fun s ->
      is_ascii_lower_alpha (Ustring.get s 0)
      || (Ustring.starts_with (us "_") s && Ustring.length s > 1) )

(** Frozen variable string parser translation *)
let pprint_frozen_str s = parser_str s (us "#frozen") (fun _ -> false)

(** Constructor string parser translation *)
let pprint_con_str s =
  parser_str s (us "#con") (fun s ->
      let c = Ustring.get s 0 in
      is_ascii_upper_alpha c )

(** Type constructor string parser translation *)
let pprint_type_str s =
  parser_str s (us "#type") (fun s ->
      let c = Ustring.get s 0 in
      is_ascii_upper_alpha c )

(** Label string parser translation *)
let pprint_label_str s =
  parser_str s (us "#label") (fun s ->
      is_ascii_lower_alpha (Ustring.get s 0)
      || (Ustring.starts_with (us "_") s && Ustring.length s > 1) )

(** Create string representation of an identifier *)
let ustring_of_ident symbol pprint_ident x s =
  if symbol then
    pprint_ident x
    ^.
    if Symb.eqsym Symb.Helpers.nosym s then us "#"
    else us "#" ^. Symb.Helpers.ustring_of_sym s
  else pprint_ident x

(** Create string representation of a variable *)
let ustring_of_var ?(symbol = !ref_symbol) x s =
  ustring_of_ident symbol pprint_var_str x s

(** Create string representation of a frozen variable *)
let ustring_of_frozen ?(symbol = !ref_symbol) x s =
  ustring_of_ident symbol pprint_frozen_str x s

(** Create string representation of a constructor *)
let ustring_of_con ?(symbol = !ref_symbol) x s =
  ustring_of_ident symbol pprint_con_str x s

(** Create string representation of a type constructor *)
let ustring_of_type ?(symbol = !ref_symbol) x s =
  ustring_of_ident symbol pprint_type_str x s

(** Create a string from a uchar, as it would appear in a string literal. *)
let lit_of_uchar c =
  let str =
    match string_of_ustring (Ustring.from_uchars [|c|]) with
    | "\n" ->
        "\\n"
    | "\t" ->
        "\\t"
    | "\\" ->
        "\\\\"
    | "\'" ->
        "\\'"
    | "\"" ->
        "\\\""
    | str ->
        str
  in
  Printf.sprintf "'%s'" str

(** Convert pattern to ustring.
 *  TODO(dlunde,?): Precedence
 *  TODO(dlunde,?): Use Format module printing *)
let ustring_of_pat p =
  let rec ppp pat =
    let ppSeq s =
      s |> Mseq.Helpers.to_list |> List.map ppp |> Ustring.concat (us ",")
    in
    let ppName = function
      | NameStr (x, s) ->
          ustring_of_var x s
      | NameWildcard ->
          us "_"
    in
    match pat with
    | PatNamed (_, NameStr (x, s)) ->
        ustring_of_var x s
    | PatSeqEdge (_, l, x, r) ->
        if Mseq.length l = 0 && Mseq.length r = 0 then us "[] ++ " ^. ppName x
        else
          let rStr =
            if Mseq.length r <> 0 then us " ++ [" ^. ppSeq r ^. us "]"
            else us ""
          in
          let lStr =
            if Mseq.length l <> 0 then us "[" ^. ppSeq l ^. us "] ++ "
            else us ""
          in
          lStr ^. ppName x ^. rStr
    | PatSeqTot (_, lst) ->
        us "[" ^. ppSeq lst ^. us "]"
    | PatNamed (_, NameWildcard) ->
        us "_"
    | PatRecord (_, ps) ->
        let ps =
          Record.bindings ps
          |> List.map (fun (label, p) ->
                 pprint_label_str label ^. us " = " ^. ppp p )
          |> Ustring.concat (us ",")
        in
        us "{" ^. ps ^. us "}"
    | PatCon (_, x, n, p) ->
        let con = ustring_of_con x n in
        let inner = ppp p in
        con ^. us "(" ^. inner ^. us ")"
    | PatInt (_, i) ->
        Ustring.Op.ustring_of_int i
    | PatChar (_, c) ->
        us (lit_of_uchar c)
    | PatBool (_, b) ->
        ustring_of_bool b
    | PatAnd (_, l, r) ->
        us "(" ^. ppp l ^. us " & " ^. ppp r ^. us ")"
    | PatOr (_, l, r) ->
        us "(" ^. ppp l ^. us " | " ^. ppp r ^. us ")"
    | PatNot (_, p) ->
        us "!(" ^. ppp p ^. us ")"
  in
  ppp p

(** Convert type to ustring.
 *  TODO(dlunde,?): Precedence
 *  TODO(dlunde,?): Use Format module printing *)
let rec ustring_of_ty = function
  | TyUnknown _ ->
      us "Unknown"
  | TyBool _ ->
      us "Bool"
  | TyInt _ ->
      us "Int"
  | TyFloat _ ->
      us "Float"
  | TyChar _ ->
      us "Char"
  | TyArrow (_, ty1, ty2) ->
      us "(" ^. ustring_of_ty ty1 ^. us "->" ^. ustring_of_ty ty2 ^. us ")"
  | TyAll (_, var, _, ty) ->
      us "all " ^. pprint_var_str var ^. us ". " ^. ustring_of_ty ty
  | TySeq (_, ty1) -> (
    match ty1 with
    | TyChar _ ->
        us "String"
    | _ ->
        us "[" ^. ustring_of_ty ty1 ^. us "]" )
  | TyTensor (_, ty) ->
      us "Tensor[" ^. ustring_of_ty ty ^. us "]"
  | TyRecord (_, r) when r = Record.empty ->
      us "()"
  | TyRecord (_, r) ->
      let pprint_ty_label (l, ty) =
        pprint_label_str l ^. us " : " ^. ustring_of_ty ty
      in
      us "{"
      ^. Ustring.concat (us ",") (List.map pprint_ty_label (Record.bindings r))
      ^. us "}"
  | TyVariant (_, tys) when tys = [] ->
      us "<>"
  | TyVariant _ ->
      failwith "Printing of non-empty variant types not yet supported"
  | TyCon (_, x, _) ->
      pprint_type_str x
  | TyVar (_, x) ->
      pprint_var_str x
  | TyUse (_, lang, ty) ->
      us "use " ^. lang ^. us " in " ^. ustring_of_ty ty
  | TyApp (_, ty1, ty2) ->
      us "(" ^. ustring_of_ty ty1 ^. us " " ^. ustring_of_ty ty2 ^. us ")"

(** Simple enum used in the concat function in ustring_of_tm *)
type sep = Space | Comma

(** Function for concatenating a list of fprintf calls using a given separator.
 *  TODO(dlunde,?) Possible to simply use Format.pp_print_list? *)
let rec concat fmt (sep, ls) =
  match ls with
  | [] ->
      ()
  | [f] ->
      f fmt
  | f :: ls -> (
    match sep with
    | Space ->
        fprintf fmt "%t@ %a" f concat (sep, ls)
    | Comma ->
        fprintf fmt "%t,@,%a" f concat (sep, ls) )

(** Precedence constants for printing *)
type prec = Match | Lam | Semicolon | If | Tup | App | Atom

(** Print a constant on the given formatter
 *  TODO(dlunde,?): Precendece?
 *  TODO(dlunde,?): Break hints? *)
let rec print_const fmt = function
  | CunsafeCoerce ->
      fprintf fmt "unsafeCoerce"
  (* MCore intrinsics: Booleans *)
  | CBool b ->
      fprintf fmt "%B" b
  (* MCore intrinsics: Integers *)
  | CInt v ->
      fprintf fmt "%d" v
  | Caddi None ->
      fprintf fmt "addi"
  | Caddi (Some v) ->
      fprintf fmt "addi(%d)" v
  | Csubi None ->
      fprintf fmt "subi"
  | Csubi (Some v) ->
      fprintf fmt "subi(%d)" v
  | Cmuli None ->
      fprintf fmt "muli"
  | Cmuli (Some v) ->
      fprintf fmt "muli(%d)" v
  | Cdivi None ->
      fprintf fmt "divi"
  | Cdivi (Some v) ->
      fprintf fmt "divi(%d)" v
  | Cmodi None ->
      fprintf fmt "modi"
  | Cmodi (Some v) ->
      fprintf fmt "modi(%d)" v
  | Cnegi ->
      fprintf fmt "negi"
  | Clti None ->
      fprintf fmt "lti"
  | Clti (Some v) ->
      fprintf fmt "lti(%d)" v
  | Cleqi None ->
      fprintf fmt "leqi"
  | Cleqi (Some v) ->
      fprintf fmt "leqi(%d)" v
  | Cgti None ->
      fprintf fmt "gti"
  | Cgti (Some v) ->
      fprintf fmt "gti(%d)" v
  | Cgeqi None ->
      fprintf fmt "geqi"
  | Cgeqi (Some v) ->
      fprintf fmt "geqi(%d)" v
  | Ceqi None ->
      fprintf fmt "eqi"
  | Ceqi (Some v) ->
      fprintf fmt "eqi(%d)" v
  | Cneqi None ->
      fprintf fmt "neqi"
  | Cneqi (Some v) ->
      fprintf fmt "neqi(%d)" v
  | Cslli None ->
      fprintf fmt "slli"
  | Cslli (Some v) ->
      fprintf fmt "slli(%d)" v
  | Csrli None ->
      fprintf fmt "srli"
  | Csrli (Some v) ->
      fprintf fmt "srli(%d)" v
  | Csrai None ->
      fprintf fmt "srai"
  | Csrai (Some v) ->
      fprintf fmt "srai(%d)" v
  | Carity ->
      fprintf fmt "arity"
  (* MCore intrinsics: Floating-point numbers *)
  | CFloat v ->
      fprintf fmt "%f" v
  | Caddf None ->
      fprintf fmt "addf"
  | Caddf (Some v) ->
      fprintf fmt "addf(%f)" v
  | Csubf None ->
      fprintf fmt "subf"
  | Csubf (Some v) ->
      fprintf fmt "subf(%f)" v
  | Cmulf None ->
      fprintf fmt "mulf"
  | Cmulf (Some v) ->
      fprintf fmt "mulf(%f)" v
  | Cdivf None ->
      fprintf fmt "divf"
  | Cdivf (Some v) ->
      fprintf fmt "divf(%f)" v
  | Cnegf ->
      fprintf fmt "negf"
  | Cltf None ->
      fprintf fmt "ltf"
  | Cltf (Some v) ->
      fprintf fmt "ltf(%f)" v
  | Cleqf None ->
      fprintf fmt "leqf"
  | Cleqf (Some v) ->
      fprintf fmt "leqf(%f)" v
  | Cgtf None ->
      fprintf fmt "gtf"
  | Cgtf (Some v) ->
      fprintf fmt "gtf(%f)" v
  | Cgeqf None ->
      fprintf fmt "geqf"
  | Cgeqf (Some v) ->
      fprintf fmt "geqf(%f)" v
  | Ceqf None ->
      fprintf fmt "eqf"
  | Ceqf (Some v) ->
      fprintf fmt "eqf(%f)" v
  | Cneqf None ->
      fprintf fmt "neqf"
  | Cneqf (Some v) ->
      fprintf fmt "neqf(%f)" v
  | Cfloorfi ->
      fprintf fmt "floorfi"
  | Cceilfi ->
      fprintf fmt "ceilfi"
  | Croundfi ->
      fprintf fmt "roundfi"
  | Cint2float ->
      fprintf fmt "int2float"
  | CstringIsFloat ->
      fprintf fmt "stringIsFloat"
  | Cstring2float ->
      fprintf fmt "string2float"
  | Cfloat2string ->
      fprintf fmt "float2string"
  (* MCore intrinsics: Characters *)
  | CChar v ->
      fprintf fmt "%s" (lit_of_uchar v)
  | Ceqc None ->
      fprintf fmt "eqc"
  | Ceqc (Some v) ->
      fprintf fmt "eqc(%d)" v
  | Cchar2int ->
      fprintf fmt "char2int"
  | Cint2char ->
      fprintf fmt "int2char"
  (* MCore intrinsic: sequences *)
  | Ccreate _ ->
      fprintf fmt "create"
  | CcreateList _ ->
      fprintf fmt "createList"
  | CcreateRope _ ->
      fprintf fmt "createRope"
  | CisList ->
      fprintf fmt "isList"
  | CisRope ->
      fprintf fmt "isRope"
  | Clength ->
      fprintf fmt "length"
  | Cconcat _ ->
      fprintf fmt "concat"
  | Cget _ ->
      fprintf fmt "get"
  | Cset _ ->
      fprintf fmt "set"
  | Ccons _ ->
      fprintf fmt "cons"
  | Csnoc _ ->
      fprintf fmt "snoc"
  | CsplitAt _ ->
      fprintf fmt "splitAt"
  | Creverse ->
      fprintf fmt "reverse"
  | Chead ->
      fprintf fmt "head"
  | Ctail ->
      fprintf fmt "tail"
  | Cnull ->
      fprintf fmt "null"
  | Cmap _ ->
      fprintf fmt "map"
  | Cmapi _ ->
      fprintf fmt "mapi"
  | Citer _ ->
      fprintf fmt "iter"
  | Citeri _ ->
      fprintf fmt "iteri"
  | Cfoldl _ ->
      fprintf fmt "foldl"
  | Cfoldr _ ->
      fprintf fmt "foldr"
  | Csubsequence _ ->
      fprintf fmt "subsequence"
  (* MCore intrinsics: Random numbers *)
  | CrandIntU _ ->
      fprintf fmt "randIntU"
  | CrandSetSeed ->
      fprintf fmt "randSetSeed"
  (* MCore intrinsics: Time *)
  | CwallTimeMs ->
      fprintf fmt "wallTimeMs"
  | CsleepMs ->
      fprintf fmt "sleepMs"
  (* MCore intrinsics: Debug and I/O *)
  | Cprint ->
      fprintf fmt "print"
  | CprintError ->
      fprintf fmt "printError"
  | Cdprint ->
      fprintf fmt "dprint"
  | CreadLine ->
      fprintf fmt "readLine"
  | CreadBytesAsString ->
      fprintf fmt "readBytesAsString"
  | CreadFile ->
      fprintf fmt "readFile"
  | CwriteFile _ ->
      fprintf fmt "writeFile"
  | CfileExists ->
      fprintf fmt "fileExists"
  | CdeleteFile ->
      fprintf fmt "deleteFile"
  | Ccommand ->
      fprintf fmt "command"
  | Cerror ->
      fprintf fmt "error"
  | Cexit ->
      fprintf fmt "exit"
  | CflushStdout ->
      fprintf fmt "flushStdout"
  | CflushStderr ->
      fprintf fmt "flushStderr"
  (* MCore intrinsics: Symbols *)
  | CSymb id ->
      fprintf fmt "symb(%s)" (Symb.Helpers.string_of_sym id)
  | Cgensym ->
      fprintf fmt "gensym"
  | Ceqsym _ ->
      fprintf fmt "eqsym"
  | Csym2hash ->
      fprintf fmt "sym2hash"
  (* MCore intrinsics: Constructor tag *)
  | CconstructorTag ->
      fprintf fmt "constructorTag"
  (* MCore intrinsics: References *)
  | Cref ->
      fprintf fmt "ref"
  | CmodRef _ ->
      fprintf fmt "modref"
  | CdeRef ->
      fprintf fmt "deref"
  (* MCore intrinsics: Tensors *)
  | CtensorCreateDense _ ->
      fprintf fmt "tensorCreateDense"
  | CtensorCreateUninitInt ->
      fprintf fmt "tensorCreateUninitInt"
  | CtensorCreateUninitFloat ->
      fprintf fmt "tensorCreateUninitFloat"
  | CtensorCreateCArrayInt _ ->
      fprintf fmt "tensorCreateCArrayInt"
  | CtensorCreateCArrayFloat _ ->
      fprintf fmt "tensorCreateCArrayFloat"
  | CtensorGetExn _ ->
      fprintf fmt "tensorGetExn"
  | CtensorSetExn _ ->
      fprintf fmt "tensorSetExn"
  | CtensorLinearGetExn _ ->
      fprintf fmt "tensorLinearGetExn"
  | CtensorLinearSetExn _ ->
      fprintf fmt "tensorLinearSetExn"
  | CtensorRank ->
      fprintf fmt "tensorRank"
  | CtensorShape ->
      fprintf fmt "tensorShape"
  | CtensorCopy ->
      fprintf fmt "tensorCopy"
  | CtensorTransposeExn _ ->
      fprintf fmt "tensorTransposeExn"
  | CtensorReshapeExn _ ->
      fprintf fmt "tensorReshapeExn"
  | CtensorSliceExn _ ->
      fprintf fmt "tensorSliceExn"
  | CtensorSubExn _ ->
      fprintf fmt "tensorSubExn"
  | CtensorIterSlice _ ->
      fprintf fmt "tensorIterSlice"
  | CtensorEq _ ->
      fprintf fmt "tensorEq"
  | Ctensor2string _ ->
      fprintf fmt "tensor2string"
  (* MCore intrinsics: Boot parser *)
  | CbootParserTree _ ->
      fprintf fmt "bootParseTree"
  | CbootParserParseMExprString _ ->
      fprintf fmt "bootParserParseMExprString"
  | CbootParserParseMLangString _ ->
      fprintf fmt "bootParserParseMLangString"
  | CbootParserParseMLangFile _ ->
      fprintf fmt "bootParserParseMLangFile"
  | CbootParserParseMCoreFile _ ->
      fprintf fmt "bootParserParseMCoreFile"
  | CbootParserGetId ->
      fprintf fmt "bootParserParseGetId"
  | CbootParserGetTerm _ ->
      fprintf fmt "bootParserParseGetTerm"
  | CbootParserGetTop _ ->
      fprintf fmt "bootParserParseGetTop"
  | CbootParserGetDecl _ ->
      fprintf fmt "bootParserParseGetDecl"
  | CbootParserGetType _ ->
      fprintf fmt "bootParserParseGetType"
  | CbootParserGetString _ ->
      fprintf fmt "bootParserParseGetString"
  | CbootParserGetInt _ ->
      fprintf fmt "bootParserParseGetInt"
  | CbootParserGetFloat _ ->
      fprintf fmt "bootParserParseGetFloat"
  | CbootParserGetListLength _ ->
      fprintf fmt "bootParserParseGetListLength"
  | CbootParserGetConst _ ->
      fprintf fmt "bootParserParseGetConst"
  | CbootParserGetPat _ ->
      fprintf fmt "bootParserParseGetPat"
  | CbootParserGetInfo _ ->
      fprintf fmt "bootParserParseGetInfo"
  (* Python intrinsics *)
  | CPy v ->
      fprintf fmt "%s" (string_of_ustring (Pypprint.pprint v))

(** Pretty print a record *)
and print_record fmt r =
  let print (l, t) =
    let l = string_of_ustring (pprint_label_str l) in
    fun fmt -> fprintf fmt "%s = %a" l print_tm (App, t)
  in
  let inner = List.map print r in
  fprintf fmt "{@[<hov 0>%a@]}" concat (Comma, inner)

(** Print a term on the given formatter and within the given precedence. *)
and print_tm fmt (prec, t) =
  let paren =
    prec
    >
    match t with
    | TmMatch (_, _, PatBool (_, true), _, _) ->
        If
    | TmMatch _ | TmLet _ | TmType _ | TmExt _ ->
        Match
    | TmLam _ ->
        Lam
    | TmConApp _ | TmSeq _ ->
        Semicolon
    | TmApp _ ->
        App
    | TmVar _
    | TmRecLets _
    | TmConst _
    | TmRecord _
    | TmRecordUpdate _
    | TmConDef _
    | TmUse _
    | TmUtest _
    | TmClos _
    | TmNever _
    | TmRef _
    | TmDive _
    | TmPreRun _
    | TmBox _
    | TmTensor _ ->
        Atom
  in
  if paren then fprintf fmt "(%a)" print_tm' t
  else fprintf fmt "%a" print_tm' t

(** Auxiliary print function *)
and print_tm' fmt t =
  let print_ty_if_known tystr =
    if tystr = "Unknown" then "" else ":" ^ tystr
  in
  match t with
  | TmVar (_, x, s, _, frozen) ->
      let var_str =
        if frozen then string_of_ustring (ustring_of_frozen x s)
        else string_of_ustring (ustring_of_var x s)
      in
      (*  fprintf fmt "%s#%d" print s *)
      fprintf fmt "%s" var_str
  | TmLam (_, x, s, _, ty, t1) ->
      let x = string_of_ustring (ustring_of_var x s) in
      let ty = ty |> ustring_of_ty |> string_of_ustring in
      fprintf fmt "@[<hov %d>lam %s%s.@ %a@]" !ref_indent x
        (print_ty_if_known ty) print_tm (Lam, t1)
  | TmLet (_, x, s, ty, t1, t2) ->
      if Ustring.length x = 0 then
        fprintf fmt "@[<hov 0>@[<hov %d>%a;@]@ %a@]" !ref_indent print_tm
          (Match, t1) print_tm (Match, t2)
      else
        let x = string_of_ustring (ustring_of_var x s) in
        let ty = ty |> ustring_of_ty |> string_of_ustring in
        fprintf fmt "@[<hov 0>@[<hov %d>let %s%s =@ %a in@]@ %a@]" !ref_indent
          x (print_ty_if_known ty) print_tm (Match, t1) print_tm (Match, t2)
  | TmType (_, x, params, ty, t1) ->
      let x = string_of_ustring (pprint_type_str x) in
      let params =
        params |> List.map string_of_ustring |> List.cons ""
        |> String.concat " "
      in
      let ty = ty |> ustring_of_ty |> string_of_ustring in
      fprintf fmt "@[<hov 0>@[<hov %d>type %s%s =@ %s in@]@ %a@]" !ref_indent x
        params ty print_tm (Match, t1)
  | TmRecLets (_, lst, t2) -> (
      let print (_, x, s, ty, t) =
        let x = string_of_ustring (ustring_of_var x s) in
        let ty = ty |> ustring_of_ty |> string_of_ustring in
        fun fmt ->
          fprintf fmt "@[<hov %d>let %s%s =@ %a@]" !ref_indent x
            (print_ty_if_known ty) print_tm (Match, t)
      in
      match lst with
      | [] ->
          fprintf fmt "@[<hov 0>%a@]" print_tm (Match, t2)
      | _ ->
          let inner = List.map print lst in
          fprintf fmt "@[<hov 0>@[<hov %d>recursive@ @[<hov 0>%a@] in@]@ %a@]"
            !ref_indent concat (Space, inner) print_tm (Match, t2) )
  | TmApp (_, t1, (TmApp _ as t2)) ->
      fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (App, t1) print_tm (Atom, t2)
  | TmApp (_, t1, t2) ->
      fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (App, t1) print_tm (App, t2)
  | TmConst (_, c) ->
      print_const fmt c
  | TmSeq (fi, tms) -> (
      if Mseq.length tms = 0 then fprintf fmt "[]"
      else
        try
          tmseq2ustring fi tms |> string_of_ustring |> String.escaped
          |> fprintf fmt "\"%s\""
        with _ ->
          let print t fmt = fprintf fmt "%a" print_tm (App, t) in
          let inner = List.map print (Mseq.Helpers.to_list tms) in
          fprintf fmt "[@[<hov 0>%a@]]" concat (Comma, inner) )
  | TmRecord (_, r) -> (
    match record2tuple r with
    | Some [tm] ->
        fprintf fmt "(%a,)" print_tm (App, tm)
    | Some tms ->
        let print t fmt = fprintf fmt "%a" print_tm (App, t) in
        let inner = List.map print (List.rev tms) in
        fprintf fmt "(@[<hov 0>%a@])" concat (Comma, inner)
    | None ->
        let contents = Record.fold (fun l v ack -> (l, v) :: ack) r [] in
        print_record fmt contents )
  | TmRecordUpdate (_, t1, l, t2) ->
      let l = string_of_ustring l in
      (* TODO(?,?): The below Atom precedences can probably be made less conservative *)
      fprintf fmt "{%a with %s = %a}" print_tm (Atom, t1) l print_tm (Atom, t2)
  | TmConDef (_, x, s, ty, t) ->
      let str = string_of_ustring (ustring_of_con x s) in
      let ty = ty |> ustring_of_ty |> string_of_ustring in
      fprintf fmt "@[<hov 0>con %s%s in@ %a@]" str (print_ty_if_known ty)
        print_tm (Match, t)
  | TmConApp (_, x, sym, t) ->
      let str = string_of_ustring (ustring_of_con x sym) in
      fprintf fmt "%s %a" str print_tm (Atom, t)
  (* If expressions *)
  | TmMatch (_, t1, PatBool (_, true), t2, t3) ->
      fprintf fmt "@[<hov %d>if %a@ @[<hov 0>then %a@ else %a@]@]" !ref_indent
        print_tm (Match, t1) print_tm (Match, t2) print_tm (If, t3)
  | TmMatch (_, t, p, then_, else_) ->
      let p = p |> ustring_of_pat |> string_of_ustring in
      fprintf fmt "@[<hov %d>match %a@ @[<hov 0>with %s@ then %a@ else %a@]@]"
        !ref_indent print_tm (Match, t) p print_tm (If, then_) print_tm
        (If, else_)
  | TmUse (_, l, t) ->
      let l = string_of_ustring l in
      fprintf fmt "@[<hov 0>use %s in@ %a@]" l print_tm (Match, t)
  | TmUtest (_, t1, t2, None, None, t4) ->
      fprintf fmt "@[<hov 0>@[<hov %d>utest@ @[<hov 0>%a with@ %a in@]@]@ %a@]"
        !ref_indent print_tm (Match, t1) print_tm (Match, t2) print_tm
        (Match, t4)
  | TmUtest (_, t1, t2, Some t3, None, t4) ->
      fprintf fmt
        "@[<hov 0>@[<hov %d>utest@ @[<hov 0>%a with@ %a using@ %a in@]@]@ %a@]"
        !ref_indent print_tm (Match, t1) print_tm (Match, t2) print_tm
        (Match, t3) print_tm (Match, t4)
  | TmUtest (_, t1, t2, None, Some t3, t4) ->
      fprintf fmt
        "@[<hov 0>@[<hov %d>utest@ @[<hov 0>%a with@ %a onfail@ %a in@]@]@ \
         %a@]"
        !ref_indent print_tm (Match, t1) print_tm (Match, t2) print_tm
        (Match, t3) print_tm (Match, t4)
  | TmUtest (_, t1, t2, Some t3, Some t4, t5) ->
      fprintf fmt
        "@[<hov 0>@[<hov %d>utest@ @[<hov 0>%a with@ %a using@ %a onfail@ %a \
         in@]@]@ %a@]"
        !ref_indent print_tm (Match, t1) print_tm (Match, t2) print_tm
        (Match, t3) print_tm (Match, t4) print_tm (Match, t5)
  | TmClos (_, x, _, _, t1, _) ->
      let x = string_of_ustring x in
      fprintf fmt "@[<hov %d>clos %s.@ %a@]" !ref_indent x print_tm (Lam, t1)
  | TmNever _ ->
      fprintf fmt "never"
  | TmRef (_, _) ->
      fprintf fmt "(ref)"
  | TmDive (_, _, t) ->
      fprintf fmt "@[<hv 0>dive %a@]" print_tm (Match, t)
  | TmPreRun (_, _, t) ->
      fprintf fmt "@[<hv 0>prerun %a@]" print_tm (Match, t)
  | TmBox (_, _) ->
      fprintf fmt "(box)"
  | TmTensor (_, t) ->
      let float_ f = TmConst (NoInfo, CFloat f) in
      let int_ n = TmConst (NoInfo, CInt n) in
      let shape, data =
        t
        |> function
        | T.TBootInt t' ->
            ( t' |> Tensor.Barray.shape
            , t' |> Tensor.Uop_barray.to_data_array |> Array.map int_ )
        | T.TBootFloat t' ->
            ( t' |> Tensor.Barray.shape
            , t' |> Tensor.Uop_barray.to_data_array |> Array.map float_ )
        | T.TBootGen t' ->
            (t' |> Tensor.Generic.shape, t' |> Tensor.Uop_generic.to_data_array)
      in
      let print t fmt = fprintf fmt "%a" print_tm (App, t) in
      let shape' =
        shape |> Array.map int_ |> Array.to_list |> List.map print
      in
      let data' = List.map print (Array.to_list data) in
      fprintf fmt "Tensor([@[<hov 0>%a@]], [@[<hov 0>%a@]])" concat
        (Comma, shape') concat (Comma, data')
  | TmExt (_, x, s, e, ty, t) ->
      let x = string_of_ustring (ustring_of_var x s) in
      let ty = ty |> ustring_of_ty |> string_of_ustring in
      let e = if e then "!" else "" in
      fprintf fmt "@[<hov 0>@[<hov %d>external %s %s : %s in@]@ %a@]"
        !ref_indent x e ty print_tm (Match, t)

(** Print an environment on the given formatter. *)
and print_env fmt env =
  let print (s, t) fmt =
    fprintf fmt "#%s -> %a" (Symb.Helpers.string_of_sym s) print_tm (Match, t)
  in
  let inner = List.map print env in
  fprintf fmt "[@[<hov 0>%a@]]" concat (Comma, inner)

(** Helper function for configuring the string formatter and printing *)
let ustr_formatter_print ?(symbol = !enable_debug_symbol_print) ?(indent = 2)
    ?(max_indent = 68) ?(margin = 79) ?(max_boxes = max_int) ?(prefix = "")
    printer arg =
  (* Configure global settings *)
  ref_symbol := symbol ;
  ref_indent := indent ;
  pp_set_margin str_formatter margin ;
  pp_set_max_indent str_formatter max_indent ;
  pp_set_max_boxes str_formatter max_boxes ;
  (* Make sure formatter is cleared *)
  ignore (flush_str_formatter ()) ;
  (* Print a prefix *)
  fprintf str_formatter "%s" prefix ;
  (* Do the actual printing *)
  printer str_formatter arg ;
  (* Return result string and clear formatter *)
  flush_str_formatter () |> us

(** Convert terms to strings.
 *  TODO(dlunde,?): Messy with optional arguments passing. Alternatives? *)
let ustring_of_tm ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix t =
  ustr_formatter_print ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_tm (Match, t)

(** Converting constants to strings.
 *  TODO(dlunde,?): Messy with optional arguments passing. Alternatives? *)
let ustring_of_const ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix c =
  ustr_formatter_print ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_const c

(** Converting environments to strings.
 *  TODO(dlunde,?): Messy with optional arguments passing. Alternatives? *)
let ustring_of_env ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix e =
  ustr_formatter_print ?symbol ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_env e

(** TODO(dlunde,?): Print mlang part as well. *)
let ustring_of_program tml =
  match tml with Program (_, _, t) -> ustring_of_tm t
