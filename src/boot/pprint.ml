(** Pretty-printing for data types in Miking.
 *
 *  The main functions that should be used outside of this module is
 *  - string_of_tm
 *  - string_of_const
 *  - string_of_env
 *
 *  Miking is licensed under the MIT license.
 *  Copyright (C) David Broman. See file LICENSE.txt *)

open Ast
open Format
open Ustring.Op

(** Whether or not debruijn printin is the default (this can still be changed
 *  through optional arguments) *)
let enable_debug_debruijn_print = ref false

(** Global configuration for debruijn printing. Needed because of the unwieldy
 *  interface to the Format module *)
let ref_debruijn = ref false

(** Global configuration for indentation size. Needed because of the unwieldy
 *  interface to the Format module *)
let ref_indent      = ref 2

(** Alias for converting from ustring to string *)
let string_of_ustring = Ustring.to_utf8

(** Create string representation of variable *)
let ustring_of_var x n =
  if !ref_debruijn
  then x ^. us(sprintf "'%d" n) else x

(** Create a string from a uchar, as it would appear in a string literal. *)
let lit_of_uchar c =
  let str = match (string_of_ustring (Ustring.from_uchars [|c|])) with
    (* TODO This is a temporary fix for newlines only. How do we do this
       properly? *)
    | "\n" -> "\\n"
    | str -> str in
  Printf.sprintf "'%s'" str

(** Convert pattern to ustring.
 *  TODO Precedence
 *  TODO Use Format module printing *)
let ustring_of_pat p =
  let rec ppp pat =
    let ppSeq s =
      s |> Mseq.to_list |> List.map ppp |> Ustring.concat (us",")
    in
    let ppName = function NameStr(x) -> x | NameWildcard -> us"_" in
    match pat with
    | PatNamed(_,NameStr(x)) -> x
    | PatSeq(_,lst,SeqMatchPrefix(x)) ->
      us"[" ^. ppSeq lst ^. us"] ++ " ^. ppName x
    | PatSeq(_,lst,SeqMatchPostfix(x)) ->
      ppName x ^. us" ++ [" ^. ppSeq lst ^. us"]"
    | PatSeq(_,lst,SeqMatchTotal) -> us"[" ^. ppSeq lst ^. us"]"
    | PatNamed(_,NameWildcard) -> us"_"
    | PatTuple(_,ps) ->
      us"(" ^. Ustring.concat (us",") (List.map ppp ps) ^. us")"
    | PatCon(_,x,n,p) ->
      let con = ustring_of_var x n in
      let inner = ppp p in
      con ^. us"(" ^. inner ^. us")"
    | PatInt(_,i) -> Ustring.Op.ustring_of_int i
    | PatChar(_,c) -> us (lit_of_uchar c)
    | PatBool(_,b) -> ustring_of_bool b
    | PatUnit _ -> us"()"
  in ppp p

(** Convert type to ustring.
 *  TODO Precedence
 *  TODO Use Format module printing *)
let rec ustring_of_ty = function
  | TyUnit  -> us"()"
  | TyDyn   -> us"Dyn"
  | TyBool  -> us"Bool"
  | TyInt   -> us"Int"
  | TyFloat -> us"Float"
  | TyChar  -> us"Char"
  | TyArrow(ty1,ty2) ->
    us"(" ^. ustring_of_ty ty1 ^. us"->" ^. ustring_of_ty ty2 ^.  us")"
  | TySeq(ty1) -> if ty1 = TyChar then us"String"
    else us"[" ^. ustring_of_ty ty1 ^. us"]"
  | TyTuple tys ->
    us"(" ^. Ustring.concat (us",") (List.map ustring_of_ty tys) ^. us")"
  | TyRecord tys ->
    let pprint_ty_label = function
      | (l, ty) -> l ^. us" : " ^. ustring_of_ty ty in
    us"{" ^. Ustring.concat (us",") (List.map pprint_ty_label tys) ^. us"}"
  | TyCon(s) -> s

(** Simple enum used in the concat function in string_of_tm *)
type sep =
  | Space
  | Comma

(** Function for concatenating a list of fprintf calls using a given separator.
 *  TODO Possible to simply use Format.pp_print_list? *)
let rec concat fmt (sep, ls) = match ls with
  | []  -> ()
  | [f] -> f fmt
  | f :: ls -> match sep with
    | Space -> fprintf fmt "%t@ %a"  f concat (sep, ls)
    | Comma -> fprintf fmt "%t,@,%a" f concat (sep, ls)

(** Precedence constants for printing *)
type prec =
  | Match
  | Lam
  | Semicolon
  | If
  | Tup
  | App
  | Atom

(** Print a constant on the given formatter
 *  TODO Precendece?
 *  TODO Break hints? *)
let rec print_const fmt = function

  (* MCore intrinsic: unit - no operation *)
  | Cunit -> fprintf fmt "()"

  (* MCore Intrinsic Booleans *)
  | CBool(b)      -> fprintf fmt "%B" b
  | Cnot          -> fprintf fmt "not"
  | Cand(None)    -> fprintf fmt "and"
  | Cand(Some(v)) -> fprintf fmt "and(%B)" v
  | Cor(None)     -> fprintf fmt "or"
  | Cor(Some(v))  -> fprintf fmt "or(%B)" v

  (* MCore Intrinsic Integers *)
  | CInt(v)        -> fprintf fmt "%d" v
  | Caddi(None)    -> fprintf fmt "addi"
  | Caddi(Some(v)) -> fprintf fmt "addi(%d)" v
  | Csubi(None)    -> fprintf fmt "subi"
  | Csubi(Some(v)) -> fprintf fmt "subi(%d)" v
  | Cmuli(None)    -> fprintf fmt "muli"
  | Cmuli(Some(v)) -> fprintf fmt "muli(%d)" v
  | Cdivi(None)    -> fprintf fmt "divi"
  | Cdivi(Some(v)) -> fprintf fmt "divi(%d)" v
  | Cmodi(None)    -> fprintf fmt "modi"
  | Cmodi(Some(v)) -> fprintf fmt "modi(%d)" v
  | Cnegi          -> fprintf fmt "negi"
  | Clti(None)     -> fprintf fmt "lti"
  | Clti(Some(v))  -> fprintf fmt "lti(%d)" v
  | Cleqi(None)    -> fprintf fmt "leqi"
  | Cleqi(Some(v)) -> fprintf fmt "leqi(%d)" v
  | Cgti(None)     -> fprintf fmt "gti"
  | Cgti(Some(v))  -> fprintf fmt "gti(%d)" v
  | Cgeqi(None)    -> fprintf fmt "geqi"
  | Cgeqi(Some(v)) -> fprintf fmt "geqi(%d)" v
  | Ceqi(None)     -> fprintf fmt "eqi"
  | Ceqi(Some(v))  -> fprintf fmt "eqi(%d)" v
  | Cneqi(None)    -> fprintf fmt "neqi"
  | Cneqi(Some(v)) -> fprintf fmt "neqi(%d)" v
  | Cslli(None)    -> fprintf fmt "slli"
  | Cslli(Some(v)) -> fprintf fmt "slli(%d)" v
  | Csrli(None)    -> fprintf fmt "srli"
  | Csrli(Some(v)) -> fprintf fmt "srli(%d)" v
  | Csrai(None)    -> fprintf fmt "srai"
  | Csrai(Some(v)) -> fprintf fmt "srai(%d)" v
  | Carity         -> fprintf fmt "arity"

  (* MCore intrinsic: Floating-point number constant and operations *)
  | CFloat(v)      -> fprintf fmt "%f" v
  | Caddf(None)    -> fprintf fmt "addf"
  | Caddf(Some(v)) -> fprintf fmt "addf(%f)" v
  | Csubf(None)    -> fprintf fmt "subf"
  | Csubf(Some(v)) -> fprintf fmt "subf(%f)" v
  | Cmulf(None)    -> fprintf fmt "mulf"
  | Cmulf(Some(v)) -> fprintf fmt "mulf(%f)" v
  | Cdivf(None)    -> fprintf fmt "divf"
  | Cdivf(Some(v)) -> fprintf fmt "divf(%f)" v
  | Cnegf          -> fprintf fmt "negf"
  | Cltf(None)     -> fprintf fmt "ltf"
  | Cltf(Some(v))  -> fprintf fmt "ltf(%f)" v
  | Cleqf(None)    -> fprintf fmt "leqf"
  | Cleqf(Some(v)) -> fprintf fmt "leqf(%f)" v
  | Cgtf(None)     -> fprintf fmt "gtf"
  | Cgtf(Some(v))  -> fprintf fmt "gtf(%f)" v
  | Cgeqf(None)    -> fprintf fmt "geqf"
  | Cgeqf(Some(v)) -> fprintf fmt "geqf(%f)" v
  | Ceqf(None)     -> fprintf fmt "eqf"
  | Ceqf(Some(v))  -> fprintf fmt "eqf(%f)" v
  | Cneqf(None)    -> fprintf fmt "neqf"
  | Cneqf(Some(v)) -> fprintf fmt "neqf(%f)" v
  | Cfloorfi       -> fprintf fmt "floorfi"
  | Cceilfi        -> fprintf fmt "ceilfi"
  | Croundfi       -> fprintf fmt "roundfi"
  | CInt2float     -> fprintf fmt "int2float"
  | CString2float  -> fprintf fmt "string2float"

  (* MCore intrinsic: characters *)
  | CChar(v)  -> fprintf fmt "%s" (lit_of_uchar v)
  | CChar2int -> fprintf fmt "char2int"
  | CInt2char -> fprintf fmt "int2char"

  (* MCore intrinsic: sequences *)
  | CmakeSeq(_) -> fprintf fmt "makeseq"
  | Clength     -> fprintf fmt "length"
  | Cconcat(_)  -> fprintf fmt "concat"
  | Cget(_)     -> fprintf fmt "get"
  | Cset(_)     -> fprintf fmt "set"
  | Ccons(_)    -> fprintf fmt "cons"
  | Csnoc(_)    -> fprintf fmt "snoc"
  | CsplitAt(_) -> fprintf fmt "splitAt"
  | Creverse    -> fprintf fmt "reverse"

  (* MCore records *)
  | CRecord(r) ->
    let contents = Record.fold (fun l v ack -> (l, v)::ack) r [] in
    print_record fmt contents

  (* MCore debug and stdio intrinsics *)
  | Cprint        -> fprintf fmt "print"
  | Cdprint       -> fprintf fmt "dprint"
  | CreadFile     -> fprintf fmt "readFile"
  | CwriteFile(_) -> fprintf fmt "writeFile"
  | CfileExists   -> fprintf fmt "fileExists"
  | CdeleteFile   -> fprintf fmt "deleteFile"
  | Cerror        -> fprintf fmt "error"
  | CdebugShow    -> fprintf fmt "debugShow"

  (* MCore Symbols *)
  | CSymb(id) -> fprintf fmt "symb(%d)" id
  | Cgensym   -> fprintf fmt "gensym"
  | Ceqs(_)   -> fprintf fmt "eqs"

  (* External pprint TODO: Should not be part of core language *)
  | CExt(v) -> fprintf fmt "%s" (string_of_ustring (Extpprint.pprint v))

(** Pretty print a record *)
and print_record fmt r =
  let print (l,t) =
    let l = string_of_ustring l in
    (fun fmt -> fprintf fmt "%s = %a" l print_tm (App, t)) in
  let inner = List.map print r in
  fprintf fmt "{@[<hov 0>%a@]}" concat (Comma,inner)

(** Print a term on the given formatter and within the given precedence. *)
and print_tm fmt (prec, t) =

  let paren = prec > match t with
    | TmMatch(_,_,PatBool(_,true),_,_) -> If
    | TmMatch _ | TmLet _              -> Match
    | TmLam _                          -> Lam
    | TmSeq _                          -> Semicolon
    | TmTuple _                        -> Tup
    | TmApp _                          -> App
    | TmVar _    | TmRecLets _
    | TmConst _  | TmRecord _
    | TmProj _   | TmRecordUpdate _
    | TmCondef _ | TmConsym _
    | TmUse _    | TmUtest _
    | TmClos _   | TmFix _             -> Atom
  in

  if paren then
    fprintf fmt "(%a)" print_tm' t
  else
    fprintf fmt "%a" print_tm' t

(** Auxiliary print function *)
and print_tm' fmt t = match t with

  | TmVar(_,x,n) ->
    let print = string_of_ustring (ustring_of_var x n) in
    fprintf fmt "%s" print

  | TmLam(_,x,ty,t1) ->
    let x = string_of_ustring x in
    let ty = ty |> ustring_of_ty |> string_of_ustring in
    fprintf fmt "@[<hov %d>lam %s:%s.@ %a@]"
      !ref_indent x
      ty
      print_tm (Lam, t1)

  | TmLet(_,x,t1,t2) ->
    let x = string_of_ustring x in
    fprintf fmt "@[<hov 0>\
                   @[<hov %d>let %s =@ %a in@]\
                   @ %a\
                 @]"
      !ref_indent x
      print_tm (Match, t1)
      print_tm (Match, t2)

  | TmRecLets(_,lst,t2) ->
    let print (_,x,t) =
      let x = string_of_ustring x in
      (fun fmt -> fprintf fmt "@[<hov %d>let %s =@ %a@]"
          !ref_indent x print_tm (Match,t)) in
    let inner = List.map print lst in
    fprintf fmt "@[<hov 0>\
                   @[<hov %d>recursive@ @[<hov 0>%a@] in@]\
                   @ %a\
                 @]"
      !ref_indent concat (Space,inner)
      print_tm (Match, t2)

  | TmApp(_,t1,(TmApp _ as t2)) ->
    fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (App, t1) print_tm (Atom, t2)

  | TmApp(_,t1,t2) ->
    fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (App, t1) print_tm (App, t2)

  | TmConst(_,c) -> print_const fmt c

  | TmSeq(_,tms) ->
    let print t = (fun fmt -> fprintf fmt "%a" print_tm (App,t)) in
    let inner = List.map print (Mseq.to_list tms) in
    fprintf fmt "[@[<hov 0>%a@]]" concat (Comma,inner)

  | TmTuple(_,tms) ->
    let print t = (fun fmt -> fprintf fmt "%a" print_tm (App,t)) in
    let inner = List.map print tms in
    fprintf fmt "(@[<hov 0>%a@])" concat (Comma,inner)

  | TmRecord(_,r) -> print_record fmt r

  | TmProj(_,t,l) ->
    let l = match l with
      | LabIdx i -> string_of_int i
      | LabStr s -> string_of_ustring s in
    fprintf fmt "%a.%s" print_tm (Atom, t) l

  | TmRecordUpdate(_,t1,l,t2) ->
    let l = string_of_ustring l in
    (* TODO The below Atom precedences can probably be made less conservative *)
    fprintf fmt "{%a with %s = %a}"
      print_tm (Atom, t1)
      l
      print_tm (Atom, t2)

  | TmCondef(_,s,ty,t) ->
    let s = string_of_ustring s in
    let ty = ty |> ustring_of_ty |> string_of_ustring in
    fprintf fmt "@[<hov 0>con %s:%s in@ %a@]"
      s ty print_tm (Match, t)

  | TmConsym(_,s,sym,tmop) ->
    let s = string_of_ustring s in
    (match tmop with
     (* TODO Atom precedence too conservative? *)
     | Some(t) -> fprintf fmt "%s_%d %a" s sym print_tm (Atom ,t)
     | None -> fprintf fmt "%s_%d" s sym)

  (* If expressions *)
  | TmMatch(_,t1,PatBool(_,true),t2,t3) ->
    fprintf fmt "@[<hov %d>\
                   if %a@ \
                   @[<hov 0>\
                     then %a@ \
                     else %a\
                   @]\
                 @]"
      !ref_indent
      print_tm (Match, t1)
      print_tm (Match, t2)
      print_tm (If, t3)

  | TmMatch(_,t,p,then_,else_) ->
    let p = p |> ustring_of_pat |> string_of_ustring in
    fprintf fmt "@[<hov %d>\
                   match %a@ \
                   @[<hov 0>\
                     with %s@ \
                     then %a@ \
                     else %a\
                   @]\
                 @]"
      !ref_indent
      print_tm (Match, t)
      p
      print_tm (If, then_)
      print_tm (If, else_)

  | TmUse(_,l,t) ->
    let l = string_of_ustring l in
    fprintf fmt "@[<hov 0>use %s in@ %a@]"
      l print_tm (Match, t)

  | TmUtest(_,t1,t2,t3) ->
    fprintf fmt "@[<hov 0>\
                   @[<hov %d>\
                     utest@ \
                     @[<hov 0>\
                       %a with@ \
                       %a in\
                     @]\
                   @]\
                   @ %a\
                 @]"
      !ref_indent
      print_tm (Match, t1)
      print_tm (Match, t2)
      print_tm (Match, t3)

  | TmClos(_,x,ty,t1,_) ->
    let x = string_of_ustring x in
    let ty = ty |> ustring_of_ty |> string_of_ustring in
    fprintf fmt "@[<hov %d>clos %s:%s.@ %a@]"
      !ref_indent x
      ty
      print_tm (Lam, t1)

  | TmFix _ -> fprintf fmt "fix"

(** Print an environment on the given formatter. *)
and print_env fmt env =
  let print i t = (fun fmt -> fprintf fmt "%d -> %a" i print_tm (Match, t)) in
  let inner = List.mapi print env in
  fprintf fmt "[@[<hov 0>%a@]]" concat (Comma,inner)

(** Helper function for configuring the string formatter and printing *)
let ustr_formatter_print
    ?(debruijn   = !enable_debug_debruijn_print)
    ?(indent     = 2)
    ?(max_indent = 68)
    ?(margin     = max_int)
    ?(max_boxes  = max_int)
    ?(prefix     = "")
    printer arg =

  (* Configure global settings *)
  ref_debruijn := debruijn;
  ref_indent   := indent;
  pp_set_margin     str_formatter margin;
  pp_set_max_indent str_formatter max_indent;
  pp_set_max_boxes  str_formatter max_boxes;

  (* Make sure formatter is cleared *)
  ignore (flush_str_formatter ());

  (* Print a prefix *)
  fprintf str_formatter "%s" prefix;

  (* Do the actual printing *)
  printer str_formatter arg;

  (* Return result string and clear formatter *)
  flush_str_formatter () |> us

(** Convert terms to strings.
 *  TODO Messy with optional arguments passing. Alternatives? *)
let ustring_of_tm ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix t =
  ustr_formatter_print ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_tm (Match, t)

(** Converting constants to strings.
 *  TODO Messy with optional arguments passing. Alternatives? *)
let ustring_of_const ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix c =
  ustr_formatter_print ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_const c

(** Converting environments to strings.
 *  TODO Messy with optional arguments passing. Alternatives? *)
let ustring_of_env ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix e =
  ustr_formatter_print ?debruijn ?indent ?max_indent ?margin ?max_boxes ?prefix
    print_env e

(** TODO: Print mlang part as well. *)
let ustring_of_program tml =
  match tml with
  | Program(_,_,t) -> ustring_of_tm t

