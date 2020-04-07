(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
*)

open Ast
open Format

(** Precedence constants for printing *)
type prec =
  | MATCH
  | LAM
  | SEMICOLON
  | IF
  | TUP
  | APP
  | ATOM

(** Global configuration for prints. Needed because of the unwieldy interface
    to the Format module *)
let ref_debruijn    = ref false
let ref_indent      = ref 2

(** Alias for converting from ustring to string *)
let string_of_ustring = Ustring.to_utf8

(** Sets up the formatter. *)
let setup_print
    ?(debruijn   = !Pprint.enable_debug_debruijn_print)
    ?(indent     = 2)
    ?(max_indent = 68)
    ?(margin     = 80)
    ?(max_boxes  = max_int)
    () =
  ref_debruijn    := debruijn;
  ref_indent      := indent;
  pp_set_margin str_formatter margin;
  pp_set_max_indent str_formatter max_indent;
  pp_set_max_boxes str_formatter max_boxes

(** Simple enum used in the concat function in string_of_tm *)
type sep =
  | SPACE
  | COMMA

(** Function for concatenating a list of fprintf calls using a given separator.
    TODO Possible to simply use Format.pp_print_list? *)
let rec concat fmt (sep, ls) = match ls with
  | []  -> ()
  | [f] -> f fmt
  | f :: ls -> match sep with
    | SPACE -> fprintf fmt "%t@ %a"  f concat (sep, ls)
    | COMMA -> fprintf fmt "%t,@,%a" f concat (sep, ls)

(** Print a term on the given formatter and within the given precedence. *)
let rec print_tm fmt (prec, t) =

  let paren = prec > match t with
    | TmMatch(_,_,PatBool(_,true),_,_)            -> IF
    | TmMatch _ | TmLet _                         -> MATCH
    | TmLam _                                     -> LAM
    | TmSeq _                                     -> SEMICOLON
    | TmTuple _                                   -> TUP
    | TmApp _                                     -> APP
    | TmVar _    | TmRecLets _ | TmConst _
    | TmRecord _ | TmProj _    | TmRecordUpdate _
    | TmCondef _ | TmConsym _  | TmUse _
    | TmUtest _  | TmClos _    | TmFix _          -> ATOM
  in

  if paren then
    fprintf fmt "(%a)" print_tm' t
  else
    fprintf fmt "%a" print_tm' t

(* Auxiliary print function *)
and print_tm' fmt t = match t with

  | TmVar(_,x,i) ->
    let x = string_of_ustring x in
    if !ref_debruijn then fprintf fmt "%s'%d" x i else fprintf fmt "%s" x

  | TmLam(_,x,ty,t1) ->
    let x = string_of_ustring x in
    let ty = ty |> Pprint.pprint_ty |> string_of_ustring in
    fprintf fmt "@[<hov %d>lam %s:%s.@ %a@]"
      !ref_indent x
      ty
      print_tm (LAM, t1)

  | TmLet(_,x,t1,t2) ->
    let x = string_of_ustring x in
    fprintf fmt "@[<hov 0>\
                 @[<hov %d>let %s =@ %a in@]\
                 @ %a@]"
      !ref_indent x
      print_tm (MATCH, t1)
      print_tm (MATCH, t2)

  | TmRecLets(_,lst,t2) ->
    let print (_,x,t) =
      let x = string_of_ustring x in
      (fun fmt -> fprintf fmt "@[<hov %d>let %s =@ %a@]"
          !ref_indent x print_tm (MATCH,t)) in
    let inner = List.map print lst in
    fprintf fmt "@[<hov 0>\
                 @[<hov %d>recursive@ @[<hov 0>%a@] in@]\
                 @ %a@]"
      !ref_indent concat (SPACE,inner)
      print_tm (MATCH, t2)

  | TmApp(_,t1,(TmApp _ as t2)) ->
    fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (APP, t1) print_tm (ATOM, t2)

  | TmApp(_,t1,t2) ->
    fprintf fmt "@[<hv 0>%a@ %a@]" print_tm (APP, t1) print_tm (APP, t2)

  (* TODO: CRecord should probably be handled separately *)
  | TmConst(_,c) ->
      fprintf fmt "%s" (string_of_ustring (Pprint.pprint_const c))

  | TmSeq(_,tms) ->
    let print t = (fun fmt -> fprintf fmt "%a" print_tm (APP,t)) in
    let inner = List.map print tms in
    fprintf fmt "[@[<hov 0>%a@]]" concat (COMMA,inner)

  | TmTuple(_,tms) ->
    let print t = (fun fmt -> fprintf fmt "%a" print_tm (APP,t)) in
    let inner = List.map print tms in
    fprintf fmt "(@[<hov 0>%a@])" concat (COMMA,inner)

  | TmRecord(_,r) ->
    let print (l,t) =
      let l = string_of_ustring l in
      (fun fmt -> fprintf fmt "%s = %a" l print_tm (APP, t)) in
    let inner = List.map print r in
    fprintf fmt "{@[<hov 0>%a@]}" concat (COMMA,inner)

  | TmProj(_,t,l) ->
    let l = match l with
      | LabIdx i -> string_of_int i
      | LabStr s -> string_of_ustring s in
    fprintf fmt "%a.%s" print_tm (ATOM, t) l

  | TmRecordUpdate(_,t1,l,t2) ->
    let l = string_of_ustring l in
    (* TODO The below ATOM precedences can probably be made less conservative *)
    fprintf fmt "{%a with %s = %a}"
      print_tm (ATOM, t1)
      l
      print_tm (ATOM, t2)

  | TmCondef(_,s,ty,t) ->
    let s = string_of_ustring s in
    let ty = ty |> Pprint.pprint_ty |> string_of_ustring in
    fprintf fmt "@[<hov 0>con %s:%s in@ %a@]"
      s ty print_tm (MATCH, t)

  | TmConsym(_,_s,_sym,_tmop) ->
    failwith "TODO: Printing of TmConsym not yet supported"

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
      print_tm (MATCH, t1)
      print_tm (MATCH, t2)
      print_tm (IF, t3)

  | TmMatch(_,t,p,then_,else_) ->
    let p = p |> Pprint.pprintPat |> string_of_ustring in
    fprintf fmt "@[<hov %d>\
                   match %a@ \
                   @[<hov 0>\
                     with %s@ \
                     then %a@ \
                     else %a\
                   @]\
                 @]"
      !ref_indent
      print_tm (MATCH, t)
      p
      print_tm (IF, then_)
      print_tm (IF, else_)

  | TmUse(_,l,t) ->
    let l = string_of_ustring l in
    fprintf fmt "@[<hov 0>use %s in@ %a@]"
      l print_tm (MATCH, t)

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
      print_tm (MATCH, t1)
      print_tm (MATCH, t2)
      print_tm (MATCH, t3)

  | TmClos(_,_x,_ty,_t,_) ->
    failwith "TODO: Printing of TmClos not yet supported"

  | TmFix _ ->
    failwith "TODO: Printing of TmFix not yet supported"

  (* Fallback *)
  (* | _ -> fprintf fmt "%s" (string_of_ustring (Pprint.pprintME t)) *)

(** Convert terms to strings.
    TODO Messy with optional arguments passing. Alternatives? *)
let string_of_tm
    ?debruijn ?indent ?max_indent ?margin ?max_boxes ?(prefix = "") t =

  setup_print ?debruijn ?indent ?max_indent ?margin ?max_boxes ();

  fprintf str_formatter "%s" prefix;
  print_tm str_formatter (MATCH, t);
  flush_str_formatter ()

