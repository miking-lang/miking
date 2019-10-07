

(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Msg

(*******************
 * Auxiliary stuff *
 *******************)
let constr_compare decl1 decl2 =
  match decl1, decl2 with
  | CDecl(_, c1, _), CDecl(_, c2, _) -> Ustring.compare c1 c2

(***************
 * Flattening *
 ***************)

(** This code currently executes with the following assumptions
   (some of which should be fixed):

  - If two constructor names are the same, they have the same
   parameter types

  - If two constructor names are the same, they belong to the same
   datatype

  - Two interpreters being merged have the same return type
*)

let rec merge_data d constrs = function
  | [] -> [Data(NoInfo, d, constrs)]
  | Data(info', d', constrs')::decls when d = d' ->
     let unique_constrs = List.sort_uniq constr_compare (constrs@constrs') in
     (* TODO: Assumes arguments are the same *)
     Data(info', d, unique_constrs)::decls
  | decl::decls ->
     decl::merge_data d constrs decls

let rec merge_inter f params cases = function
  | [] -> [Inter(NoInfo, f, params, cases)]
  | Inter(info', f', params', cases')::decls when f = f' ->
     if not (List.length params = List.length params') then
       raise_error info' ("Different number of parameters for interpreter '"^
                          Ustring.to_utf8 f^"'")
     else if not (List.for_all2 (fun p1 p2 -> p1 = p2) params params') then
       raise_error info' ("Parameters are not the same for interpreter '"^
                          Ustring.to_utf8 f^"'")
     else
       Inter(info', f', params', cases@cases')::decls
  | decl::decls ->
     decl::merge_inter f params cases decls

let merge_decl decls = function
  | Data(_, d, constrs) -> merge_data d constrs decls
  | Inter(_, f, params, cases) -> merge_inter f params cases decls

let merge_langs lang1 lang2 : mlang =
  match lang1, lang2 with
  | Lang(info, l1, ls, decls1), Lang(_, _, _, decls2) ->
     let decls1' = List.fold_left merge_decl decls1 decls2 in
     Lang(info, l1, ls, decls1')

let lookup_lang info langs l =
  let has_name l lang = match lang with Lang(_, l', _, _) -> l = l' in
  match List.find_opt (has_name l) langs with
  | Some res -> res
  | None -> raise_error info ("Unknown language fragment '"^
                              Ustring.to_utf8 l^"'")

let flatten_langs langs : mlang list =
  let flatten_langs' flat = function
    | Lang(info, _, ls, _) as lang ->
       let included_langs = List.map (lookup_lang info flat) ls in
       let lang' = List.fold_left merge_langs lang included_langs in
       lang'::flat
  in
  List.rev (List.fold_left flatten_langs' [] langs)

let flatten = function
  | Program(info, langs, e) -> Program(info, flatten_langs langs, e)

(***************
 * Translation *
 ***************)
let translate_data l d constrs : tm =
  let _ = l in
  let _ = d in
  let _ = constrs in
  failwith "Not implemented"

let translate_inter l f params cases : tm =
  let _ = l in
  let _ = f in
  let _ = params in
  let _ = cases in
  failwith "Not implemented"

let translate_decl l = function
  | Data (_, d, constrs) -> translate_data l d constrs
  | Inter (_, f, params, cases) -> translate_inter l f params cases

let translate_lang = function
  | Lang (_, l, _, decls) -> List.map (translate_decl l) decls

let translate = function
  | Program(_, langs, e) -> let _ = langs in e