

(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Msg
open Ustring.Op

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

  - If two constructor names are the same, they belong to the same
   datatype

  - Two interpreters being merged have the same return type
*)

let check_matching_constrs info constrs =
  let check_matching_constr = function
    | CDecl(_, c, ty) ->
       let matching_constr = function
       | CDecl(_, c', _) -> c = c'
       in
       match List.find_opt matching_constr constrs with
       | Some (CDecl(_, _, ty')) ->
          if not (ty = ty')
          then raise_error info
                 ("Conflicting parameter types for constructor '"^
                  Ustring.to_utf8 c^"'")
       | None -> ()
  in
  List.iter check_matching_constr

let rec merge_data d constrs = function
  | [] -> [Data(NoInfo, d, constrs)]
  | Data(info', d', constrs')::decls when d = d' ->
       check_matching_constrs info' constrs constrs';
       let unique_constrs = List.sort_uniq constr_compare (constrs@constrs') in
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

let translate_data l d =
  let translate_constr constr inner =
    match constr with
    | CDecl(_, k, ty) -> (* TmData (NoInfo, k, ty, inner) *)
       let _ = inner in
       let _ = l in
       let _ = d in
       let _ = k in
       let _ = ty in
       failwith "Not implemented"
  in
  List.fold_right translate_constr

let translate_params =
  let translate_param p base =
    match p with
    | Param(_, x, ty) -> TmLam (NoInfo, x, ty, base)
  in
  List.fold_right translate_param

let translate_cases f target cases =
  let translate_case case inner =
    match case with
    | (Pattern (_, k, x), handler) ->
       let _ = target in
       let _ = k in
       let _ = x in
       let _ = handler in
       let _ = inner in
     (* TmMatch (NoInfo, target,
                 k, x, handler, inner) *)
       failwith "Not implemented"
  in
  let msg = List.map (fun c -> TmConst(NoInfo,CChar(c)))
            (ustring2list (us"No matching case for function " ^. f))
  in
  let no_match =
    TmApp (NoInfo, TmConst (NoInfo, Cerror), TmConst(NoInfo, CSeq msg))
  in
  List.fold_right translate_case cases no_match

let translate_inter l f params cases : tm -> tm =
  let _ = l in
  let target = us"_" in
  let mtch = TmLam (NoInfo, target, TyDyn, translate_cases f target cases) in
  let wrapped_match = translate_params params mtch in
  let recursive_fn = TmApp (NoInfo, TmFix NoInfo,
                            TmLam (NoInfo, f, TyDyn, wrapped_match)) in
  fun cont -> TmLet (NoInfo, f, recursive_fn, cont)

let translate_decl l : decl -> tm -> tm = function
  | Data (_, d, constrs) -> fun inner -> translate_data l d constrs inner
  | Inter (_, f, params, cases) -> translate_inter l f params cases

let translate_lang : mlang -> (tm -> tm) list = function
  | Lang (_, l, _, decls) -> List.map (translate_decl l) decls

let translate = function
  | Program(_, langs, e) -> let _ = langs (* List.map translate_lang langs *) in e
