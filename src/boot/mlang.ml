

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

let param_eq p1 p2 =
  match p1, p2 with
  | Param(_,_,ty1), Param(_,_,ty2) -> ty1 = ty2

(*********************
 * Compare patterns  *
 *********************)

let pattern_compare p1 p2 = match p1, p2 with
  | VarPattern _,         VarPattern _ -> 0
  | VarPattern _,         ConPattern _ -> 1
  | ConPattern _,         VarPattern _ -> -1
  | ConPattern(_, k1, _), ConPattern(_, k2, _) -> Ustring.compare k1 k2

(***************
 * Flattening *
 ***************)

(** TODO: Some things that should be fixed or investigated

  - If two constructor names are the same, they are assumed to
   belong to the same datatype

  - Two interpreters being merged are assumed to have the same
   return type

  - It is uncertain if there is any interoperability between
   languages (or if there should be)

  - It is uncertain how nested language uses work (or if they
   should be allowed)

 *)

let check_matching_constrs info constrs =
  let check_matching_constr = function
    | CDecl(_, c, ty) ->
       let matching_constr = function
       | CDecl(_, c', _) -> c = c'
       in
       match List.find_opt matching_constr constrs with
       | Some (CDecl(_, _, ty')) ->
(*
          if not (ty = ty')
          then raise_error info
                 ("Conflicting parameter types for constructor '"^
                  Ustring.to_utf8 c^"'")
*)
          let _ = ty in
          let _ = ty' in
          let _ = info in
          () (* TODO: Disabled to cater for extensible records *)
       | None -> ()
  in
  List.iter check_matching_constr

let rec merge_data d constrs = function
  | [] -> []
  | Data(info', d', constrs')::decls when d = d' ->
       let matching_constr (CDecl(_, c, _)) (CDecl(_, c', _)) = c = c' in
       let is_previously_defined c = List.exists (matching_constr c) constrs in
       check_matching_constrs info' constrs constrs';
       let new_constrs = List.filter (fun c -> is_previously_defined c |> not) constrs' in
       Data(info', d, new_constrs)::decls
  | decl::decls ->
     decl::merge_data d constrs decls

let rec merge_inter f params cases = function
  | [] -> [Inter(NoInfo, f, params, cases)]
  | Inter(info', f', params', cases')::decls when f = f' ->
     if not (List.length params = List.length params') then
       raise_error info' ("Different number of parameters for interpreter '"^
                          Ustring.to_utf8 f^"'")
     else if not (List.for_all2 param_eq params params') then
       raise_error info' ("Parameters are not the same for interpreter '"^
                          Ustring.to_utf8 f^"'")
     else
       Inter(info', f', params', cases@cases')::decls
  | decl::decls ->
     decl::merge_inter f params cases decls

(* add decl to decls, since decl comes from a language that was included by the language decls originates from *)
let merge_decl decl decls = match decl with
  | Data(_, d, constrs) -> merge_data d constrs decls
  | Inter(_, f, params, cases) -> merge_inter f params cases decls

(* merge lang2 into lang1 (because lang1 includes lang2) *)
let merge_langs lang1 lang2 : mlang =
  match lang1, lang2 with
  | Lang(info, l1, ls, decls1), Lang(_, _, _, decls2) ->
     let decls1' = List.fold_right merge_decl decls2 decls1 in
     Lang(info, l1, ls, decls1')

let lookup_lang info tops l =
  let has_name l = function
    | TopLang(Lang(_, l', _, _)) -> l = l'
    | TopLet _ -> false
    | TopRecLet _ -> false
    | TopCon _ -> false
  in
  match List.find_opt (has_name l) tops with
  | Some (TopLang res) -> res
  | _ -> raise_error info ("Unknown language fragment '"^
                              Ustring.to_utf8 l^"'")

let sort_decls = function
  | Lang(info, l, ls, decls) ->
     let is_data_decl = function | Data _ -> true | _ -> false in
     match List.partition is_data_decl decls with
     | (data, inters) -> Lang(info, l, ls, data@inters)

let flatten_langs tops : top list =
  let flatten_langs' flat = function
    | TopLang(Lang(info, _, ls, _) as lang)  ->
       let included_langs = List.map (lookup_lang info flat) ls in
       let lang' = List.fold_left merge_langs lang included_langs in
       let sorted = sort_decls lang' in
       TopLang sorted::flat
    | TopLet _ as let_ -> let_::flat
    | TopRecLet _ as let_ -> let_::flat
    | TopCon _ as con -> con::flat
  in
  List.rev (List.fold_left flatten_langs' [] tops)

let flatten = function
  | Program(includes, tops, e) -> Program(includes, flatten_langs tops, e)

(***************
 * Translation *
 ***************)

module AstHelpers = struct
  let var x = TmVar(NoInfo, x, -1)
  let app l r = TmApp(NoInfo, l, r)
  let let_ x e body = TmLet(NoInfo, x, e, body)
end

open AstHelpers

let translate_cases f target cases =
  let translate_case case inner =
    match case with
    | (ConPattern (fi, k, x), handler) ->
      TmMatch (fi, target, PatCon(fi, k, noidx, PatNamed(fi, x)), handler, inner)
    | (VarPattern (fi, x), handler) ->
      TmLet(fi, x, target, handler)
  in
  let msg = List.map (fun c -> TmConst(NoInfo,CChar(c)))
            (ustring2list (us"No matching case for function " ^. f))
  in
  let no_match =
    let_ (us"_")
      (app (TmConst (NoInfo, CdebugShow)) target)
      (app (TmConst (NoInfo, Cerror)) (TmConst(NoInfo, CSeq msg)))
  in
  let case_compare c1 c2 = match c1, c2 with
    | (p1, _), (p2, _) -> pattern_compare p1 p2
  in
  let sorted_cases = List.sort case_compare cases in
  List.fold_right translate_case sorted_cases no_match

module USMap = Map.Make (Ustring)

type mlangEnv = { constructors : ustring USMap.t; normals : ustring USMap.t }
let emptyMlangEnv = {constructors = USMap.empty; normals = USMap.empty}

(* Adds the names from b to a, overwriting with the name from b when they overlap *)
let merge_env_overwrite a b =
  { constructors = USMap.union (fun _ _ r -> Some r) a.constructors b.constructors
  ; normals = USMap.union (fun _ _ r -> Some r) a.normals b.normals }

let empty_mangle str = str

let resolve_con {constructors; _} ident =
  match USMap.find_opt ident constructors with
  | Some(ident') -> ident'
  | None -> empty_mangle ident

let resolve_id {normals; _} ident =
  match USMap.find_opt ident normals with
  | Some(ident') -> ident'
  | None -> empty_mangle ident

(* TODO(vipa): this function is here since the current implementation has variables and constructors in the same namespace, it should be replaced by correct uses of resolve_id and resolve_con *)
let resolve_id_or_con {constructors; normals} ident =
  match USMap.find_opt ident normals with
  | Some ident' -> ident'
  | None ->
     (match USMap.find_opt ident constructors with
      | Some ident' -> ident'
      | None -> empty_mangle ident)

(* TODO(vipa): see resolve_id_or_con *)
let delete_id_and_con {constructors; normals} ident =
  { constructors = USMap.remove ident constructors
  ; normals = USMap.remove ident normals }

let rec desugar_tm nss env =
  let map_right f (a, b) = (a, f b)
  in function
  (* Referencing things *)
  | TmVar(fi, name, i) -> TmVar(fi, resolve_id_or_con env name, i)
  | (TmConsym _) as tm -> tm
  (* Introducing things *)
  | TmLam(fi, name, ty, body) ->
     TmLam(fi, empty_mangle name, ty, desugar_tm nss (delete_id_and_con env name) body)
  | TmLet(fi, name, e, body) ->
     TmLet(fi, empty_mangle name, desugar_tm nss env e, desugar_tm nss (delete_id_and_con env name) body)
  | TmRecLets(fi, bindings, body) ->
     let env' = List.fold_left (fun env' (_, name, _) -> delete_id_and_con env' name) env bindings
     in TmRecLets(fi, List.map (fun (fi, name, e) -> (fi, empty_mangle name, desugar_tm nss env' e)) bindings, desugar_tm nss env' body)
  | TmCondef(fi, name, ty, body) ->
     TmCondef(fi, empty_mangle name, ty, desugar_tm nss (delete_id_and_con env name) body)
  | (TmClos _) as tm -> tm
  (* Both introducing and referencing *)
  | TmMatch(fi, target, pat, thn, els) ->
     let rec desugar_pat env = function
       | PatNamed(fi, name) -> (delete_id_and_con env name, PatNamed(fi, empty_mangle name))
       | PatTuple(fi, pats) ->
          List.fold_right (fun p (env, pats) -> desugar_pat env p |> map_right (fun p -> p::pats)) pats (env, [])
          |> map_right (fun pats -> PatTuple(fi, pats))
       | PatCon(fi, name, sym, p) ->
          desugar_pat env p
          |> map_right (fun p -> PatCon(fi, resolve_con env name, sym, p))
       | (PatInt _ | PatChar _ | PatBool _ | PatUnit _) as pat -> (env, pat) in
     let (env', pat') = desugar_pat env pat in
     TmMatch(fi, desugar_tm nss env target, pat', desugar_tm nss env' thn, desugar_tm nss env els)
  (* Use *)
  | TmUse(fi, name, body) ->
     (match USMap.find_opt name nss with
      | None -> raise_error fi ("Unknown language fragment '" ^ Ustring.to_utf8 name ^ "'")
      | Some ns -> desugar_tm nss (merge_env_overwrite env ns) body)
  (* Simple recursions *)
  | TmApp(fi, a, b) -> TmApp(fi, desugar_tm nss env a, desugar_tm nss env b)
  | TmIf(fi, c, th, el) -> TmIf(fi, desugar_tm nss env c, desugar_tm nss env th, desugar_tm nss env el)
  | TmSeq(fi, tms) -> TmSeq(fi, List.map (desugar_tm nss env) tms)
  | TmTuple(fi, tms) -> TmTuple(fi, List.map (desugar_tm nss env) tms)
  | TmRecord(fi, tms) -> TmRecord(fi, List.map (desugar_tm nss env |> map_right) tms)
  | TmProj(fi, tm, lab) -> TmProj(fi, desugar_tm nss env tm, lab)
  | TmRecordUpdate(fi, a, lab, b) -> TmRecordUpdate(fi, desugar_tm nss env a, lab, desugar_tm nss env b)
  | TmUtest(fi, a, b, body) -> TmUtest(fi, desugar_tm nss env a, desugar_tm nss env b, desugar_tm nss env body)
  | TmConst(fi, CRecord record) -> TmConst(fi, CRecord (Record.map (desugar_tm nss env) record))
  (* Non-recursive *)
  | (TmConst _ | TmFix _ ) as tm -> tm

(* add namespace to nss (overwriting) if relevant, prepend a tm -> tm function to stack, return updated tuple. Should use desugar_tm, as well as desugar both sem and syn *)
let desugar_top (nss, (stack : (tm -> tm) list)) = function
  | TopLang (Lang(_, langName, includes, decls)) ->
     let add_lang ns lang = USMap.find_opt lang nss |> Option.value ~default:emptyMlangEnv |> merge_env_overwrite ns in
     let previous_ns = List.fold_left add_lang emptyMlangEnv includes in
     (* compute the namespace *)
     let mangle str = langName ^. us"_" ^. str in
     let cdecl_names (CDecl(_, name, _)) = (name, mangle name) in
     let add_decl {constructors; normals} = function
       | Data (_, _, cdecls) ->
          let new_constructors = List.to_seq cdecls |> Seq.map cdecl_names
          in {constructors = USMap.add_seq new_constructors constructors; normals}
       | Inter (_, name, _, _) -> {normals = USMap.add name (mangle name) normals; constructors} in
     let ns = List.fold_left add_decl previous_ns decls in
     (* wrap in "con"s *)
     let wrap_con ty_name (CDecl(fi, cname, ty)) tm =
       TmCondef(fi, mangle cname, TyArrow(TyCon ty_name, ty), tm) in (* TODO(vipa): the type will likely be incorrect once we start doing product extensions of constructors *)
     let wrap_data decl tm = match decl with (* TODO(vipa): this does not declare the type itself *)
       | Data(_, name, cdecls) -> List.fold_right (wrap_con name) cdecls tm
       | _ -> tm in
     (* translate "Inter"s into (info * ustring * tm) *)
     let inter_to_tm fname fi params cases =
       let target = us"__sem_target" in
       let wrap_param (Param(fi, name, ty)) tm = TmLam(fi, name, ty, tm)
       in TmLam(fi, target, TyDyn, translate_cases fname (var target) cases)
          |> List.fold_right wrap_param params
          |> desugar_tm nss ns in
     let translate_inter = function
       | Inter(fi, name, params, cases) -> Some (fi, mangle name, inter_to_tm name fi params cases)
       | _ -> None in
     (* put translated inters in a single letrec, then wrap in cons, then done *)
     let wrap tm = TmRecLets(NoInfo, List.filter_map translate_inter decls, tm)
                   |> List.fold_right wrap_data decls
     in (USMap.add langName ns nss, wrap :: stack)

  (* The other tops are trivial translations *)
  | TopLet(Let(fi, id, tm)) ->
     let wrap tm' = TmLet(fi, empty_mangle id, desugar_tm nss emptyMlangEnv tm, tm')
     in (nss, (wrap :: stack))
  | TopRecLet(RecLet(fi, lets)) ->
     let wrap tm' = TmRecLets(fi, List.map (fun (fi', id, tm) -> fi', empty_mangle id, desugar_tm nss emptyMlangEnv tm) lets, tm')
     in (nss, (wrap :: stack))
  | TopCon(Con(fi, id, ty)) ->
     let wrap tm' = TmCondef(fi, id, ty, tm')
     in (nss, (wrap :: stack))

let desugar_post_flatten (Program(_, tops, t)) =
  let acc_start = (USMap.empty, []) in
  let (nss, stack) = List.fold_left desugar_top acc_start tops in
  List.fold_left (|>) (desugar_tm nss emptyMlangEnv t) stack
