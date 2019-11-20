

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
     else if not (List.for_all2 param_eq params params') then
       raise_error info' ("Parameters are not the same for interpreter '"^
                          Ustring.to_utf8 f^"'")
     else
       Inter(info', f', params', cases@cases')::decls
  | decl::decls ->
     decl::merge_inter f params cases decls

let merge_decl decl decls = match decl with
  | Data(_, d, constrs) -> merge_data d constrs decls
  | Inter(_, f, params, cases) -> merge_inter f params cases decls

let merge_langs lang1 lang2 : mlang =
  match lang1, lang2 with
  | Lang(info, l1, ls, decls1), Lang(_, _, _, decls2) ->
     let decls1' = List.fold_right merge_decl decls1 decls2 in
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

let flatten_langs tops : top list =
  let flatten_langs' flat = function
    | TopLang(Lang(info, _, ls, _) as lang)  ->
       let included_langs = List.map (lookup_lang info flat) ls in
       let lang' = List.fold_left merge_langs lang included_langs in
       TopLang lang'::flat
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
  let lam x body = TmLam(NoInfo, us x, TyDyn, body)
  let lam2 x y body =
    TmLam(NoInfo, us x, TyDyn, lam y body)
  let lam3 x y z body =
    TmLam(NoInfo, us x, TyDyn, lam2 y z body)
  let var x = TmVar(NoInfo, us x, -1)
  let app l r = TmApp(NoInfo, l, r)
  let app2 l r1 r2 = TmApp(NoInfo, app l r1, r2)
  let app3 l r1 r2 r3 = TmApp(NoInfo, app2 l r1 r2, r3)
  let fix = TmFix(NoInfo)
  let let_ x e body = TmLet(NoInfo, us x, e, body)
  let if_ c t e = TmIf(NoInfo, c, t, e)
  let int n = TmConst(NoInfo, CInt n)
end

open AstHelpers

let translate_data =
  let translate_constr constr inner =
    match constr with
    | CDecl(_, k, ty) -> TmCondef (NoInfo, k, ty, inner)
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
    | (ConPattern (fi, k, x), handler) ->
      TmMatch (fi, target,
               k, -1, x, handler, inner)
    | (VarPattern (fi, x), handler) ->
      TmLet(fi, x, target, handler)
  in
  let msg = List.map (fun c -> TmConst(NoInfo,CChar(c)))
            (ustring2list (us"No matching case for function " ^.
                             Ustring.from_utf8 f))
  in
  let no_match = app (TmConst (NoInfo, Cerror)) (TmConst(NoInfo, CSeq msg))
  in
  let case_compare c1 c2 = match c1, c2 with
    | (p1, _), (p2, _) -> pattern_compare p1 p2
  in
  let sorted_cases = List.sort case_compare cases in
  List.fold_right translate_case sorted_cases no_match

let unpack_recursive_functions names seq body =
  let rec unpack i = function
    | [] -> body
    | f::fs -> let_ f (app2 (var "nth") (var seq) (int i)) (unpack (i + 1) fs)
  in
  unpack 0 names

let translate_inter f fs params cases : tm -> tm =
  let target_name = "_" ^ f ^ "_target" in
  let target = var target_name in
  let mtch =
    lam target_name (translate_cases f target cases) in
  let wrapped_match = translate_params params mtch in
  let funs_seq = f ^ "_funs" in
  let unpacked = unpack_recursive_functions fs funs_seq wrapped_match in
  let fn = lam funs_seq unpacked in
  fun inner -> let_ (f ^ "_abs") fn inner

let translate_decl fs : decl -> tm -> tm = function
  | Data (_, _, constrs) -> fun inner -> translate_data constrs inner
  | Inter (_, f, params, cases) ->
     translate_inter (Ustring.to_utf8 f) fs params cases

let translate_lang : mlang -> (tm -> tm) list = function
  | Lang (_, _, _, decls) ->
     let extract_name decl ack = match decl with
       | Inter(_, f, _, _) -> Ustring.to_utf8 f::ack
       | _ -> ack
     in
     let fun_names = List.fold_right extract_name decls [] in
     let fun_abstractions = List.map (translate_decl fun_names) decls in
     let abs_seq =
       TmSeq(NoInfo, List.map (fun f -> var (f ^ "_abs")) fun_names)
     in
     let fix =
       fun inner -> let_ "@funs" (app (var "fix_mutual") abs_seq) inner
     in
     let unpacks =
       fun inner -> unpack_recursive_functions fun_names "@funs" inner in
     fun_abstractions @ [fix; unpacks]


let translate_uses tops t =
  let translate_use = function
    | TmUse(fi, l, inner) ->
       let lang = lookup_lang fi tops l in
       let decl_wrappers = translate_lang lang in
       List.fold_right (@@) decl_wrappers inner
    | t -> t
  in
  Ast.map_tm translate_use t

let desugar_uses_in_interpreters tops =
  let desugar_uses_in_case tops = function
    | (p, t) -> (p, translate_uses tops t)
  in
  let desugar_uses_in_decl tops = function
    | Inter (fi, f, params, cases) ->
       let cases' = List.map (desugar_uses_in_case tops) cases in
       Inter(fi, f, params, cases')
    | Data _ as d -> d
  in
  let desugar_uses_in_lang desugared = function
    | TopLang(Lang(fi, l, ls, decls)) ->
       let decls' = List.map (desugar_uses_in_decl desugared) decls in
       let lang' = TopLang(Lang(fi, l, ls, decls')) in
       lang'::desugared
    | l -> l::desugared
  in
  List.rev (List.fold_left desugar_uses_in_lang [] tops)

let insert_top_level_decls tops t =
  let insert_let top inner = match top with
    | TopLet(Let(fi, x, tm)) ->
       TmLet(fi, x, tm, inner)
    | TopRecLet(RecLet(fi, lst)) ->
       TmRecLets(fi, lst, inner)
    | TopCon(Con(fi, k, ty)) ->
       TmCondef(fi, k, ty, inner)
    | TopLang _ -> inner
  in
  List.fold_right insert_let tops t

let desugar_language_uses = function
  | Program(_, tops, t) ->
     let tops' = desugar_uses_in_interpreters tops in
     let t' = insert_top_level_decls tops' t in
     let t'' = translate_uses tops' t' in
     t''
