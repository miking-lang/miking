

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

(***************
 * Flattening *
 ***************)

(** TODO: Some things that should be fixed or investigated

  - If two constructor names are the same, they are assumed to
   belong to the same datatype

  - Two interpreters being merged are assumed to have the same
   return type

  - Interpreters cannot be mutually recursive

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

module Generated = struct
  let lam x body = TmLam(NoInfo, x, TyDyn, body)
  let lam2 x y body =
    TmLam(NoInfo, x, TyDyn, lam y body)
  let lam3 x y z body =
    TmLam(NoInfo, x, TyDyn, lam2 y z body)
  let var x = TmVar(NoInfo, x, -1)
  let app l r = TmApp(NoInfo, l, r)
  let app2 l r1 r2 = TmApp(NoInfo, app l r1, r2)
  let app3 l r1 r2 r3 = TmApp(NoInfo, app2 l r1 r2, r3)
  let fix = TmFix(NoInfo)
  let let_ x e body = TmLet(NoInfo, x, e, body)
  let if_ c t e = TmIf(NoInfo, c, t, e)
  let int n = TmConst(NoInfo, CInt n)
  let nil = TmSeq(NoInfo, [])

  let head = lam (us"seq") (app2 (var (us"nth")) (var (us"seq")) (int 0))
  let head_name = us"@head"
  let head_var = TmVar(NoInfo, head_name, -1)
  let head_def body = TmLet(NoInfo, head_name, head, body)

  let tail = lam (us"seq") (app3 (var (us"slice")) (var (us"seq")) (int 1)
                                 (app (var (us"length")) (var (us"seq"))))
  let tail_name = us"@tail"
  let tail_var = TmVar(NoInfo, tail_name, -1)
  let tail_def body = TmLet(NoInfo, tail_name, tail, body)

  let map =
    app fix
        (lam3 (us"map") (us"f") (us"seq")
              (if_ (app2 (var (us"eqi"))
                         (app (var (us"length")) (var (us"seq")))
                         (int 0))
                   nil
                   (app2 (var (us"cons"))
                         (app (var (us"f")) (app head_var (var (us"seq"))))
                         (app2 (var (us"map"))
                               (var (us"f"))
                               (app tail_var (var (us"seq")))))))
  let map_name = us"@map"
  let map_var = var map_name
  let map_def body = let_ map_name map body

  let fix_mutual =
    lam (us"l")
        (app2 fix
              (lam2 (us"self") (us"l")
                    (app2 map_var
                          (lam2 (us"li") (us"x")
                                (app2 (var (us"li"))
                                      (app (var (us"self")) (var (us"l")))
                                      (var (us"x"))))
                          (var (us"l"))))
              (var (us"l")))
  let fix_mutual_name = us"@fix_mutual"
  let fix_mutual_var = var fix_mutual_name
  let fix_mutual_def body = let_ fix_mutual_name fix_mutual body

  let defs = [head_def; tail_def; map_def; fix_mutual_def]
  let gen_defs body = List.fold_right (@@) defs body
end

open Generated

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
    | (Pattern (fi, k, x), handler) ->
      TmMatch (fi, target,
               k, -1, x, handler, inner)
  in
  let msg = List.map (fun c -> TmConst(NoInfo,CChar(c)))
            (ustring2list (us"No matching case for function " ^. f))
  in
  let no_match = app (TmConst (NoInfo, Cerror)) (TmConst(NoInfo, CSeq msg))
  in
  List.fold_right translate_case cases no_match

let unpack_recursive_functions names seq body =
  let rec unpack i = function
    | [] -> body
    | f::fs -> let_ f (app2 (var (us"nth")) (var seq) (int i)) (unpack (i + 1) fs)
  in
  unpack 0 names

let translate_inter f fs params cases : tm -> tm =
  let target_name = us"_" ^. f ^. us"_target" in
  let target = var target_name in
  let mtch =
    lam target_name (translate_cases f target cases) in
  let wrapped_match = translate_params params mtch in
  let funs_seq = f ^. us"_funs" in
  let unpacked = unpack_recursive_functions fs funs_seq wrapped_match in
  let fn = lam funs_seq unpacked in
  fun inner -> let_ (f ^. us"_abs") fn inner

let translate_decl fs : decl -> tm -> tm = function
  | Data (_, _, constrs) -> fun inner -> translate_data constrs inner
  | Inter (_, f, params, cases) -> translate_inter f fs params cases

let translate_lang : mlang -> (tm -> tm) list = function
  | Lang (_, _, _, decls) ->
     let extract_name decl ack = match decl with
       | Inter(_, f, _, _) -> f::ack
       | _ -> ack
     in
     let fun_names = List.fold_right extract_name decls [] in
     let fun_abstractions = List.map (translate_decl fun_names) decls in
     let abs_seq =
       TmSeq(NoInfo, List.map (fun f -> var (f ^. us"_abs")) fun_names)
     in
     let fix =
       fun inner -> let_ (us"@funs") (app fix_mutual_var abs_seq) inner
     in
     let unpacks =
       fun inner -> unpack_recursive_functions fun_names (us"@funs") inner in
     fun_abstractions @ [fix; unpacks]


let translate_uses langs t =
  let translate_use langs = function
    | TmUse(fi, l, inner) ->
       let lang = lookup_lang fi langs l in
       let decl_wrappers = translate_lang lang in
       List.fold_right (@@) decl_wrappers inner
    | t -> t
  in
  Ast.map_tm (translate_use langs) t

let desugar_uses_in_interpreters langs =
  let desugar_uses_in_case langs = function
    | (p, t) -> (p, translate_uses langs t)
  in
  let desugar_uses_in_decl langs = function
    | Inter (fi, f, params, cases) ->
       let cases' = List.map (desugar_uses_in_case langs) cases in
       Inter(fi, f, params, cases')
    | Data _ as d -> d
  in
  let desugar_uses_in_lang desugared = function
    | Lang(fi, l, ls, decls) ->
       let decls' = List.map (desugar_uses_in_decl desugared) decls in
       let lang' = Lang(fi, l, ls, decls') in
       lang'::desugared
  in
  List.rev (List.fold_left desugar_uses_in_lang [] langs)

let desugar_language_uses = function
  | Program(_, langs, t) ->
     let langs' = desugar_uses_in_interpreters langs in
     let t' = translate_uses langs' t in
     gen_defs t'