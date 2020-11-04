(*
   Miking is licensed under the MIT license.
   Copyright (C) David Broman. See file LICENSE.txt
 *)

open Ast
open Msg
open Ustring.Op
open Pprint
open Intrinsics
open Patterns

let accum_map (f : 'acc -> 'a -> 'acc * 'b) (acc : 'acc) (l : 'a list) :
    'acc * 'b list =
  let rec recur acc = function
    | [] ->
        (acc, [])
    | x :: xs ->
        let acc, x' = f acc x in
        let acc, xs' = recur acc xs in
        (acc, x' :: xs')
  in
  recur acc l

let rec pair_with_later : 'a list -> ('a * 'a) list = function
  | [] ->
      []
  | x :: xs ->
      List.rev_append (List.map (fun y -> (x, y)) xs) (pair_with_later xs)

let fold_map ~(fold : 'b -> 'b -> 'b) ~(map : 'a -> 'b) : 'b -> 'a list -> 'b =
  let rec recur acc = function
    | [] ->
        acc
    | x :: xs ->
        recur (fold acc (map x)) xs
  in
  recur

let add_new_by (eq : 'a -> 'a -> bool) (source : 'a list) (target : 'a list) =
  List.fold_left
    (fun prev a -> if List.exists (eq a) prev then prev else a :: prev)
    target source

let lookup_lang info prev_langs name =
  match Record.find_opt name prev_langs with
  | None ->
      raise_error info
        ("Unknown language fragment '" ^ Ustring.to_utf8 name ^ "'")
  | Some l ->
      l

type case =
  { pat: pat
  ; rhs: tm
  ; (* We precompute the normpat corresponding to pat, as well as the one
     * corresponding to not(pat) *)
    pos_pat: normpat
  ; neg_pat: normpat }

type inter_data =
  { info: info
  ; params: param list
  ; (* We represent each case by the location of its pattern *)
    cases: (info * case) list
  ; (* We store the DAG of subset relations as a list of pairs (a, b),
     * where a \subset b. Note proper subset, since equality
     * means we should error because we can't order the patterns. *)
    subsets: (info * info) list }

type lang_data =
  {inters: inter_data Record.t; syns: (info * cdecl list) Record.t}

let spprint_inter_data {info; cases; _} : ustring =
  List.map
    (fun (fi, {pat; _}) ->
      us "  " ^. ustring_of_pat pat ^. us " at " ^. info2str fi)
    cases
  |> Ustring.concat (us "\n")
  |> fun msg -> us "My location is " ^. info2str info ^. us "\n" ^. msg

let spprint_lang_data {inters; _} : ustring =
  Record.bindings inters
  |> List.map (fun (name, data) -> name ^. us "\n" ^. spprint_inter_data data)
  |> Ustring.concat (us "\n")

let compute_order fi
    ( (fi1, {pat= pat1; pos_pat= p1; neg_pat= n1; _})
    , (fi2, {pat= pat2; pos_pat= p2; neg_pat= n2; _}) ) =
  let string_of_pat pat = ustring_of_pat pat |> Ustring.to_utf8 in
  let info2str fi = info2str fi |> Ustring.to_utf8 in
  match order_query (p1, n1) (p2, n2) with
  | Subset ->
      [(fi1, fi2)]
  | Superset ->
      [(fi2, fi1)]
  | Equal ->
      raise_error fi
        ( "Patterns at " ^ info2str fi1 ^ " and " ^ info2str fi2
        ^ " cannot be ordered by specificity; they match exactly the same \
           values." )
  | Disjoint ->
      []
  | Overlapping (only1, both, only2) ->
      "Two patterns in this semantic function cannot be ordered by \
       specificity (neither is more specific than the other), but the order \
       matters; they overlap." ^ "\n  " ^ info2str fi1 ^ ": "
      ^ string_of_pat pat1 ^ "\n  " ^ info2str fi2 ^ ": " ^ string_of_pat pat2
      ^ "\n Example:" ^ "\n  Only in the first: " ^ string_of_pat only1
      ^ "\n  In both: " ^ string_of_pat both ^ "\n  Only in the other: "
      ^ string_of_pat only2
      |> raise_error fi

(* Check that a single language fragment is self-consistent; it has compatible patterns,
 * no duplicate definitions, etc. Does not consider included languages at all.
 *)
let compute_lang_data (Lang (info, _, _, decls)) : lang_data =
  let add_new_syn name ((fi, _) as data) = function
    | None ->
        Some data
    | Some (old_fi, _) ->
        raise_error fi
          ( "Duplicate definition of '" ^ Ustring.to_utf8 name
          ^ "', previously defined at "
          ^ Ustring.to_utf8 (info2str old_fi) )
  in
  let add_new_sem name fi data = function
    | None ->
        Some data
    | Some {info; _} ->
        raise_error fi
          ( "Duplicate definition of '" ^ Ustring.to_utf8 name
          ^ "', previously defined at "
          ^ Ustring.to_utf8 (info2str info) )
  in
  let add_decl lang_data = function
    | Data (fi, name, cons) ->
        { lang_data with
          syns= Record.update name (add_new_syn name (fi, cons)) lang_data.syns
        }
    | Inter (fi, name, params, cases) ->
        let mk_case (pat, rhs) =
          let pos_pat = pat_to_normpat pat in
          ( pat_info pat
          , {pat; rhs; pos_pat; neg_pat= normpat_complement pos_pat} )
        in
        let cases = List.map mk_case cases in
        let subsets =
          pair_with_later cases
          |> fold_map
               ~fold:(fun a b -> List.rev_append b a)
               ~map:(compute_order info) []
        in
        let inter_data = {info= fi; params; cases; subsets} in
        { lang_data with
          inters=
            Record.update name
              (add_new_sem name fi inter_data)
              lang_data.inters }
  in
  List.fold_left add_decl {inters= Record.empty; syns= Record.empty} decls

(* Merges the second language into the first, because the first includes the second *)
let merge_lang_data fi {inters= i1; syns= s1} {inters= i2; syns= s2} :
    lang_data =
  let eq_cons (CDecl (_, c1, _)) (CDecl (_, c2, _)) = c1 =. c2 in
  let merge_syn _ a b =
    match (a, b) with
    | None, None ->
        None
    | None, Some _ ->
        Some (NoInfo, [])
    | Some a, None ->
        Some a
    | Some (fi, cons), Some (_, old_cons) ->
        Some
          ( fi
          , List.filter
              (fun c1 -> List.exists (eq_cons c1) old_cons |> not)
              cons )
  in
  let merge_inter name a b =
    match (a, b) with
    | None, None ->
        None
    | None, Some a ->
        Some {a with info= fi}
    | Some a, None ->
        Some a
    | ( Some ({info= fi1; params= p1; cases= c1; subsets= s1} as data)
      , Some {info= fi2; params= p2; cases= c2; subsets= s2} ) ->
        if eq_info fi1 fi2 then Some data
        else if List.length p1 <> List.length p2 then
          raise_error fi1
            ( "Different number of parameters for interpreter '"
            ^ Ustring.to_utf8 name ^ "' compared to previous definitian at "
            ^ Ustring.to_utf8 (info2str fi2) )
        else
          let c2 =
            List.filter
              (fun (fi, _) ->
                List.exists (fun (fi2, _) -> eq_info fi fi2) c1 |> not)
              c2
          in
          let subsets =
            add_new_by
              (fun (a1, a2) (b1, b2) -> eq_info a1 b1 && eq_info a2 b2)
              s2 s1
          in
          let subsets =
            liftA2 (fun a b -> (a, b)) c1 c2
            |> fold_map
                 ~fold:(fun a b -> List.rev_append b a)
                 ~map:(compute_order fi1) subsets
          in
          Some {data with subsets; cases= List.rev_append c2 c1}
  in
  {inters= Record.merge merge_inter i1 i2; syns= Record.merge merge_syn s1 s2}

(* TODO(vipa,?): this is likely fairly low hanging fruit when it comes to optimization *)
let topo_sort (eq : 'a -> 'a -> bool) (edges : ('a * 'a) list)
    (vertices : 'a list) =
  let rec recur rev_order edges vertices =
    match
      List.find_opt
        (fun v -> List.exists (fun (_, t) -> eq v t) edges |> not)
        vertices
    with
    | None ->
        if vertices <> [] then
          uprint_endline
            ( us "topo_sort ended with "
            ^. ustring_of_int (List.length vertices)
            ^. us " vertices remaining" ) ;
        List.rev rev_order
    | Some x ->
        recur (x :: rev_order)
          (List.filter (fun (f, t) -> (not (eq x f)) && not (eq x t)) edges)
          (List.filter (fun v -> not (eq x v)) vertices)
  in
  recur [] edges vertices

let data_to_lang info name includes {inters; syns} : mlang =
  let info_assoc fi l = List.find (fun (fi2, _) -> eq_info fi fi2) l |> snd in
  let syns =
    Record.bindings syns
    |> List.map (fun (syn_name, (fi, cons)) -> Data (fi, syn_name, cons))
  in
  let sort_inter name {info; params; cases; subsets} =
    let mk_case fi =
      let case = info_assoc fi cases in
      (case.pat, case.rhs)
    in
    let cases =
      List.map fst cases |> topo_sort eq_info subsets |> List.map mk_case
    in
    Inter (info, name, params, cases)
  in
  let inters =
    Record.bindings inters
    |> List.map (fun (name, inter_data) -> sort_inter name inter_data)
  in
  Lang (info, name, includes, List.rev_append syns inters)

let flatten_lang (prev_langs : lang_data Record.t) :
    top -> lang_data Record.t * top = function
  | (TopLet _ | TopRecLet _ | TopCon _ | TopUtest _) as top ->
      (prev_langs, top)
  | TopLang (Lang (info, name, includes, _) as lang) ->
      let self_data = compute_lang_data lang in
      let included_data = List.map (lookup_lang info prev_langs) includes in
      let merged_data =
        List.fold_left (merge_lang_data info) self_data included_data
      in
      ( Record.add name merged_data prev_langs
      , TopLang (data_to_lang info name includes merged_data) )

let flatten_with_env (prev_langs : lang_data Record.t)
    (Program (includes, tops, e) : program) =
  let new_langs, new_tops = accum_map flatten_lang prev_langs tops in
  (new_langs, Program (includes, new_tops, e))

(* Flatten top-level language definitions *)
let flatten prg : program = snd (flatten_with_env Record.empty prg)

(***************
 * Translation *
 ***************)

module AstHelpers = struct
  let var x = TmVar (NoInfo, x, Symb.Helpers.nosym)

  let app l r = TmApp (NoInfo, l, r)

  let let_ x s e body = TmLet (NoInfo, x, s, TyUnknown, e, body)
end

open AstHelpers

let translate_cases f target cases =
  let translate_case (pat, handler) inner =
    TmMatch (pat_info pat, target, pat, handler, inner)
  in
  let msg =
    Mseq.Helpers.map
      (fun c -> TmConst (NoInfo, CChar c))
      (us "No matching case for function " ^. f |> Mseq.Helpers.of_ustring)
  in
  let no_match =
    let_ (us "_") Symb.Helpers.nosym
      (* TODO(?,?): we should probably have a special sort for let with wildcards *)
      (app (TmConst (NoInfo, Cdprint)) target)
      (app (TmConst (NoInfo, Cerror)) (TmSeq (NoInfo, msg)))
  in
  List.fold_right translate_case cases no_match

module USMap = Map.Make (Ustring)

type mlangEnv = {constructors: ustring USMap.t; normals: ustring USMap.t}

let emptyMlangEnv = {constructors= USMap.empty; normals= USMap.empty}

(* Adds the names from b to a, overwriting with the name from b when they overlap *)
let merge_env_overwrite a b =
  { constructors=
      USMap.union (fun _ _ r -> Some r) a.constructors b.constructors
  ; normals= USMap.union (fun _ _ r -> Some r) a.normals b.normals }

let empty_mangle str = str

let resolve_con {constructors; _} ident =
  match USMap.find_opt ident constructors with
  | Some ident' ->
      ident'
  | None ->
      empty_mangle ident

let resolve_id {normals; _} ident =
  match USMap.find_opt ident normals with
  | Some ident' ->
      ident'
  | None ->
      empty_mangle ident

let delete_id ({normals; _} as env) ident =
  {env with normals= USMap.remove ident normals}

let delete_con ({constructors; _} as env) ident =
  {env with constructors= USMap.remove ident constructors}

let rec desugar_tm nss env =
  let map_right f (a, b) = (a, f b) in
  function
  (* Referencing things *)
  | TmVar (fi, name, i) ->
      TmVar (fi, resolve_id env name, i)
  (* Introducing things *)
  | TmLam (fi, name, s, ty, body) ->
      TmLam
        (fi, empty_mangle name, s, ty, desugar_tm nss (delete_id env name) body)
  | TmLet (fi, name, s, ty, e, body) ->
      TmLet
        ( fi
        , empty_mangle name
        , s
        , ty
        , desugar_tm nss env e
        , desugar_tm nss (delete_id env name) body )
  | TmRecLets (fi, bindings, body) ->
      let env' =
        List.fold_left
          (fun env' (_, name, _, _, _) -> delete_id env' name)
          env bindings
      in
      TmRecLets
        ( fi
        , List.map
            (fun (fi, name, s, ty, e) ->
              (fi, empty_mangle name, s, ty, desugar_tm nss env' e))
            bindings
        , desugar_tm nss env' body )
  | TmCondef (fi, name, s, ty, body) ->
      TmCondef
        ( fi
        , empty_mangle name
        , s
        , ty
        , desugar_tm nss (delete_con env name) body )
  | TmConapp (fi, x, s, t) ->
      TmConapp (fi, resolve_con env x, s, desugar_tm nss env t)
  | TmClos _ as tm ->
      tm
  (* Both introducing and referencing *)
  | TmMatch (fi, target, pat, thn, els) ->
      let desugar_pname env = function
        | NameStr (n, s) ->
            (delete_id env n, NameStr (empty_mangle n, s))
        | NameWildcard ->
            (env, NameWildcard)
      in
      let rec desugar_pat_seq env pats =
        Mseq.Helpers.fold_right
          (fun p (env, pats) ->
            desugar_pat env p |> map_right (fun p -> Mseq.cons p pats))
          pats (env, Mseq.empty)
      and desugar_pat env = function
        | PatNamed (fi, name) ->
            name |> desugar_pname env |> map_right (fun n -> PatNamed (fi, n))
        | PatSeqTot (fi, pats) ->
            let env, pats = desugar_pat_seq env pats in
            (env, PatSeqTot (fi, pats))
        | PatSeqEdge (fi, l, x, r) ->
            let env, l = desugar_pat_seq env l in
            let env, x = desugar_pname env x in
            let env, r = desugar_pat_seq env r in
            (env, PatSeqEdge (fi, l, x, r))
        | PatRecord (fi, pats) ->
            let env = ref env in
            let pats =
              pats
              |> Record.map (fun p ->
                     let env', p = desugar_pat !env p in
                     env := env' ;
                     p)
            in
            (!env, PatRecord (fi, pats))
        | PatAnd (fi, l, r) ->
            let env, l = desugar_pat env l in
            let env, r = desugar_pat env r in
            (env, PatAnd (fi, l, r))
        | PatOr (fi, l, r) ->
            let env, l = desugar_pat env l in
            let env, r = desugar_pat env r in
            (env, PatOr (fi, l, r))
        | PatNot (fi, p) ->
            let env, p = desugar_pat env p in
            (env, PatNot (fi, p))
        | PatCon (fi, name, sym, p) ->
            desugar_pat env p
            |> map_right (fun p -> PatCon (fi, resolve_con env name, sym, p))
        | (PatInt _ | PatChar _ | PatBool _) as pat ->
            (env, pat)
      in
      let env', pat' = desugar_pat env pat in
      TmMatch
        ( fi
        , desugar_tm nss env target
        , pat'
        , desugar_tm nss env' thn
        , desugar_tm nss env els )
  (* Use *)
  | TmUse (fi, name, body) -> (
    match USMap.find_opt name nss with
    | None ->
        raise_error fi
          ("Unknown language fragment '" ^ Ustring.to_utf8 name ^ "'")
    | Some ns ->
        desugar_tm nss (merge_env_overwrite env ns) body )
  (* Simple recursions *)
  | TmApp (fi, a, b) ->
      TmApp (fi, desugar_tm nss env a, desugar_tm nss env b)
  | TmSeq (fi, tms) ->
      TmSeq (fi, Mseq.Helpers.map (desugar_tm nss env) tms)
  | TmRecord (fi, r) ->
      TmRecord (fi, Record.map (desugar_tm nss env) r)
  | TmRecordUpdate (fi, a, lab, b) ->
      TmRecordUpdate (fi, desugar_tm nss env a, lab, desugar_tm nss env b)
  | TmUtest (fi, a, b, using, body) ->
      let using_desugared = Option.map (desugar_tm nss env) using in
      TmUtest
        ( fi
        , desugar_tm nss env a
        , desugar_tm nss env b
        , using_desugared
        , desugar_tm nss env body )
  | TmNever fi ->
      TmNever fi
  (* Non-recursive *)
  | (TmConst _ | TmFix _) as tm ->
      tm

(* add namespace to nss (overwriting) if relevant, prepend a tm -> tm function to stack, return updated tuple. Should use desugar_tm, as well as desugar both sem and syn *)
let desugar_top (nss, (stack : (tm -> tm) list)) = function
  | TopLang (Lang (_, langName, includes, decls)) ->
      let add_lang ns lang =
        USMap.find_opt lang nss
        |> Option.default emptyMlangEnv
        |> merge_env_overwrite ns
      in
      let previous_ns = List.fold_left add_lang emptyMlangEnv includes in
      (* compute the namespace *)
      let mangle str = langName ^. us "_" ^. str in
      let cdecl_names (CDecl (_, name, _)) = (name, mangle name) in
      let add_decl {constructors; normals} = function
        | Data (_, _, cdecls) ->
            let new_constructors = List.to_seq cdecls |> Seq.map cdecl_names in
            {constructors= USMap.add_seq new_constructors constructors; normals}
        | Inter (_, name, _, _) ->
            {normals= USMap.add name (mangle name) normals; constructors}
      in
      let ns = List.fold_left add_decl previous_ns decls in
      (* wrap in "con"s *)
      let wrap_con ty_name (CDecl (fi, cname, ty)) tm =
        TmCondef
          ( fi
          , mangle cname
          , Symb.Helpers.nosym
          , TyArrow (ty, TyCon ty_name)
          , tm )
      in
      (* TODO(vipa,?): the type will likely be incorrect once we start doing product extensions of constructors *)
      let wrap_data decl tm =
        match decl with
        (* TODO(vipa,?): this does not declare the type itself *)
        | Data (_, name, cdecls) ->
            List.fold_right (wrap_con name) cdecls tm
        | _ ->
            tm
      in
      (* translate "Inter"s into (info * ustring * tm) *)
      let inter_to_tm fname fi params cases =
        let target = us "__sem_target" in
        let wrap_param (Param (fi, name, ty)) tm =
          TmLam (fi, name, Symb.Helpers.nosym, ty, tm)
        in
        TmLam
          ( fi
          , target
          , Symb.Helpers.nosym
          , TyUnknown
          , translate_cases fname (var target) cases )
        |> List.fold_right wrap_param params
        |> desugar_tm nss ns
      in
      let translate_inter = function
        | Inter (fi, name, params, cases) ->
            Some
              ( fi
              , mangle name
              , Symb.Helpers.nosym
              , TyUnknown
              , inter_to_tm name fi params cases )
        | _ ->
            None
      in
      (* put translated inters in a single letrec, then wrap in cons, then done *)
      let wrap tm =
        TmRecLets (NoInfo, List.filter_map translate_inter decls, tm)
        |> List.fold_right wrap_data decls
      in
      (USMap.add langName ns nss, wrap :: stack)
  (* The other tops are trivial translations *)
  | TopLet (Let (fi, id, ty, tm)) ->
      let wrap tm' =
        TmLet
          ( fi
          , empty_mangle id
          , Symb.Helpers.nosym
          , ty
          , desugar_tm nss emptyMlangEnv tm
          , tm' )
      in
      (nss, wrap :: stack)
  | TopRecLet (RecLet (fi, lets)) ->
      let wrap tm' =
        TmRecLets
          ( fi
          , List.map
              (fun (fi', id, ty, tm) ->
                ( fi'
                , empty_mangle id
                , Symb.Helpers.nosym
                , ty
                , desugar_tm nss emptyMlangEnv tm ))
              lets
          , tm' )
      in
      (nss, wrap :: stack)
  | TopCon (Con (fi, id, ty)) ->
      let wrap tm' =
        TmCondef (fi, empty_mangle id, Symb.Helpers.nosym, ty, tm')
      in
      (nss, wrap :: stack)
  | TopUtest (Utest (fi, lhs, rhs, using)) ->
      let wrap tm' = TmUtest (fi, lhs, rhs, using, tm') in
      (nss, wrap :: stack)

let desugar_post_flatten_with_nss nss (Program (_, tops, t)) =
  let acc_start = (nss, []) in
  let new_nss, stack = List.fold_left desugar_top acc_start tops in
  let desugared_tm =
    List.fold_left ( |> ) (desugar_tm new_nss emptyMlangEnv t) stack
  in
  (new_nss, desugared_tm)

(* Desugar top level statements after flattening language fragments. *)
let desugar_post_flatten prg =
  snd (desugar_post_flatten_with_nss USMap.empty prg)
