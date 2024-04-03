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
module USSet = Set.Make (Ustring)

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

(* === Types for MLang language fragments and their contents === *)

type sem_case_id = Symb.t

type sem_id = Symb.t

type syn_case_id = Symb.t

type syn_id = Symb.t

type alias_id = Symb.t

type sem_case =
  { id: sem_case_id
  ; pat: pat
  ; rhs: tm
  ; (* We precompute the normpat corresponding to pat, as well as the one
     * corresponding to not(pat) *)
    pos_pat: normpat
  ; neg_pat: normpat }

module SemCase = struct
  type t = sem_case

  let compare a b = Symb.compare a.id b.id
end

module SemCaseSet = Set.Make (SemCase)

module SubsetOrd = struct
  type t = sem_id * sem_id

  let compare (a1, a2) (b1, b2) =
    let res = Symb.compare a1 b1 in
    if res <> 0 then res else Symb.compare a2 b2
end

module SubsetOrdSet = Set.Make (SubsetOrd)

type sem_data =
  { id: sem_id
  ; fi: info
  ; ty: ty
  ; params: param list option
  ; cases: SemCaseSet.t
  ; (* We store the DAG of subset relations as a list of pairs (a, b),
     * where a \subset b. Note proper subset, since equality
     * means we should error because we can't order the patterns. *)
    subsets: SubsetOrdSet.t }

type syn_case =
  { id: syn_case_id
  ; fi: info
  ; def_here: bool
  ; ty_params: ustring list
  ; name: ustring * ustring (* prefix, name *)
  ; carried: ty }

type syn_data =
  { id: syn_id
  ; def_here: bool
  ; ty: ustring * ustring * int (* prefix, name, number of parameters *)
  ; cons: syn_case Record.t
  ; fi: info }

type alias_data =
  { id: alias_id
  ; def_here: bool
  ; name: ustring * ustring (* prefix, name *)
  ; params: ustring list
  ; ty: ty
  ; fi: info }

type ty_in_lang = (alias_data, syn_data) Either.t

type lang_data = {values: sem_data Record.t; types: ty_in_lang Record.t}

(* let spprint_inter_data {info; cases; _} : ustring = *)
(*   List.map *)
(*     (fun (fi, {pat; _}) -> *)
(*       us "  " ^. ustring_of_pat pat ^. us " at " ^. info2str fi ) *)
(*     cases *)
(*   |> Ustring.concat (us "\n") *)
(*   |> fun msg -> us "My location is " ^. info2str info ^. us "\n" ^. msg *)

(* let spprint_lang_data {inters; _} : ustring = *)
(*   Record.bindings inters *)
(*   |> List.map (fun (name, data) -> name ^. us "\n" ^. spprint_inter_data data) *)
(*   |> Ustring.concat (us "\n") *)

(* === Functions relating to merging and extending fragments === *)

(* NOTE(vipa, 2023-11-14): When we extend a language most components
 * of the old language are simply in scope, they should not be re-defined
 * in the new fragment; this function is what makes it so. *)
let pre_extend_lang : lang_data -> lang_data =
 fun lang ->
  let work_syn_case : syn_case -> syn_case =
   fun case -> {case with def_here= false}
  in
  let work_syn : syn_data -> syn_data =
   fun data ->
    {data with def_here= false; cons= Record.map work_syn_case data.cons}
  in
  let work_alias : alias_data -> alias_data =
   fun data -> {data with def_here= false}
  in
  { lang with
    types= Record.map (Either.map ~left:work_alias ~right:work_syn) lang.types
  }

(* NOTE(vipa, 2023-11-14): Compute the order between two sem cases
   based on the specificity of their patterns *)
let compute_order (fi : info)
    ({id= id1; pat= pat1; pos_pat= p1; neg_pat= n1; _} : sem_case)
    ({id= id2; pat= pat2; pos_pat= p2; neg_pat= n2; _} : sem_case) :
    (sem_case_id * sem_case_id) option =
  let string_of_pat pat = ustring_of_pat pat |> Ustring.to_utf8 in
  let info2str fi = info2str fi |> Ustring.to_utf8 in
  match order_query (p1, n1) (p2, n2) with
  | Subset ->
      Some (id1, id2)
  | Superset ->
      Some (id2, id1)
  | Equal ->
      raise_error fi
        ( "Patterns at "
        ^ info2str (pat_info pat1)
        ^ " and "
        ^ info2str (pat_info pat2)
        ^ " cannot be ordered by specificity; they match exactly the same \
           values." )
  | Disjoint ->
      None
  | Overlapping (only1, both, only2) ->
      "Two patterns in this semantic function cannot be ordered by \
       specificity (neither is more specific than the other), but the order \
       matters; they overlap." ^ "\n  "
      ^ info2str (pat_info pat1)
      ^ ": " ^ string_of_pat pat1 ^ "\n  "
      ^ info2str (pat_info pat2)
      ^ ": " ^ string_of_pat pat2 ^ "\n Example:" ^ "\n  Only in the first: "
      ^ string_of_pat only1 ^ "\n  In both: " ^ string_of_pat both
      ^ "\n  Only in the other: " ^ string_of_pat only2
      |> raise_error fi

(* NOTE(vipa, 2023-11-14): Merge two sems with the same name, failing
   if they originate from different root sems. *)
let merge_sems_in_lang : info -> ustring -> sem_data -> sem_data -> sem_data =
 fun fi name a b ->
  let su = Ustring.to_utf8 in
  if Symb.eqsym a.id b.id then
    let inconsistent_parameter_lists =
      match (a.params, b.params) with
      | Some p1, Some p2 ->
          Bool.not
            (List.equal
               (fun (Param (_, a, _)) (Param (_, b, _)) -> a =. b)
               p1 p2 )
      | _ ->
          false
    in
    if inconsistent_parameter_lists then
      raise_error fi
        ( "Trying to merge two 'sem's with inconsistent parameter lists \
           (length or names) into '" ^ su name ^ "' (previous definitions: "
        ^ su (info2str a.fi)
        ^ " and "
        ^ su (info2str b.fi)
        ^ ")" )
    else
      let new_subsets =
        let new_a =
          List.of_seq (SemCaseSet.to_seq (SemCaseSet.diff a.cases b.cases))
        in
        let new_b =
          List.of_seq (SemCaseSet.to_seq (SemCaseSet.diff b.cases a.cases))
        in
        liftA2 (compute_order fi) new_a new_b
        |> List.filter_map (fun x -> x)
        |> List.to_seq |> SubsetOrdSet.of_seq
      in
      { a with
        params= (if Option.is_some a.params then a.params else b.params)
      ; cases= SemCaseSet.union a.cases b.cases
      ; subsets=
          SubsetOrdSet.union
            (SubsetOrdSet.union a.subsets b.subsets)
            new_subsets }
  else
    raise_error fi
      ( "'sem' name conflict, found two definitions of '" ^ su name
      ^ "', one at "
      ^ su (info2str a.fi)
      ^ "and one at "
      ^ su (info2str b.fi) )

let merge_aliases_in_lang :
    info -> ustring -> alias_data -> alias_data -> alias_data =
 fun fi name a b ->
  let su = Ustring.to_utf8 in
  if Symb.eqsym a.id b.id then a
  else
    raise_error fi
      ("Name conflict, there are two type aliases named '" ^ su name ^ "'")

let merge_syn_cases_in_lang :
    info -> ustring -> syn_case -> syn_case -> syn_case =
 fun fi name a b ->
  let su = Ustring.to_utf8 in
  if Symb.eqsym a.id b.id then a
  else
    raise_error fi
      ( "Conflicting definitions of constructor '" ^ su name ^ "', at "
      ^ su (info2str a.fi)
      ^ " and "
      ^ su (info2str b.fi) )

let merge_syns_in_lang : info -> ustring -> syn_data -> syn_data -> syn_data =
 fun fi name a b ->
  let su = Ustring.to_utf8 in
  if Symb.eqsym a.id b.id then
    match (a.ty, b.ty) with
    | (_, _, a_count), (_, _, b_count) when a_count <> b_count ->
        raise_error fi
          ( "Trying to merge two 'syn's with different number of parameters \
             into '" ^ su name ^ "' (previous definitions: "
          ^ su (info2str a.fi)
          ^ " and "
          ^ su (info2str b.fi)
          ^ ")" )
    | _ ->
        { a with
          cons=
            Record.union
              (fun name a b -> Some (merge_syn_cases_in_lang fi name a b))
              a.cons b.cons }
  else
    raise_error fi
      ( "'syn' name conflict, found two definitions of '" ^ su name
      ^ "', one at "
      ^ su (info2str a.fi)
      ^ " and one at "
      ^ su (info2str b.fi) )

let merge_types_in_lang :
    info -> ustring -> ty_in_lang -> ty_in_lang -> ty_in_lang =
 fun fi name a b ->
  let su = Ustring.to_utf8 in
  match (a, b) with
  | Left _, Right _ | Right _, Left _ ->
      raise_error fi
        ("Name conflict, a type alias and a syn are named '" ^ su name ^ "'")
  | Left a, Left b ->
      Left (merge_aliases_in_lang fi name a b)
  | Right a, Right b ->
      Right (merge_syns_in_lang fi name a b)

let merge_langs : info -> lang_data -> lang_data -> lang_data =
 fun fi a b ->
  { values=
      Record.union
        (fun name a b -> Some (merge_sems_in_lang fi name a b))
        a.values b.values
  ; types=
      Record.union
        (fun name a b -> Some (merge_types_in_lang fi name a b))
        a.types b.types }

(* === Functions that facilitate renaming types and values, and thus merging them after the fact === *)

module NoCap = struct
  (* NOTE(vipa, 2023-11-15): This only supportrs renaming type
     constructors and values, not type variabels nor constructors *)
  type small_env = {subst: ustring Record.t; avoid: USSet.t}

  let empty_small = {subst= Record.empty; avoid= USSet.empty}

  type big_env = {values: small_env; ty_cons: small_env}

  let empty_big = {values= empty_small; ty_cons= empty_small}

  let subst_name : ustring -> small_env -> ustring =
   fun name env -> Option.value ~default:name (Record.find_opt name env.subst)

  let add_subst : ustring -> ustring -> small_env -> small_env =
   fun before now env ->
    {subst= Record.add before now env.subst; avoid= USSet.add now env.avoid}

  let subst_ty_con_env (before : ustring) (now : ustring) : big_env =
    {empty_big with ty_cons= add_subst before now empty_big.ty_cons}

  let subst_value_env (before : ustring) (now : ustring) : big_env =
    {empty_big with values= add_subst before now empty_big.values}

  let process_binding : small_env -> ustring -> small_env * ustring =
   fun env name ->
    if USSet.mem name env.avoid then
      let new_name = name ^. us "_new" in
      (add_subst name new_name env, new_name)
    else (env, name)

  let rec subst_ty (env : big_env) : ty -> ty = function
    | TyCon (fi, name, data) ->
        TyCon (fi, subst_name name env.ty_cons, data)
    | TyUse (fi, _, _) ->
        raise_error fi
          "Compiler limitation: we can't easily rename syns or sems if 'use' \
           is somewhere in the language fragment."
    | ty ->
        smap_ty_ty (subst_ty env) ty

  let rec subst_pat (env : big_env) : pat -> big_env * pat = function
    | PatNamed (fi, NameStr (id, sym)) ->
        let values, id = process_binding env.values id in
        ({env with values}, PatNamed (fi, NameStr (id, sym)))
    | PatSeqEdge (fi, l, NameStr (id, sym), r) ->
        let env, l = Mseq.Helpers.map_accum_left subst_pat env l in
        let values, id = process_binding env.values id in
        let env = {env with values} in
        let env, r = Mseq.Helpers.map_accum_left subst_pat env r in
        (env, PatSeqEdge (fi, l, NameStr (id, sym), r))
    | _ ->
        failwith "todo"

  let rec subst_tm (env : big_env) : tm -> tm = function
    | TmVar (fi, name, sym, pesym, frozen) ->
        let name = subst_name name env.values in
        TmVar (fi, name, sym, pesym, frozen)
    | TmLam (fi, name, sym, pesym, ty, tm) ->
        let ty = subst_ty env ty in
        let values, name = process_binding env.values name in
        let env = {env with values} in
        let tm = subst_tm env tm in
        TmLam (fi, name, sym, pesym, ty, tm)
    | TmLet (fi, name, sym, ty, body, inexpr) ->
        let ty = subst_ty env ty in
        let body = subst_tm env body in
        let values, name = process_binding env.values name in
        let env = {env with values} in
        let inexpr = subst_tm env inexpr in
        TmLet (fi, name, sym, ty, body, inexpr)
    | TmRecLets (fi, lets, inexpr) ->
        let process values (fi, id, sym, ty, tm) =
          let values, id = process_binding values id in
          (values, (fi, id, sym, ty, tm))
        in
        let values, lets = List.fold_left_map process env.values lets in
        let env = {env with values} in
        let subst_let (fi, id, sym, ty, tm) =
          (fi, id, sym, subst_ty env ty, subst_tm env tm)
        in
        let lets = List.map subst_let lets in
        TmRecLets (fi, lets, subst_tm env inexpr)
    | TmType (fi, name, params, ty, tm) ->
        let ty = subst_ty env ty in
        let ty_cons, name = process_binding env.ty_cons name in
        let env = {env with ty_cons} in
        TmType (fi, name, params, ty, subst_tm env tm)
    | TmUse (fi, _, _) ->
        raise_error fi
          "Compiler limitation: we can't easily rename syns or sems if 'use' \
           is somewhere in the language fragment."
    | TmExt (fi, name, sym, side, ty, tm) ->
        let ty = subst_ty env ty in
        let values, name = process_binding env.values name in
        let tm = subst_tm {env with values} tm in
        TmExt (fi, name, sym, side, ty, tm)
    | TmMatch (fi, scrut, pat, th, el) ->
        let scrut = subst_tm env scrut in
        let new_env, pat = subst_pat env pat in
        let th = subst_tm new_env th in
        let el = subst_tm env el in
        TmMatch (fi, scrut, pat, th, el)
    | tm ->
        smap_tm_tm (subst_tm env) tm

  let subst_lang (_env : big_env) (_lang : lang_data) : lang_data =
    (* NOTE(vipa, 2023-11-15):

       I'm not sure we can actually do full and proper capture avoiding
       substitution here, because of `use`. Consider:

       lang X
         sem bar =
       end

       lang A
         sem foo =
         | _ -> use X in (foo, bar)
       end

       lang B = A
         with bar = A.foo
       end

       Here we cannot rename `foo` to `bar` without capture, because we
       cannot also rename `bar` in `X`.

       For this reason I'm waiting with actually using the machinery
       above, that should otherwise do decent capture-avoiding
       substitution.

       It's worth noting that none of this would be an issue if we had
       symbols, so a potential fix would be to make symbolize in boot
       respect already placed symbols.

       It's also worth noting that this would also not be an issue with
       dot-notation (e.g., `X.foo` instead of `use X in foo`), because
       the former makes it clear that we're using a name in `X` rather
       than a name from `X` or the current scope.
    *)
    failwith
      "We don't presently support renaming `syn`s or `sem`s using `with`. See \
       this error in the code for why."
end

let rec_add_with :
    ('a -> 'a -> 'a) -> ustring -> 'a -> 'a Record.t -> 'a Record.t =
 fun f k v m ->
  let f = function Some v1 -> Some (f v1 v) | None -> Some v in
  Record.update k f m

let rename_type :
    info -> ustring -> ustring * ustring * syn_id -> lang_data -> lang_data =
 fun fi orig_name (new_prefix, new_name, new_id) data ->
  let update_alias (alias : alias_data) =
    {alias with id= new_id; def_here= true; name= (new_prefix, new_name)}
  in
  let update_syn (syn : syn_data) =
    let _, _, param_count = syn.ty in
    let update_syn_case (c : syn_case) =
      {c with name= (new_prefix, snd c.name); def_here= true}
    in
    { syn with
      id= new_id
    ; def_here= true
    ; ty= (new_prefix, new_name, param_count)
    ; cons= Record.map update_syn_case syn.cons }
  in
  match Record.find_opt orig_name data.types with
  | Some ty_content ->
      let types = Record.remove orig_name data.types in
      let ty_content =
        Either.map ~left:update_alias ~right:update_syn ty_content
      in
      let types =
        rec_add_with
          (merge_types_in_lang fi new_name)
          new_name ty_content types
      in
      let data = {data with types} in
      if orig_name =. new_name then data
      else
        let subst = NoCap.subst_ty_con_env orig_name new_name in
        NoCap.subst_lang subst data
  | None ->
      data

let rename_value :
    info -> ustring -> ustring * ustring * sem_id -> lang_data -> lang_data =
 fun fi orig_name (_new_prefix, new_name, new_id) data ->
  match Record.find_opt orig_name data.values with
  | Some val_content ->
      let values = Record.remove orig_name data.values in
      let update_sem (sem : sem_data) = {sem with id= new_id} in
      let val_content = update_sem val_content in
      let values =
        rec_add_with
          (merge_sems_in_lang fi new_name)
          new_name val_content values
      in
      let data = {data with values} in
      if orig_name =. new_name then data
      else
        let subst = NoCap.subst_value_env orig_name new_name in
        NoCap.subst_lang subst data
  | None ->
      data

(* === Translating from MLang (list of top-declarations, including lang) to MExpr (single tm) === *)

type mlang_env =
  { values: ustring Record.t
  ; ty_cons: ustring Record.t
  ; constructors: ustring Record.t
  ; languages: lang_data Record.t
  ; language_envs: mlang_env Record.t }

let empty_mlang_env =
  { values= Record.empty
  ; ty_cons= Record.empty
  ; constructors= Record.empty
  ; languages= Record.empty
  ; language_envs= Record.empty }

let empty_mangle : ustring -> ustring = fun x -> x

let lang_value_mangle : ustring * ustring -> ustring =
 fun (prefix, name) -> us "v" ^. prefix ^. us "_" ^. name

let lang_con_mangle : ustring * ustring -> ustring =
 fun (prefix, name) -> prefix ^. us "_" ^. name

let merge_env_prefer_right : mlang_env -> mlang_env -> mlang_env =
 fun a b ->
  { values= Record.union (fun _ _a b -> Some b) a.values b.values
  ; ty_cons= Record.union (fun _ _a b -> Some b) a.ty_cons b.ty_cons
  ; constructors=
      Record.union (fun _ _a b -> Some b) a.constructors b.constructors
  ; languages= Record.union (fun _ _a b -> Some b) a.languages b.languages
  ; language_envs=
      Record.union (fun _ _a b -> Some b) a.language_envs b.language_envs }

let rec translate_ty (env : mlang_env) : ty -> ty =
  let translate_cons =
    List.map (fun k ->
        Option.value ~default:k (Record.find_opt k env.constructors) )
  in
  function
  | TyCon (fi, id, data) -> (
      let data =
        Option.map
          (function
            | DCons ks ->
                DCons (translate_cons ks)
            | DNCons ks ->
                DNCons (translate_cons ks)
            | DVar v ->
                DVar v )
          data
      in
      match Record.find_opt id env.ty_cons with
      | Some id ->
          TyCon (fi, id, data)
      | None ->
          TyCon (fi, empty_mangle id, data) )
  | TyUse (fi, lang, ty) -> (
    match Record.find_opt lang env.language_envs with
    | Some new_env ->
        translate_ty (merge_env_prefer_right env new_env) ty
    | None ->
        raise_error fi
          ("Unbound language fragment '" ^ Ustring.to_utf8 lang ^ "'") )
  | TyAll (fi, id, kind, ty) ->
      let kind =
        kind
        |> Option.map
             (List.map (fun (t, lower, upper) ->
                  let t =
                    match Record.find_opt t env.ty_cons with
                    | Some t ->
                        t
                    | None ->
                        empty_mangle t
                  in
                  let lower = translate_cons lower in
                  let upper = Option.map translate_cons upper in
                  (t, lower, upper) ) )
      in
      TyAll (fi, id, kind, translate_ty env ty)
  | ty ->
      let ty = smap_ty_ty (translate_ty env) ty in
      ty

let rec translate_pat (env : mlang_env) : pat -> mlang_env * pat = function
  | PatNamed (_, NameStr (id, _)) as pat ->
      ({env with values= Record.remove id env.values}, pat)
  | PatSeqEdge (fi, l, (NameStr (id, _) as name), r) ->
      let env, l = Mseq.Helpers.map_accum_left translate_pat env l in
      let env, r = Mseq.Helpers.map_accum_left translate_pat env r in
      ( {env with values= Record.remove id env.values}
      , PatSeqEdge (fi, l, name, r) )
  | PatCon (fi, id, sym, pat) ->
      let id, sym =
        match Record.find_opt id env.constructors with
        | Some id ->
            (id, Symb.Helpers.nosym)
        | None ->
            (id, sym)
      in
      let env, pat = translate_pat env pat in
      (env, PatCon (fi, id, sym, pat))
  | pat ->
      smap_accum_left_pat_pat translate_pat env pat

let rec translate_tm (env : mlang_env) : tm -> tm = function
  | TmVar (fi, name, sym, pesym, frozen) ->
      let name, sym =
        match Record.find_opt name env.values with
        | Some name ->
            (name, Symb.Helpers.nosym)
        | None ->
            (name, sym)
      in
      (* TODO(vipa, 2023-11-14): is it correct to do nothing about pesym? *)
      TmVar (fi, name, sym, pesym, frozen)
  | TmLam (fi, name, sym, pesym, ty, tm) ->
      let new_env = {env with values= Record.remove name env.values} in
      TmLam
        ( fi
        , empty_mangle name
        , sym
        , pesym
        , translate_ty env ty
        , translate_tm new_env tm )
  | TmLet (fi, name, sym, ty, body, inexpr) ->
      let new_env = {env with values= Record.remove name env.values} in
      TmLet
        ( fi
        , empty_mangle name
        , sym
        , translate_ty env ty
        , translate_tm env body
        , translate_tm new_env inexpr )
  | TmRecLets (fi, lets, inexpr) ->
      let rem_value values (_, id, _, _, _) = Record.remove id values in
      let new_env =
        {env with values= List.fold_left rem_value env.values lets}
      in
      let translate_let (fi, id, sym, ty, tm) =
        ( fi
        , empty_mangle id
        , sym
        , translate_ty new_env ty
        , translate_tm new_env tm )
      in
      TmRecLets (fi, List.map translate_let lets, translate_tm new_env inexpr)
  | TmType (fi, name, params, ty, tm) ->
      let new_env = {env with ty_cons= Record.remove name env.ty_cons} in
      TmType
        ( fi
        , empty_mangle name
        , params
        , translate_ty env ty
        , translate_tm new_env tm )
  | TmConDef (fi, name, sym, ty, tm) ->
      let new_env =
        {env with constructors= Record.remove name env.constructors}
      in
      TmConDef
        ( fi
        , empty_mangle name
        , sym
        , translate_ty env ty
        , translate_tm new_env tm )
  | TmConApp (fi, name, sym, tm) ->
      let name, sym =
        match Record.find_opt name env.constructors with
        | Some name ->
            (name, Symb.Helpers.nosym)
        | None ->
            (name, sym)
      in
      TmConApp (fi, name, sym, translate_tm env tm)
  | TmUse (fi, lang, tm) -> (
    match Record.find_opt lang env.language_envs with
    | Some lang_env ->
        translate_tm (merge_env_prefer_right env lang_env) tm
    | None ->
        raise_error fi
          ("Unbound language fragment '" ^ Ustring.to_utf8 lang ^ "'") )
  | TmExt (fi, name, sym, side, ty, tm) ->
      let new_env = {env with values= Record.add name name env.values} in
      TmExt (fi, name, sym, side, translate_ty env ty, translate_tm new_env tm)
  | TmMatch (fi, scrut, pat, th, el) ->
      let new_env, pat = translate_pat env pat in
      TmMatch
        ( fi
        , translate_tm env scrut
        , pat
        , translate_tm new_env th
        , translate_tm env el )
  | ( TmApp _
    | TmConst _
    | TmSeq _
    | TmRecord _
    | TmRecordUpdate _
    | TmUtest _
    | TmNever _
    | TmClos _
    | TmRef _
    | TmTensor _
    | TmDive _
    | TmPreRun _
    | TmBox _ ) as tm ->
      let tm = smap_tm_ty (translate_ty env) tm in
      let tm = smap_tm_tm (translate_tm env) tm in
      tm

let add_decl_to_lang (lang_fi : info) (lang_name : ustring) (data : lang_data)
    : decl -> lang_data = function
  | Data (fi, name, param_count, constructors) ->
      let syn =
        match Record.find_opt name data.types with
        | Some (Right syn) ->
            syn
        | Some _ ->
            raise_error fi
              ( "Trying to define a 'syn' that's already defined as an alias ('"
              ^ Ustring.to_utf8 name ^ "')." )
        | None ->
            { id= Symb.gensym ()
            ; def_here= true
            ; ty= (lang_name, name, param_count)
            ; cons= Record.empty
            ; fi }
      in
      let add_con : syn_case Record.t -> cdecl -> syn_case Record.t =
       fun syn (CDecl (fi, ty_params, name, carried)) ->
        let f : syn_case option -> syn_case option = function
          | Some con ->
              raise_error fi
                ( "Redefinition of constructor '" ^ Ustring.to_utf8 name
                ^ "', previously defined at "
                ^ Ustring.to_utf8 (info2str con.fi) )
          | None ->
              Some
                { id= Symb.gensym ()
                ; fi
                ; def_here= true
                ; ty_params
                ; name= (lang_name, name)
                ; carried }
        in
        Record.update name f syn
      in
      let syn =
        {syn with cons= List.fold_left add_con syn.cons constructors}
      in
      {data with types= Record.add name (Either.Right syn) data.types}
  | Inter (fi, name, ty, params, cases) ->
      let sem =
        match Record.find_opt name data.values with
        | Some sem ->
            { sem with
              params= (if Option.is_some sem.params then sem.params else params)
            }
        | None ->
            { id= Symb.gensym ()
            ; fi
            ; ty
            ; params
            ; cases= SemCaseSet.empty
            ; subsets= SubsetOrdSet.empty }
      in
      let add_case sem (pat, rhs) =
        let id = Symb.gensym () in
        let pos_pat = pat_to_normpat pat in
        let neg_pat = normpat_complement pos_pat in
        let case = {id; pat; rhs; pos_pat; neg_pat} in
        let subsets =
          SemCaseSet.to_seq sem.cases
          |> Seq.filter_map (compute_order lang_fi case)
          |> Seq.fold_left (fun acc x -> SubsetOrdSet.add x acc) sem.subsets
        in
        {sem with subsets; cases= SemCaseSet.add case sem.cases}
      in
      let sem = List.fold_left add_case sem cases in
      {data with values= Record.add name sem data.values}
  | Alias (fi, name, params, ty) ->
      if Record.mem name data.types then
        raise_error fi
          ( "Duplicate definition, a type with name '" ^ Ustring.to_utf8 name
          ^ "' is already defined." )
      else
        let alias =
          { id= Symb.gensym ()
          ; def_here= true
          ; name= (lang_name, name)
          ; params
          ; ty
          ; fi }
        in
        {data with types= Record.add name (Either.Left alias) data.types}

let lang_to_env : ustring -> lang_data -> mlang_env =
 fun name lang ->
  let values =
    Record.to_seq lang.values
    |> Seq.map (fun (n, _) -> (n, lang_value_mangle (name, n)))
    |> Record.of_seq
  in
  let mk_type_pair : ustring * ty_in_lang -> ustring * ustring = function
    | n, Either.Left alias ->
        (n, lang_con_mangle alias.name)
    | n, Either.Right {ty= pre, name, _; _} ->
        (n, lang_con_mangle (pre, name))
  in
  let ty_cons =
    Record.to_seq lang.types |> Seq.map mk_type_pair |> Record.of_seq
  in
  let constructors =
    Record.to_seq lang.types |> Seq.map snd
    |> Seq.filter_map Either.find_right
    |> Seq.flat_map (fun x -> Record.to_seq x.cons)
    |> Seq.map (fun (n, (case : syn_case)) -> (n, lang_con_mangle case.name))
    |> Record.of_seq
  in
  { values
  ; ty_cons
  ; constructors
  ; languages= Record.empty
  ; language_envs= Record.empty }

let wrap_syn_types : lang_data -> tm -> tm =
 fun lang tm ->
  let wrap_syn (tm : tm) (syn : syn_data) =
    let pre, name, param_count = syn.ty in
    TmType
      ( syn.fi
      , lang_con_mangle (pre, name)
      , List.init param_count (fun _ -> us "a")
      , TyVariant (syn.fi, [])
      , tm )
  in
  Record.to_seq lang.types |> Seq.map snd
  |> Seq.filter_map Either.find_right
  |> Seq.filter (fun (syn : syn_data) -> syn.def_here)
  |> Seq.fold_left wrap_syn tm

let wrap_aliases : mlang_env -> lang_data -> tm -> tm =
 fun env lang tm ->
  let wrap_alias (alias : alias_data) (tm : tm) =
    TmType
      ( alias.fi
      , lang_con_mangle alias.name
      , alias.params
      , translate_ty env alias.ty
      , tm )
  in
  Record.to_seq lang.types |> Seq.map snd
  |> Seq.filter_map Either.find_left
  |> Seq.filter (fun (alias : alias_data) -> alias.def_here)
  |> List.of_seq
  |> List.sort (fun (a : alias_data) (b : alias_data) ->
         Symb.compare a.id b.id )
  |> fun aliases -> List.fold_right wrap_alias aliases tm

let wrap_cons : mlang_env -> lang_data -> tm -> tm =
 fun env lang tm ->
  let cons_with_syn_name (syn : syn_data) : (ustring * syn_case) Seq.t =
    let _, name, _ = syn.ty in
    Record.to_seq syn.cons |> Seq.map (fun (_, c) -> (name, c))
  in
  let wrap_con (tm : tm) ((name : ustring), (con : syn_case)) =
    let wrap_all (tyvar : ustring) (ty : ty) =
      TyAll (con.fi, tyvar, None, ty)
    in
    let wrap_app (ty : ty) (tyvar : ustring) =
      TyApp (con.fi, ty, TyVar (con.fi, tyvar))
    in
    let ret =
      List.fold_left wrap_app (TyCon (con.fi, name, None)) con.ty_params
    in
    let ty = TyArrow (con.fi, con.carried, ret) in
    let ty = List.fold_right wrap_all con.ty_params ty in
    TmConDef
      ( con.fi
      , lang_con_mangle con.name
      , Symb.Helpers.nosym
      , translate_ty env ty
      , tm )
  in
  Record.to_seq lang.types |> Seq.map snd
  |> Seq.filter_map Either.find_right
  |> Seq.flat_map cons_with_syn_name
  |> Seq.filter (fun (_, (con : syn_case)) -> con.def_here)
  |> Seq.fold_left wrap_con tm

let wrap_sems : mlang_env -> ustring -> lang_data -> tm -> tm =
 fun env lang_name lang tm ->
  let sem_to_binding ((name : ustring), (sem : sem_data)) :
      info * ustring * Symb.t * ty * tm =
    let mk_with_body body =
      ( sem.fi
      , lang_value_mangle (lang_name, name)
      , Symb.Helpers.nosym
      , translate_ty env sem.ty
      , body )
    in
    if SemCaseSet.is_empty sem.cases then
      mk_with_body
        (TmLam
           ( sem.fi
           , us "x"
           , Symb.Helpers.nosym
           , false
           , TyUnknown sem.fi
           , TmNever sem.fi ) )
    else
      let scrut =
        TmVar (sem.fi, us "__sem_target", Symb.Helpers.nosym, false, false)
      in
      let cases =
        let vertices =
          SemCaseSet.to_seq sem.cases
          |> Seq.map (fun (case : sem_case) -> case.id)
          |> List.of_seq
        in
        let edges = SubsetOrdSet.elements sem.subsets in
        let find_by_id id =
          (* NOTE(vipa, 2023-11-15): The compare function for
             SemCaseSet only looks at `id`, thus this is ok *)
          SemCaseSet.find
            { id
            ; pat= Obj.magic ()
            ; rhs= Obj.magic ()
            ; pos_pat= Obj.magic ()
            ; neg_pat= Obj.magic () }
            sem.cases
        in
        topo_sort Symb.eqsym edges vertices |> List.map find_by_id
      in
      let wrap_case (case : sem_case) (tm : tm) =
        TmMatch (pat_info case.pat, scrut, case.pat, case.rhs, tm)
      in
      let wrap_param (Param (fi, name, ty)) (tm : tm) =
        TmLam (fi, name, Symb.Helpers.nosym, false, ty, tm)
      in
      let body = List.fold_right wrap_case cases (TmNever sem.fi) in
      let body =
        TmLam
          ( sem.fi
          , us "__sem_target"
          , Symb.Helpers.nosym
          , false
          , TyUnknown sem.fi
          , body )
      in
      let body =
        List.fold_right wrap_param (Option.value ~default:[] sem.params) body
      in
      ( sem.fi
      , lang_value_mangle (lang_name, name)
      , Symb.Helpers.nosym
      , translate_ty env sem.ty
      , translate_tm env body )
  in
  if Record.is_empty lang.values then tm
  else
    TmRecLets
      ( NoInfo
      , Record.to_seq lang.values |> Seq.map sem_to_binding |> List.of_seq
      , tm )

let lang_gen : mlang_env -> ustring -> lang_data -> mlang_env * (tm -> tm) =
 fun env lang_name lang ->
  let lang_env = lang_to_env lang_name lang in
  let wrap tm =
    let env = merge_env_prefer_right env lang_env in
    wrap_syn_types lang
      (wrap_aliases env lang
         (wrap_cons env lang (wrap_sems env lang_name lang tm)) )
  in
  (lang_env, wrap)

let translate_lang (env : mlang_env) (Lang (fi, name, includes, renames, decls))
    : mlang_env * (tm -> tm) =
  let su = Ustring.to_utf8 in
  let fetch_include inc =
    match Record.find_opt inc env.languages with
    | Some lang ->
        (inc, lang)
    | None ->
        raise_error fi ("Unknown language '" ^ su inc ^ "' in include list.")
  in
  let apply_rename includes (With (fi, kind, new_name, inputs)) =
    let f =
      match kind with WithType -> rename_type | WithValue -> rename_value
    in
    let id = Symb.gensym () in
    let f lang orig_name = f fi orig_name (name, new_name, id) lang in
    let process_input includes (lang_name, orig_name) =
      let f = function
        | Some lang ->
            Some (f lang orig_name)
        | None ->
            raise_error fi
              ("Unknown language '" ^ su lang_name ^ "' in 'with' clause.")
      in
      Record.update lang_name f includes
    in
    List.fold_left process_input includes inputs
  in
  let includes =
    List.to_seq includes |> Seq.map fetch_include |> Record.of_seq
  in
  let includes = List.fold_left apply_rename includes renames in
  let lang = {values= Record.empty; types= Record.empty} in
  let lang =
    Record.to_seq includes |> Seq.map snd
    |> Seq.fold_left (merge_langs fi) lang
  in
  let lang = List.fold_left (add_decl_to_lang fi name) lang decls in
  let lang_env, wrap = lang_gen env name lang in
  let new_env =
    { env with
      languages= Record.add name (pre_extend_lang lang) env.languages
    ; language_envs= Record.add name lang_env env.language_envs }
  in
  (new_env, wrap)

let translate_top (env : mlang_env) : top -> mlang_env * (tm -> tm) = function
  | TopLang lang ->
      translate_lang env lang
  | TopLet (Let (fi, id, ty, tm)) ->
      let new_env = {env with values= Record.remove id env.values} in
      let wrap inexpr =
        TmLet
          ( fi
          , empty_mangle id
          , Symb.Helpers.nosym
          , translate_ty new_env ty
          , translate_tm new_env tm
          , inexpr )
      in
      (new_env, wrap)
  | TopType (Type (fi, id, params, ty)) ->
      let new_env = {env with ty_cons= Record.remove id env.ty_cons} in
      let wrap inexpr =
        TmType (fi, empty_mangle id, params, translate_ty env ty, inexpr)
      in
      (new_env, wrap)
  | TopRecLet (RecLet (fi, lets)) ->
      let rem_value values (_, id, _, _) = Record.remove id values in
      let new_env =
        {env with values= List.fold_left rem_value env.values lets}
      in
      let translate_binding (fi', id, ty, tm) =
        ( fi'
        , empty_mangle id
        , Symb.Helpers.nosym
        , translate_ty new_env ty
        , translate_tm new_env tm )
      in
      let wrap inexpr =
        TmRecLets (fi, List.map translate_binding lets, inexpr)
      in
      (new_env, wrap)
  | TopCon (Con (fi, id, ty)) ->
      let new_env =
        {env with constructors= Record.remove id env.constructors}
      in
      let wrap inexpr =
        TmConDef
          (fi, empty_mangle id, Symb.Helpers.nosym, translate_ty env ty, inexpr)
      in
      (new_env, wrap)
  | TopUtest (Utest (fi, lhs, rhs, using, onfail)) ->
      let wrap inexpr =
        TmUtest
          ( fi
          , translate_tm env lhs
          , translate_tm env rhs
          , Option.map (translate_tm env) using
          , Option.map (translate_tm env) onfail
          , inexpr )
      in
      (env, wrap)
  | TopExt (Ext (fi, id, e, ty)) ->
      (* NOTE(vipa, 2023-11-14): Externals must have exactly the given
         name, thus we leave them unchanged, which we do by recording them
         in `values` (otherwise bindings would be `empty_mangle`d). *)
      let new_env = {env with values= Record.add id id env.values} in
      let wrap inexpr =
        TmExt (fi, id, Symb.Helpers.nosym, e, translate_ty env ty, inexpr)
      in
      (new_env, wrap)

let translate_tops_with_env (env : mlang_env) (tops : top list) (bot : tm) :
    mlang_env * tm =
  let rec work env = function
    | [] ->
        (env, translate_tm env bot)
    | top :: tops ->
        let env, wrap = translate_top env top in
        let env, bot = work env tops in
        (env, wrap bot)
  in
  work env tops

let translate_program_with_env (env : mlang_env)
    (Program (_includes, tops, bot)) : mlang_env * tm =
  translate_tops_with_env env tops bot

let translate_program (p : program) : tm =
  snd (translate_program_with_env empty_mlang_env p)
