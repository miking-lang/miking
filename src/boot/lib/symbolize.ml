open Intrinsics
open Ustring.Op
open Msg
open Ast

type sym_env =
  { var: Symb.t sidmap
  ; con: Symb.t sidmap
  ; ty: Symb.t sidmap
  ; label: Symb.t sidmap }

let empty_sym_env =
  {var= SidMap.empty; con= SidMap.empty; ty= SidMap.empty; label= SidMap.empty}

(* Option for allowing/disallowing free variables in symbolize *)
let allow_free = ref false

let sym_env_to_assoc env =
  let vars = List.map (fun (k, v) -> (IdVar k, v)) (SidMap.bindings env.var) in
  let cons = List.map (fun (k, v) -> (IdCon k, v)) (SidMap.bindings env.con) in
  let tys = List.map (fun (k, v) -> (IdType k, v)) (SidMap.bindings env.ty) in
  let labels =
    List.map (fun (k, v) -> (IdLabel k, v)) (SidMap.bindings env.label)
  in
  vars @ cons @ tys @ labels

let findsym fi id env =
  try
    match id with
    | IdVar x ->
        SidMap.find x env.var
    | IdCon x ->
        SidMap.find x env.con
    | IdType x ->
        SidMap.find x env.ty
    | IdLabel x ->
        SidMap.find x env.label
  with Not_found ->
    let x, kindstr =
      match id with
      | IdVar x ->
          (x, "variable")
      | IdCon x ->
          (x, "constructor")
      | IdType x ->
          (x, "type variable")
      | IdLabel x ->
          (x, "label")
    in
    if !allow_free then Symb.Helpers.nosym
    else raise_error fi ("Unknown " ^ kindstr ^ " '" ^ string_of_sid x ^ "'")

let findsym_opt id env =
  match id with
  | IdVar x ->
      SidMap.find_opt x env.var
  | IdCon x ->
      SidMap.find_opt x env.con
  | IdType x ->
      SidMap.find_opt x env.ty
  | IdLabel x ->
      SidMap.find_opt x env.label

let addsym id sym env =
  match id with
  | IdVar x ->
      {env with var= SidMap.add x sym env.var}
  | IdCon x ->
      {env with con= SidMap.add x sym env.con}
  | IdType x ->
      {env with ty= SidMap.add x sym env.ty}
  | IdLabel x ->
      {env with label= SidMap.add x sym env.label}

let merge_sym_envs_pick_left l r =
  let pick_left _ x _ = Some x in
  { var= SidMap.union pick_left l.var r.var
  ; con= SidMap.union pick_left l.con r.con
  ; ty= SidMap.union pick_left l.ty r.ty
  ; label= SidMap.union pick_left l.label r.label }

(* Add symbol associations between lambdas, patterns, and variables. The function also
   constructs TmConApp terms from the combination of variables and function applications. *)
let rec symbolize (env : sym_env) (t : tm) =
  (* add_name is only called in sPat and it reuses previously generated symbols.
   * This is imperative for or-patterns, since both branches should give the same symbols,
   * e.g., [a] | [a, _] should give the same symbol to both "a"s.
   * However, this also has an effect on what happens when the same name is bound multiple times
   * in a pattern in other cases. In particular, this means that, e.g., the pattern
   * [a, a] assigns the same symbol to both "a"s, which may or may not be desirable. Which
   * introduced binding gets used then depends on what try_match does for the pattern. *)
  let add_name (x : ident) (patEnv : sym_env) =
    match findsym_opt x patEnv with
    | Some s ->
        (patEnv, s)
    | None ->
        let s = Symb.gensym () in
        (addsym x s patEnv, s)
  in
  let rec s_pat_sequence patEnv pats =
    Mseq.Helpers.fold_right
      (fun p (patEnv, ps) ->
        let patEnv, p = sPat patEnv p in
        (patEnv, Mseq.cons p ps) )
      (patEnv, Mseq.empty) pats
  and sPat (patEnv : sym_env) = function
    | PatNamed (fi, NameStr (x, _)) ->
        let patEnv, s = add_name (IdVar (sid_of_ustring x)) patEnv in
        (patEnv, PatNamed (fi, NameStr (x, s)))
    | PatNamed (_, NameWildcard) as pat ->
        (patEnv, pat)
    | PatSeqTot (fi, pats) ->
        let patEnv, pats = s_pat_sequence patEnv pats in
        (patEnv, PatSeqTot (fi, pats))
    | PatSeqEdge (fi, l, x, r) ->
        let patEnv, l = s_pat_sequence patEnv l in
        let patEnv, x =
          match x with
          | NameWildcard ->
              (patEnv, NameWildcard)
          | NameStr (x, _) ->
              let patEnv, s = add_name (IdVar (sid_of_ustring x)) patEnv in
              (patEnv, NameStr (x, s))
        in
        let patEnv, r = s_pat_sequence patEnv r in
        (patEnv, PatSeqEdge (fi, l, x, r))
    | PatRecord (fi, pats) ->
        let patEnv = ref patEnv in
        let pats =
          Record.map
            (fun p ->
              let patEnv', p = sPat !patEnv p in
              patEnv := patEnv' ;
              p )
            pats
        in
        (!patEnv, PatRecord (fi, pats))
    | PatCon (fi, x, _, p) ->
        let s = findsym fi (IdCon (sid_of_ustring x)) env in
        let patEnv, p = sPat patEnv p in
        (patEnv, PatCon (fi, x, s, p))
    | PatInt _ as p ->
        (patEnv, p)
    | PatChar _ as p ->
        (patEnv, p)
    | PatBool _ as p ->
        (patEnv, p)
    | PatAnd (fi, l, r) ->
        let patEnv, l = sPat patEnv l in
        let patEnv, r = sPat patEnv r in
        (patEnv, PatAnd (fi, l, r))
    | PatOr (fi, l, r) ->
        let patEnv, l = sPat patEnv l in
        let patEnv, r = sPat patEnv r in
        (patEnv, PatOr (fi, l, r))
    | PatNot (fi, p) ->
        let _, p = sPat patEnv p in
        (* NOTE(vipa): new names in a not-pattern do not matter since they will
         * never bind (it should probably be an error to bind a name inside a
         * not-pattern, but we're not doing that kind of static checks yet.
         * Note that we still need to run symbolize though, constructors must
         * refer to the right symbol. *)
        (patEnv, PatNot (fi, p))
  in
  match t with
  | TmVar (fi, x, _, pes, frozen) ->
      TmVar (fi, x, findsym fi (IdVar (sid_of_ustring x)) env, pes, frozen)
  | TmLam (fi, x, _, pes, ty, t1) ->
      let s = Symb.gensym () in
      TmLam
        ( fi
        , x
        , s
        , pes
        , ty
        , symbolize (addsym (IdVar (sid_of_ustring x)) s env) t1 )
  | TmClos (_, _, _, _, _, _) ->
      failwith "Closures should not be available."
  | TmLet (fi, x, _, ty, t1, t2) ->
      let s = Symb.gensym () in
      TmLet
        ( fi
        , x
        , s
        , ty
        , symbolize env t1
        , symbolize (addsym (IdVar (sid_of_ustring x)) s env) t2 )
  | TmType (fi, x, params, ty, t1) ->
      (* TODO(dlunde,2020-11-23): Should type lets be recursive? Right now,
         they are not.*)
      TmType (fi, x, params, ty, symbolize env t1)
  | TmRecLets (fi, lst, tm) ->
      let env2 =
        List.fold_left
          (fun env (_, x, _, _, _) ->
            let s = Symb.gensym () in
            addsym (IdVar (sid_of_ustring x)) s env )
          env lst
      in
      TmRecLets
        ( fi
        , List.map
            (fun (fi, x, _, ty, t) ->
              ( fi
              , x
              , findsym fi (IdVar (sid_of_ustring x)) env2
              , ty
              , symbolize env2 t ) )
            lst
        , symbolize env2 tm )
  | TmApp (fi, t1, t2) ->
      TmApp (fi, symbolize env t1, symbolize env t2)
  | TmSeq (fi, tms) ->
      TmSeq (fi, Mseq.map (symbolize env) tms)
  | TmRecord (fi, r) ->
      TmRecord (fi, Record.map (symbolize env) r)
  | TmRecordUpdate (fi, t1, l, t2) ->
      TmRecordUpdate (fi, symbolize env t1, l, symbolize env t2)
  | TmConDef (fi, x, _, ty, t) ->
      let s = Symb.gensym () in
      TmConDef
        (fi, x, s, ty, symbolize (addsym (IdCon (sid_of_ustring x)) s env) t)
  | TmConApp (fi, x, _, t) ->
      TmConApp
        (fi, x, findsym fi (IdCon (sid_of_ustring x)) env, symbolize env t)
  | TmMatch (fi, t1, p, t2, t3) ->
      let matchedEnv, p = sPat empty_sym_env p in
      TmMatch
        ( fi
        , symbolize env t1
        , p
        , symbolize (merge_sym_envs_pick_left matchedEnv env) t2
        , symbolize env t3 )
  | TmUse (fi, l, t) ->
      TmUse (fi, l, symbolize env t)
  | TmUtest (fi, t1, t2, tusing, onfail, tnext) ->
      let sym_using = Option.map (fun t -> symbolize env t) tusing in
      let sym_onfail = Option.map (fun t -> symbolize env t) onfail in
      TmUtest
        ( fi
        , symbolize env t1
        , symbolize env t2
        , sym_using
        , sym_onfail
        , symbolize env tnext )
  | TmExt (fi, x, _, e, ty, t) ->
      let s = Symb.gensym () in
      TmExt
        (fi, x, s, e, ty, symbolize (addsym (IdVar (sid_of_ustring x)) s env) t)
  | TmDive (fi, l, t) ->
      TmDive (fi, l, symbolize env t)
  | TmPreRun (fi, l, t) ->
      TmPreRun (fi, l, symbolize env t)
  | TmBox (_, _) ->
      failwith "Box is a runtime value"
  | TmConst _ | TmNever _ | TmRef _ | TmTensor _ ->
      t

(* Same as symbolize, but records all toplevel definitions and returns them
   along with the symbolized term. *)
let rec symbolize_toplevel (env : sym_env) = function
  | TmLet (fi, x, _, ty, t1, t2) ->
      let s = Symb.gensym () in
      let new_env, new_t2 =
        symbolize_toplevel (addsym (IdVar (sid_of_ustring x)) s env) t2
      in
      (new_env, TmLet (fi, x, s, ty, symbolize env t1, new_t2))
  | TmRecLets (fi, lst, tm) ->
      let env2 =
        List.fold_left
          (fun env (_, x, _, _, _) ->
            let s = Symb.gensym () in
            addsym (IdVar (sid_of_ustring x)) s env )
          env lst
      in
      let new_env, new_tm = symbolize_toplevel env2 tm in
      ( new_env
      , TmRecLets
          ( fi
          , List.map
              (fun (fi, x, _, ty, t) ->
                ( fi
                , x
                , findsym fi (IdVar (sid_of_ustring x)) env2
                , ty
                , symbolize env2 t ) )
              lst
          , new_tm ) )
  | TmConDef (fi, x, _, ty, t) ->
      let s = Symb.gensym () in
      let new_env, new_t2 =
        symbolize_toplevel (addsym (IdCon (sid_of_ustring x)) s env) t
      in
      (new_env, TmConDef (fi, x, s, ty, new_t2))
  | TmExt (fi, x, _, e, ty, t) ->
      let s = Symb.gensym () in
      let new_env, new_t =
        symbolize_toplevel (addsym (IdVar (sid_of_ustring x)) s env) t
      in
      (new_env, TmExt (fi, x, s, e, ty, new_t))
  | ( TmVar _
    | TmLam _
    | TmApp _
    | TmType _
    | TmConst _
    | TmSeq _
    | TmRecord _
    | TmRecordUpdate _
    | TmConApp _
    | TmMatch _
    | TmUse _
    | TmUtest _
    | TmNever _
    | TmClos _
    | TmRef _
    | TmDive _
    | TmPreRun _
    | TmBox _
    | TmTensor _ ) as t ->
      (env, symbolize env t)
