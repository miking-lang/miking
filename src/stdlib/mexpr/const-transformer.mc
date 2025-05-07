-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Transforms an MExpr expression where variables referring to builtins
-- are replaced with the actual const terms

include "string.mc"
include "name.mc"
include "map.mc"
include "ast-builder.mc"
include "ast.mc"
include "option.mc"

-- Add info for both term and type in const tms
let _constWithInfos: Info -> use Ast in Expr -> use Ast in Expr =
  use MExprAst in
  lam i: Info. lam tm: Expr.
    match tm with
      TmConst ({ info = NoInfo _, ty = TyUnknown ({ info = NoInfo _ } & ty)} & t)
    then
      TmConst {{t with info = i} with ty = TyUnknown {ty with info = i}}
    else tm

lang ConstTransformer = VarAst + LamAst + LetDeclAst + RecLetsDeclAst + MatchAst + ExtDeclAst + NamedPat + ConstAst

  sem constTransform builtin =
  | t ->
      let f = lam acc. lam v.
        match v with (x, c) then mapInsert x (Some (uconst_ c)) acc else never in
      let env = foldl f (mapEmpty cmpString) builtin in
      let t2 = ctWorker env t in
      --dprint t2;
      t2

  sem ctWorkerDecl (env: Map String (Option Expr)) =
  | DeclLet r ->
    let body = ctWorker env r.body in
    (mapInsert (nameGetStr r.ident) (None()) env, DeclLet {r with body = body})
  | DeclRecLets r ->
    let fEnv = lam acc. lam b:DeclLetRecord. mapInsert (nameGetStr b.ident) (None()) acc in
    let env = foldl fEnv env r.bindings in
    let bindings = map (lam b:DeclLetRecord. {b with body = ctWorker env b.body}) r.bindings in
    (env, DeclRecLets {r with bindings = bindings})
  | d & DeclExt r ->
    (mapInsert (nameGetStr r.ident) (None()) env, d)
  | d -> (env, smap_Decl_Expr (ctWorker env) d)

  sem ctWorker (env: Map String (Option Expr)) =
  | TmDecl x ->
    match ctWorkerDecl env x.decl with (env, decl) in
    let inexpr = ctWorker env x.inexpr in
    TmDecl {x with decl = decl, inexpr = inexpr}
  | TmLam r ->
    let t = ctWorker (mapInsert (nameGetStr r.ident) (None()) env) r.body in
    TmLam {r with body = t}
  | TmVar r ->
    let ident = nameGetStr r.ident in
    match mapFindOrElse (lam. Some (TmVar r)) ident env with Some tm
    then _constWithInfos r.info tm else TmVar r
  | TmMatch r ->
    let fEnv = lam acc. lam x. mapInsert x (None()) acc in
    let env2 = foldl fEnv env (ctGetPatVars [] r.pat) in
    TmMatch {r with target = ctWorker env r.target
                  , thn = ctWorker env2 r.thn
                  , els = ctWorker env r.els}
  | t -> smap_Expr_Expr (ctWorker env) t


  sem ctGetPatVars (acc: [String]) =
  | PatNamed r ->
      match r.ident with PName n then cons (nameGetStr n) acc else acc
  | t -> sfold_Pat_Pat ctGetPatVars acc t

  -- Replaces all constants in an expression with variables where the name of
  -- the variable is defined by `env`. Only constant that are
  -- present in `env` are replaced.
  sem constTransformConstsToVars : Map Const Name -> Expr -> Expr
  sem constTransformConstsToVars env =
  | t & TmConst r ->
    optionMapOr t
      (lam ident. TmVar {
        ident = ident,
        ty = r.ty,
        info = r.info,
        frozen = false
      })
      (mapLookup r.val env)
  | t -> smap_Expr_Expr (constTransformConstsToVars env) t
end
