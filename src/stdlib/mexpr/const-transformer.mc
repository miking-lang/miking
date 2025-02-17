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

lang ConstTransformer = VarAst + LamAst + LetAst + RecLetsAst + MatchAst + ExtAst + NamedPat + ConstAst

  sem constTransform builtin =
  | t ->
      let f = lam acc. lam v.
        match v with (x, c) then mapInsert x (Some (uconst_ c)) acc else never in
      let env = foldl f (mapEmpty cmpString) builtin in
      let t2 = ctWorker env t in
      --dprint t2;
      t2

  sem ctWorker (env: Map String (Option Expr)) =
  | TmLet r ->
    let t1 = ctWorker env r.body in
    let env = mapInsert (nameGetStr r.ident) (None()) env in
    let t2 = ctWorker env r.inexpr in
    TmLet {r with body = t1, inexpr = t2}
  | TmLam r ->
    let t = ctWorker (mapInsert (nameGetStr r.ident) (None()) env) r.body in
    TmLam {r with body = t}
  | TmVar r ->
    let ident = nameGetStr r.ident in
    match mapFindOrElse (lam. Some (TmVar r)) ident env with Some tm
    then _constWithInfos r.info tm else TmVar r
  | TmRecLets r ->
    let fEnv = lam acc. lam b:RecLetBinding. mapInsert (nameGetStr b.ident) (None()) acc in
    let env = foldl fEnv env r.bindings in
    let bindings = map (lam b:RecLetBinding. {b with body = ctWorker env b.body}) r.bindings in
    TmRecLets {r with bindings = bindings, inexpr = ctWorker env r.inexpr}
  | TmMatch r ->
    let fEnv = lam acc. lam x. mapInsert x (None()) acc in
    let env2 = foldl fEnv env (ctGetPatVars [] r.pat) in
    TmMatch {r with target = ctWorker env r.target
                  , thn = ctWorker env2 r.thn
                  , els = ctWorker env r.els}
  | TmExt r ->
    let t = ctWorker (mapInsert (nameGetStr r.ident) (None()) env) r.inexpr in
    TmExt {r with inexpr = t}
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
