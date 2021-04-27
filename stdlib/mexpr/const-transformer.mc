-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Transforms an MExpr expression where variables referring to builtins
-- are replaced with the actual const terms

include "string.mc"
include "name.mc"
include "map.mc"
include "mexpr/builtin.mc"
include "mexpr/ast-builder.mc"
include "mexpr/ast.mc"

lang ConstTransformer = VarAst + LamAst + LetAst

  sem constTransform =
  | t ->
      let f = lam acc. lam v.
        match v with (x, c) then mapInsert x (Some (uconst_ c)) acc else never in
      let env = foldl f (mapEmpty cmpString) builtin in
      let t2 = ctWorker env t in
      --dprint t2;
      t2

  sem ctWorker (env: Map String Expr) =
  | TmLet r ->
    let env = mapInsert (nameGetStr r.ident) (None()) env in
    let t1 = ctWorker env r.body in
    let t2 = ctWorker env r.inexpr in
    TmLet {{r with body = t1} with inexpr = t2}
  | TmLam r ->
    let t = ctWorker (mapInsert (nameGetStr r.ident) (None()) env) r.body in
    TmLam {r with body = t}
  | TmVar r ->
    let ident = nameGetStr r.ident in
    match mapFindOrElse (lam. TmVar r) ident env with Some tm then tm else TmVar r
  -- TODO in this PR: | TmMatch
  -- TOCO in this PR: | TmRecLets
  | t -> smap_Expr_Expr (ctWorker env) t
end
