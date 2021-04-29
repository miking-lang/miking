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

lang ConstTransformer = VarAst + LamAst + LetAst + RecLetsAst + MatchAst + NamedPat

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
    match mapFindOrElse (lam. Some (TmVar r)) ident env with Some tm then tm else TmVar r
  | TmRecLets r ->
     let fEnv = lam acc. lam b:RecLetBinding. mapInsert (nameGetStr b.ident) (None()) acc in
     let env = foldl fEnv env r.bindings in
     let bindings = map (lam b:RecLetBinding. {b with body = ctWorker env b.body}) r.bindings in
     TmRecLets {{r with bindings = bindings}
                   with inexpr = ctWorker env r.inexpr}
  | TmMatch r ->
     let fEnv = lam acc. lam x. mapInsert x (None()) acc in
     let env2 = foldl fEnv env (ctGetPatVars [] r.pat) in
     TmMatch {{{r with target = ctWorker env r.target}
                  with thn = ctWorker env2 r.thn}
                  with els = ctWorker env r.els}
  | t -> smap_Expr_Expr (ctWorker env) t


  sem ctGetPatVars (acc: [String]) =
  | PatNamed r ->
      match r.ident with PName n then cons (nameGetStr n) acc else acc
  | t -> sfold_Pat_Pat ctGetPatVars acc t


end
