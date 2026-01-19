-- This file provides a simple implementation of higher-order abstract
-- syntax, i.e., where we represent lambdas with actual functions. The
-- implementation in this file is intended to simplify the
-- construction of clean ASTs, rather than to truly work with HOAS
-- throughout, hence the names `TempLam` and `TempFix`.
--
-- Assumptions:
-- * Functions in `TempLam` and `TempFix` should be _linear_, i.e.,
--   applying the function to an expression will not duplicate that
--   expression, nor any part of it.
-- * Functions in `TempLam` and `TempFix` should behave properly
--   according to parametric polymorphism, i.e., they should produce a
--   semantically equivalent expression no matter their
--   argument. However, they are allowed to perform some reductions
--   before returning an expressions, e.g., pattern matching on an
--   input record by taking apart a `TmRecord` rather than producing a
--   `TmMatch`.
--
-- There is also an extensible `_app` function (via `_app`), which
-- semantically functions like `app_` from `ast-builder.mc`, but may
-- reduce the application if posible.

include "mexpr/ast.mc"
include "mexpr/pprint.mc"

lang TempLamAst = Ast + PrettyPrint + OpaqueAst
  type TempFixRec =
    { canMakeProgress : Expr -> Bool
    , f : (Expr -> Expr) -> Expr -> Expr
    , info : Info
    , ty : Type
    }
  type TempLamRec =
    { f : Expr -> Expr
    , info : Info
    , ty : Type
    }
  syn Expr =
  | TempLam TempLamRec
  | TempFix TempFixRec

  sem tempLam_ : (Expr -> Expr) -> Expr
  sem tempLam_ = | f ->
    TempLam {f = f, info = NoInfo (), ty = TyUnknown {info = NoInfo ()}}

  sem isAtomic =
  | TempLam _ -> false
  | TempFix _ -> false

  sem pprintCode indent env =
  | TempLam f ->
    let x = nameSym "x" in
    match pprintVarName env x with (env, str) in
    match pprintCode (pprintIncr indent) env (f.f (nvar_ x)) with (env, body) in
    ( env
    , join ["/-temp-/lam ", str, ".", pprintNewline (pprintIncr indent), body]
    )
  | TempFix f ->
    let x = nameSym "x" in
    let fName = nameSym "f" in
    match pprintVarName env fName with (env, fStr) in
    match pprintVarName env x with (env, xStr) in
    match pprintCode (pprintIncr indent) env (f.f (app_ (nvar_ fName)) (nvar_ x)) with (env, body) in
    ( env
    , join ["/-temp-/recursive let ", fStr, " = lam ", xStr, ".", pprintNewline (pprintIncr indent), body, " in ", fStr]
    )

  sem stripTempLam : Expr -> Expr
  sem stripTempLam = | tm -> _stripTempLam ([], tm)

  sem _defaultStripFix : [Expr] -> TempFixRec -> Expr
  sem _defaultStripFix args = | x ->
    let n = nameSym "n" in
    let f = nameSym "f" in
    TmDecl
    { decl = DeclRecLets
      { bindings =
        [ { ident = f
          , tyAnnot = tyunknown_
          , tyBody = tyunknown_
          , body = nulam_ n (stripTempLam (x.f (app_ (nvar_ f)) (nvar_ n)))
          , info = x.info
          }
        ]
      , info = x.info
      }
    , inexpr = appSeq_ (nvar_ f) args
    , info = x.info
    , ty = x.ty
    }

  sem _stripTempLam : ([Expr], Expr) -> Expr
  sem _stripTempLam =
  | ([arg] ++ args, TempLam f) ->
    _stripTempLam (args, f.f arg)
  | ([], TempLam f) ->
    let n = nameSym "x" in
    TmLam
    { ident = n
    , tyAnnot = tyunknown_
    , tyParam = tyunknown_
    , body = stripTempLam (f.f (nvar_ n))
    , ty = tyunknown_
    , info = NoInfo ()
    }
  | (allArgs & [arg] ++ args, f & TempFix x) ->
    if x.canMakeProgress arg
    then _stripTempLam (args, x.f (_app f) arg)
    else _defaultStripFix allArgs x
  | ([], TempFix x) ->
    _defaultStripFix [] x
  | (args, TmApp x) ->
    _stripTempLam (cons (stripTempLam x.rhs) args, x.lhs)
  | (args, TmDecl x) ->
    let decl = smap_Decl_Expr stripTempLam x.decl in
    let inexpr = _stripTempLam (args, x.inexpr) in
    TmDecl {x with decl = decl, inexpr = inexpr}
  | (args, tm & TmOpaque _) -> appSeq_ tm args
  | (args, tm) -> appSeq_ (smap_Expr_Expr stripTempLam tm) args

  sem maybeEtaExpand : Expr -> {ident : Name, tyAnnot : Type, tyParam : Type, body : Expr, ty : Type, info : Info}
  sem maybeEtaExpand =
  | TmLam f -> f
  | tm ->
    let n = nameSym "x" in
    { ident = n
    , tyAnnot = tyunknown_
    , tyParam = tyunknown_
    , body = _app tm (nvar_ n)
    , ty = tyTm tm
    , info = infoTm tm
    }

  sem tyTm =
  | TempLam _ -> TyUnknown {info = NoInfo ()}
  | TempFix x -> x.ty

  sem withType ty =
  | tm & TempLam _ -> tm
  | TempFix x -> TempFix {x with ty = ty}

  sem infoTm =
  | TempLam x -> x.info
  | TempFix x -> x.info

  sem withInfo info =
  | TempLam x -> TempLam {x with info = info}
  | TempFix x -> TempFix {x with info = info}

  sem _app : Expr -> Expr -> Expr
  sem _app l = | r -> _app_ (l, r)

  sem _app_ : (Expr, Expr) -> Expr
  sem _app_ =
  -- we have a simple function, just apply it
  | (TempLam f, x) -> f.f x
  -- we have a simple recursive function, just apply it
  | (f & TempFix f2, x) ->
    if f2.canMakeProgress x
    then f2.f (_app f) x
    else app_ f x
  -- mapSeq id = id
  | (f & TmConst {val = CMap _}, x & TempLam f2) ->
    if isIdentity f2.f then tempLam_ (lam x. x) else app_ f x
  -- mapSeq f [x, ...] = [f x, ...]
  | ( TmApp
      { lhs = TmConst {val = CMap _}
      , rhs = f
      }
    , TmSeq x
    ) ->
    TmSeq {x with tms = map (_app f) x.tms}
  | (TmDecl f, x) ->
    TmDecl {f with inexpr = _app f.inexpr x}
  -- base case, just make the TmApp
  | (f, x) -> app_ f x

  sem isIdentity : (Expr -> Expr) -> Bool
  sem isIdentity = | f ->
    let n = nameSym "x" in
    match f (nvar_ n) with TmVar {ident = ident}
    then nameEq ident n
    else false
end
