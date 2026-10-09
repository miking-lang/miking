include "basic-types.mc"
include "name.mc"
include "info.mc"
include "seq.mc"
include "map.mc"
include "set.mc"
include "ast.mc"
include "ast-builder.mc"
include "eq.mc"

lang InstantiatedVarAst = Ast
  syn Expr +=
  | TmInstantiatedVar
    { ident : Name
    , ty : Type
    , info : Info
    , instantiated : Map Name Type
    }

  sem infoTm +=
  | TmInstantiatedVar r -> r.info

  sem tyTm +=
  | TmInstantiatedVar t -> t.ty

  sem withInfo info +=
  | TmInstantiatedVar t -> TmInstantiatedVar {t with info = info}

  sem withType (ty : Type) +=
  | TmInstantiatedVar t -> TmInstantiatedVar {t with ty = ty}

  sem smapAccumL_Expr_TypeLabel f acc +=
  | TmInstantiatedVar t ->
    match f acc t.ty with (acc, ty) in
    match mapMapAccum (lam acc. lam. lam ty. f acc ty) acc t.instantiated with (acc, instantiated) in
    (acc, TmInstantiatedVar {t with ty = ty, instantiated = instantiated})
end

lang FindInstantiatedVars = InstantiatedVarAst + VarAst + AllTypeAst + VarTypeAst
  sem findInstantiatedVarsDecl : Map Name Type -> Decl -> (Map Name Type, Decl)
  sem findInstantiatedVarsDecl polyTyEnv =
  | decl -> (polyTyEnv, smap_Decl_Expr (findInstantiatedVars polyTyEnv) decl)
  sem findInstantiatedVarsPat : Map Name Type -> Pat -> Map Name Type
  sem findInstantiatedVarsPat polyTyEnv =
  | pat -> sfold_Pat_Pat findInstantiatedVarsPat polyTyEnv pat

  sem findInstantiatedVars : Map Name Type -> Expr -> Expr
  sem findInstantiatedVars polyTyEnv =
  | tm -> smap_Expr_Expr (findInstantiatedVars polyTyEnv) tm
  | tm & TmVar (x & {frozen = false}) ->
    match mapLookup x.ident polyTyEnv with Some polyTy then
      match stripTyAll polyTy with (vars, stripped) in
      let vars = setOfSeq nameCmp (map (lam v. v.0) vars) in
      TmInstantiatedVar
      { ident = x.ident
      , ty = x.ty
      , info = x.info
      , instantiated = _matchTyVars vars (mapEmpty nameCmp) stripped x.ty
      }
    else tm

  sem _matchTyVars : Set Name -> Map Name Type -> Type -> Type -> Map Name Type
  sem _matchTyVars vars acc pat = | ty ->
    let pat = unwrapType pat in
    let ty = unwrapType ty in
    match pat with TyVar x then
      if setMem x.ident vars then mapInsert x.ident ty acc else acc
    else if eqi (constructorTag pat) (constructorTag ty) then
      let children = lam ty. sfold_Type_Type snoc [] ty in
      let patChildren = children pat in
      let tyChildren = children ty in
      if eqi (length patChildren) (length tyChildren)
      then foldl2 (_matchTyVars vars) acc patChildren tyChildren
      else acc
    else acc
end

lang DeclFindInstantiatedVars = FindInstantiatedVars + DeclAst
  sem findInstantiatedVars polyTyEnv +=
  | TmDecl x ->
    match findInstantiatedVarsDecl polyTyEnv x.decl with (polyTyEnv, decl) in
    TmDecl {x with decl = decl, inexpr = findInstantiatedVars polyTyEnv x.inexpr}
end

lang LetFindInstantiatedVars = FindInstantiatedVars + LetDeclAst
  sem findInstantiatedVarsDecl polyTyEnv +=
  | DeclLet x ->
    let body = findInstantiatedVars polyTyEnv x.body in
    ( match unwrapType x.tyBody with TyAll _
      then mapInsert x.ident x.tyBody polyTyEnv
      else polyTyEnv
    , DeclLet {x with body = body}
    )
end

lang RecLetsFindInstantiatedVars = FindInstantiatedVars + RecLetsDeclAst
  sem findInstantiatedVarsDecl polyTyEnv +=
  | DeclRecLets x ->
    let addBinding = lam env. lam b.
      match unwrapType b.tyBody with TyAll _
      then mapInsert b.ident b.tyBody env
      else env in
    let polyTyEnv = foldl addBinding polyTyEnv x.bindings in
    let bindings = map
      (lam b. {b with body = findInstantiatedVars polyTyEnv b.body})
      x.bindings in
    (polyTyEnv, DeclRecLets {x with bindings = bindings})
end

lang ExtFindInstantiatedVars = FindInstantiatedVars + ExtDeclAst
  sem findInstantiatedVarsDecl polyTyEnv +=
  | DeclExt x ->
    ( match unwrapType x.tyIdent with TyAll _
      then mapInsert x.ident x.tyIdent polyTyEnv
      else polyTyEnv
    , DeclExt x
    )
end

lang MatchFindInstantiatedVars = FindInstantiatedVars + MatchAst
  sem findInstantiatedVars polyTyEnv +=
  | TmMatch x ->
    TmMatch
    { x with target = findInstantiatedVars polyTyEnv x.target
    , thn = findInstantiatedVars (findInstantiatedVarsPat polyTyEnv x.pat) x.thn
    , els = findInstantiatedVars polyTyEnv x.els
    }
end

lang NamedFindInstantiatedVars = FindInstantiatedVars + NamedPat
  sem findInstantiatedVarsPat polyTyEnv +=
  | PatNamed (x & {ident = PName ident}) ->
    match unwrapType x.ty with TyAll _
    then mapInsert ident x.ty polyTyEnv
    else polyTyEnv
end

lang LamFindInstantiatedVars = FindInstantiatedVars + LamAst
  sem findInstantiatedVars polyTyEnv +=
  | TmLam x ->
    let polyTyEnv =
      match unwrapType x.tyParam with TyAll _
      then mapInsert x.ident x.tyParam polyTyEnv
      else polyTyEnv in
    TmLam {x with body = findInstantiatedVars polyTyEnv x.body}
end

lang OpaqueFindInstantiatedVars = FindInstantiatedVars + OpaqueAst
  sem findInstantiatedVars polyTyEnv +=
  | TmOpaque x -> TmOpaque {x with body = findInstantiatedVars polyTyEnv x.body}
end

lang MExprFindInstantiatedVars
  = FindInstantiatedVars + DeclFindInstantiatedVars + LetFindInstantiatedVars
  + RecLetsFindInstantiatedVars + ExtFindInstantiatedVars
  + MatchFindInstantiatedVars + NamedFindInstantiatedVars
  + LamFindInstantiatedVars + OpaqueFindInstantiatedVars
end

lang TestLang = MExprFindInstantiatedVars + MExprAst + MExprEq
end

mexpr

use TestLang in

let tvar_ = lam s. lam ty. lam i.
  TmVar {ident = nameNoSym s, ty = ty, info = infoVal "test" i 0 i 0, frozen = false} in

let collect : Expr -> [(Info, [(Name, Type)])] = lam tm.
  recursive let work = lam acc. lam tm.
    let acc = match tm with TmInstantiatedVar x
      then snoc acc (x.info, mapBindings x.instantiated)
      else acc in
    sfold_Expr_Expr work acc tm
  in work [] tm in

let eqBinding = lam a. lam b. if nameEq a.0 b.0 then eqType a.1 b.1 else false in
let eqInst = eqSeq (lam a. lam b.
  if eqi (infoCmp a.0 b.0) 0 then eqSeq eqBinding a.1 b.1 else false) in
let i = lam i. infoVal "test" i 0 i 0 in

let run = lam tm. collect (findInstantiatedVars (mapEmpty nameCmp) tm) in

let idTy = tyall_ "a" (tyarrow_ (tyvar_ "a") (tyvar_ "a")) in
let constTy = tyall_ "a" (tyall_ "b"
  (tyarrows_ [tyvar_ "a", tyvar_ "b", tyvar_ "a"])) in

utest run
  (bind_ (let_ "id" idTy (ulam_ "x" (var_ "x")))
    (app_ (tvar_ "id" (tyarrow_ tyint_ tyint_) 1) (int_ 1)))
with [(i 1, [(nameNoSym "a", tyint_)])] using eqInst in

utest run
  (bind_ (let_ "const" constTy (ulam_ "x" (ulam_ "y" (var_ "x"))))
    (tvar_ "const" (tyarrows_ [tyint_, tyfloat_, tyint_]) 1))
with [(i 1, [(nameNoSym "a", tyint_), (nameNoSym "b", tyfloat_)])] using eqInst in

utest run
  (bind_ (let_ "id" idTy (ulam_ "x" (var_ "x")))
    (bind_ (ulet_ "y" (tvar_ "id" (tyarrow_ tyint_ tyint_) 1))
      (tvar_ "id" (tyarrow_ tyfloat_ tyfloat_) 2)))
with [(i 1, [(nameNoSym "a", tyint_)]), (i 2, [(nameNoSym "a", tyfloat_)])] using eqInst in

utest run
  (bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
    (tvar_ "f" (tyarrow_ tyint_ tyint_) 1))
with [] using eqInst in

utest run
  (bind_
    (reclets_
      [ ("id", idTy, ulam_ "x" (var_ "x"))
      , ("f", tyunknown_, ulam_ "y" (app_ (tvar_ "id" (tyarrow_ tyint_ tyint_) 1) (var_ "y")))
      ])
    (app_ (tvar_ "f" (tyarrow_ tyint_ tyint_) 2)
      (app_ (tvar_ "id" (tyarrow_ tyint_ tyint_) 3) (int_ 1))))
with [(i 1, [(nameNoSym "a", tyint_)]), (i 3, [(nameNoSym "a", tyint_)])] using eqInst in

utest run
  (bind_
    (reclets_
      [ ("f", tyunknown_, ulam_ "y" (tvar_ "g" (tyarrow_ tyfloat_ tyfloat_) 1))
      , ("g", idTy, ulam_ "x" (var_ "x"))
      ])
    (tvar_ "g" (tyarrow_ tyint_ tyint_) 2))
with [(i 1, [(nameNoSym "a", tyfloat_)]), (i 2, [(nameNoSym "a", tyint_)])] using eqInst in

utest run
  (bind_ (ext_ "e" false idTy)
    (bind_ (ext_ "m" false (tyarrow_ tyint_ tyint_))
      (app_ (tvar_ "m" (tyarrow_ tyint_ tyint_) 1)
        (app_ (tvar_ "e" (tyarrow_ tyint_ tyint_) 2) (int_ 1)))))
with [(i 2, [(nameNoSym "a", tyint_)])] using eqInst in

let ppolyvar_ = lam s. lam ty.
  PatNamed {ident = PName (nameNoSym s), info = NoInfo (), ty = ty} in

utest run
  (match_ (ulam_ "x" (var_ "x")) (ppolyvar_ "f" idTy)
    (tvar_ "f" (tyarrow_ tyint_ tyint_) 1)
    (tvar_ "f" (tyarrow_ tyint_ tyint_) 2))
with [(i 1, [(nameNoSym "a", tyint_)])] using eqInst in

utest run
  (match_ (utuple_ [int_ 1, ulam_ "x" (var_ "x")])
    (ptuple_ [pvar_ "n", ppolyvar_ "f" idTy])
    (app_ (tvar_ "f" (tyarrow_ tyfloat_ tyfloat_) 1) (tvar_ "n" tyint_ 2))
    never_)
with [(i 1, [(nameNoSym "a", tyfloat_)])] using eqInst in

utest run
  (lam_ "f" idTy
    (utuple_
      [ tvar_ "f" (tyarrow_ tyint_ tyint_) 1
      , tvar_ "f" (tyarrow_ tyfloat_ tyfloat_) 2
      ]))
with [(i 1, [(nameNoSym "a", tyint_)]), (i 2, [(nameNoSym "a", tyfloat_)])] using eqInst in

utest run
  (bind_ (let_ "id" idTy (ulam_ "x" (var_ "x")))
    (app_ (lam_ "x" tyint_ (tvar_ "id" (tyarrow_ tyint_ tyint_) 1))
      (tvar_ "x" tyint_ 2)))
with [(i 1, [(nameNoSym "a", tyint_)])] using eqInst in

utest run
  (bind_ (let_ "id" idTy (ulam_ "x" (var_ "x")))
    (TmOpaque
      { body = app_ (tvar_ "id" (tyarrow_ tyint_ tyint_) 1) (int_ 1)
      , info = NoInfo ()
      , ty = tyint_
      }))
with [(i 1, [(nameNoSym "a", tyint_)])] using eqInst in

let tm = findInstantiatedVars
  (mapFromSeq nameCmp [(nameNoSym "id", idTy)])
  (withType (tyarrow_ tyint_ tyint_) (var_ "id")) in
utest sfold_Expr_TypeLabel (lam acc. lam ty. snoc acc ty) [] tm
with [tyarrow_ tyint_ tyint_, tyint_] using eqSeq eqType in
let tm = smap_Expr_TypeLabel (lam. tyfloat_) tm in
utest sfold_Expr_TypeLabel (lam acc. lam ty. snoc acc ty) [] tm
with [tyfloat_, tyfloat_] using eqSeq eqType in

()
