-- NOTE(vipa, 2023-06-12): We assume a certain collection size and
-- explicitly evaluate the cost expression
type OpCost = Float

-- A representation unification variable, for use in the UCT analysis
type ReprContent
type Repr = Ref ReprContent
con UninitRepr : () -> ReprContent
con BotRepr :
  { sym : Symbol
  , scope : Int
  } -> ReprContent
con LinkRepr :
  -- Invariant: link may only point to a repr with <= scope
  { link : Repr
  , scope : Int
  } -> ReprContent

lang TyWildAst = Ast
  syn Type =
  | TyWild { info : Info }

  sem tyWithInfo info =
  | TyWild x -> TyWild {x with info = info}

  sem infoTy =
  | TyWild x -> x.info
end

lang CollTypeAst = Ast
  syn Type =
  | TyColl { info : Info, filter : Type, permutation : Type, element : Type, repr : Repr, explicitSubst : Option Name }

  sem tyWithInfo info =
  | TyColl x -> TyColl {x with info = info}

  sem infoTy =
  | TyColl x -> x.info

  sem smapAccumL_Type_Type f acc =
  | TyColl x ->
    match f acc x.filter with (acc, filter) in
    match f acc x.permutation with (acc, permutation) in
    match f acc x.element with (acc, element) in
    (acc, TyColl {x with filter = filter, permutation = permutation, element = element})
end

lang OpDeclAst = Ast + LetAst + NeverAst + UnknownTypeAst
  syn Expr =
  | TmOpDecl { info : Info, ident : Name, tyAnnot : Type, ty : Type, inexpr : Expr }

  sem tyTm =
  | TmOpDecl x -> x.ty

  sem withType ty =
  | TmOpDecl x -> TmOpDecl {x with ty = ty}

  sem withInfo info =
  | TmOpDecl x -> TmOpDecl {x with info = info}

  sem infoTm =
  | TmOpDecl x -> x.info

  sem smapAccumL_Expr_Expr f acc =
  | TmOpDecl x ->
    match f acc x.inexpr with (env, inexpr) in
    (env, TmOpDecl {x with inexpr = inexpr})

  sem smapAccumL_Expr_Type f acc =
  | TmOpDecl x ->
    match f acc x.tyAnnot with (env, tyAnnot) in
    (env, TmOpDecl {x with tyAnnot = tyAnnot})
end

lang OpImplAst = Ast
  type OpImplAlt =
    { selfCost : OpCost
    , body : Expr
    , specType : Type
    , delayedReprUnifications : [(Repr, Repr)]
    }
  syn Expr =
  | TmOpImpl {ident : Name, alternatives : [OpImplAlt], inexpr : Expr, ty : Type, reprScope : Int, info : Info}

  sem tyTm =
  | TmOpImpl x -> x.ty

  sem withType ty =
  | TmOpImpl x -> TmOpImpl {x with ty = ty}

  sem infoTm =
  | TmOpImpl x ->
    match x.alternatives with [alt] ++ _ in
    infoTm alt.body

  sem smapAccumL_Expr_Expr f acc =
  | TmOpImpl x ->
    let applyToAlt = lam acc. lam alt.
      match f acc alt.body with (acc, body) in
      (acc, {alt with body = body}) in
    match mapAccumL applyToAlt acc x.alternatives with (acc, alternatives) in
    match f acc x.inexpr with (acc, inexpr) in
    (acc, TmOpImpl {x with alternatives = alternatives, inexpr = inexpr})
end

lang OpVarAst = Ast
  type TmOpVarRec = {ident : Name, ty : Type, info : Info, frozen : Bool, reprs : [Repr], scaling : OpCost}
  syn Expr =
  | TmOpVar TmOpVarRec

  sem tyTm =
  | TmOpVar x -> x.ty

  sem withType ty =
  | TmOpVar x -> TmOpVar {x with ty = ty}

  sem infoTm =
  | TmOpVar x -> x.info

  sem withInfo info =
  | TmOpVar x -> TmOpVar {x with info = info}
end

lang ReprDeclAst = Ast
  syn Expr =
  | TmReprDecl
    { ident : Name
    , vars : [Name]
    , pat : Type
    , repr : Type
    , ty : Type
    , inexpr : Expr
    , info : Info
    }

  sem tyTm =
  | TmReprDecl x -> x.ty

  sem withType ty =
  | TmReprDecl x -> TmReprDecl {x with ty = ty}

  sem infoTm =
  | TmReprDecl x -> x.info

  sem withInfo info =
  | TmReprDecl x -> TmReprDecl {x with info = info}

  sem smapAccumL_Expr_Expr f acc =
  | TmReprDecl x ->
    match f acc x.inexpr with (acc, inexpr) in
    (acc, TmReprDecl {x with inexpr = inexpr})

  sem smapAccumL_Expr_Type f acc =
  | TmReprDecl x ->
    match f acc x.pat with (acc, pat) in
    match f acc x.repr with (acc, repr) in
    (acc, TmReprDecl {x with pat = pat, repr = repr})
end

type CollectedImpl =
  { selfCost : OpCost
  , body : Expr
  , specType : Type
  }

type ImplData =
  { impls : Map SID [CollectedImpl]
  , reprs : Map Name {vars : [Name], pat : Type, repr : Type}
  }

let emptyImplData : ImplData =
  { impls = mapEmpty cmpSID
  , reprs = mapEmpty nameCmp
  }
let mergeImplData : ImplData -> ImplData -> ImplData = lam a. lam b.
  { impls = mapUnionWith concat a.impls b.impls
  , reprs = mapUnionWith (lam. lam. never) a.reprs b.reprs
  }
