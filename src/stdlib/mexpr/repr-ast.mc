include "mexpr/ast.mc"

-- NOTE(vipa, 2023-06-12): We assume a certain collection size and
-- explicitly evaluate the cost expression
type OpCost = Float

-- A representation unification variable, for use in the UCT analysis
type ReprContent
type ReprVar = Ref ReprContent
con UninitRepr : () -> ReprContent
con BotRepr :
  { sym : Symbol
  , scope : Int
  } -> ReprContent
con LinkRepr :
  -- Invariant: link may only point to a repr with <= scope
  ReprVar -> ReprContent

recursive let botRepr : ReprVar -> ReprVar = lam r.
  switch deref r
  case BotRepr _ | UninitRepr _ then r
  case LinkRepr x then
    let bot = botRepr x in
    modref r (LinkRepr bot);
    bot
  end
end


lang TyWildAst = Ast
  syn Type =
  | TyWild { info : Info }

  sem tyWithInfo info =
  | TyWild x -> TyWild {x with info = info}

  sem infoTy =
  | TyWild x -> x.info
end

lang ReprTypeAst = Ast
 syn Type =
 | TyRepr { info : Info, arg : Type, repr : ReprVar }

 sem tyWithInfo info =
 | TyRepr x -> TyRepr {x with info = info}

 sem infoTy =
 | TyRepr x -> x.info

 sem smapAccumL_Type_Type f acc =
 | TyRepr x ->
   match f acc x.arg with (acc, arg) in
   (acc, TyRepr { x with arg = arg })
end

lang ReprSubstAst = Ast
  syn Type =
  | TySubst { info : Info, arg : Type, subst : Name }

  sem tyWithInfo info =
  | TySubst x -> TySubst {x with info = info}

  sem infoTy =
  | TySubst x -> x.info

  sem smapAccumL_Type_Type f acc =
  | TySubst x ->
   match f acc x.arg with (acc, arg) in
   (acc, TySubst { x with arg = arg })
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

type ImplId = Int
lang OpImplAst = Ast
  type TmOpImplRec = use Ast in
    { ident : Name
    , implId : ImplId
    , reprScope : Int
    , metaLevel : Int
    , selfCost : OpCost
    , body : Expr
    , specType : Type
    , delayedReprUnifications : [(ReprVar, ReprVar)]
    , inexpr : Expr
    , ty : Type
    , info : Info
    }
  syn Expr =
  | TmOpImpl TmOpImplRec

  sem tyTm =
  | TmOpImpl x -> x.ty

  sem withType ty =
  | TmOpImpl x -> TmOpImpl {x with ty = ty}

  sem infoTm =
  | TmOpImpl x -> x.info

  sem smapAccumL_Expr_Expr f acc =
  | TmOpImpl x ->
    match f acc x.body with (acc, body) in
    match f acc x.inexpr with (acc, inexpr) in
    (acc, TmOpImpl {x with body = body, inexpr = inexpr})

  sem smapAccumL_Expr_Type f acc =
  | TmOpImpl x ->
    match f acc x.specType with (acc, specType) in
    (acc, TmOpImpl {x with specType = specType})
end

lang OpVarAst = Ast
  type TmOpVarRec = {ident : Name, ty : Type, info : Info, frozen : Bool, scaling : OpCost}
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

lang RepTypesAst = ReprTypeAst + ReprSubstAst + OpDeclAst + OpImplAst + OpVarAst + ReprDeclAst + TyWildAst
end

type CollectedImpl = use Ast in
  { selfCost : OpCost
  , body : Expr
  , specType : Type
  , info : Info
  }

type ImplData = use Ast in
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
