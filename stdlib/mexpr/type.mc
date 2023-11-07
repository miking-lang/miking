include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/const-types.mc"
include "mexpr/eq.mc"
include "mexpr/pprint.mc"

---------------------------
-- UNIFICATION VARIABLES --
---------------------------

-- A level denotes the level in the AST that a type was introduced at
type Level = Int

-- Unification meta variables.  These variables represent some
-- specific but as-of-yet undetermined type.
lang MetaVarTypeAst = KindAst + Ast
  type MetaVarRec = {ident  : Name,
                     level  : Level,
    -- The level indicates at what depth of let-binding the variable
    -- was introduced, which is used to determine which variables can
    -- be generalized and to check that variables stay in their scope.
                     kind   : Kind}

  syn MetaVar =
  | Unbound MetaVarRec
  | Link Type

  syn Type =
  -- Meta type variable
  | TyMetaVar {info     : Info,
               contents : Ref MetaVar}

  sem tyWithInfo (info : Info) =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound _ then
      TyMetaVar {t with info = info}
    case Link ty then
      tyWithInfo info ty
    end

  sem infoTy =
  | TyMetaVar {info = info} -> info

  sem smapAccumL_Type_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound r then
      match smapAccumL_Kind_Type f acc r.kind with (acc, kind) in
      modref t.contents (Unbound {r with kind = kind});
      (acc, TyMetaVar t)
    case Link ty then
      f acc ty
    end

  sem rappAccumL_Type_Type (f : acc -> Type -> (acc, Type)) (acc : acc) =
  | TyMetaVar t & ty ->
    recursive let work = lam ty.
      match ty with TyMetaVar x then
        switch deref x.contents
        case Link l then
          let new = work l in
          modref x.contents (Link new);
          new
        case Unbound _ then
          ty
        end
      else ty in
    switch work ty
    case TyMetaVar _ & ty1 then (acc, ty1)
    case ty1 then f acc ty1
    end
end

lang MetaVarTypeCmp = Cmp + MetaVarTypeAst
  sem cmpTypeH =
  | (TyMetaVar l, TyMetaVar r) ->
    -- NOTE(vipa, 2023-04-19): Any non-link TyMetaVar should have been
    -- unwrapped already, thus we can assume `Unbound` here.
    match (deref l.contents, deref r.contents) with (Unbound l, Unbound r) in
    nameCmp l.ident r.ident
end

lang MetaVarTypePrettyPrint = IdentifierPrettyPrint + KindPrettyPrint + MetaVarTypeAst
  sem typePrecedence =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound _ then
      100000
    case Link ty then
      typePrecedence ty
    end
  sem getTypeStringCode (indent : Int) (env : PprintEnv) =
  | TyMetaVar t ->
    switch deref t.contents
    case Unbound t then
      match pprintVarName env t.ident with (env, idstr) in
      match getKindStringCode indent env idstr t.kind with (env, str) in
      let monoPrefix =
        match t.kind with Mono _ then "_" else "" in
      (env, concat monoPrefix str)
    case Link ty then
      getTypeStringCode indent env ty
    end
end

lang MetaVarTypeEq = KindEq + MetaVarTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyMetaVar _ & rhs ->
    switch (unwrapType lhs, unwrapType rhs)
    case (TyMetaVar l, TyMetaVar r) then
      match (deref l.contents, deref r.contents) with (Unbound n1, Unbound n2) in
      optionBind
        (_eqCheck n1.ident n2.ident biEmpty free.freeTyFlex)
        (lam freeTyFlex.
          eqKind typeEnv {free with freeTyFlex = freeTyFlex} (n1.kind, n2.kind))
    case (! TyMetaVar _, ! TyMetaVar _) then
      eqTypeH typeEnv free lhs rhs
    case _ then None ()
    end
end

let newmetavar =
  lam kind. lam level. lam info. use MetaVarTypeAst in
  TyMetaVar {info = info,
             contents = ref (Unbound {ident = nameSym "a",
                                      level = level,
                                      kind  = kind})}

let newmonovar = use KindAst in
  newmetavar (Mono ())
let newpolyvar = use KindAst in
  newmetavar (Poly ())
let newrowvar = use KindAst in
  lam fields. newmetavar (Row {fields = fields})

let newvar = newpolyvar

-- Substitutes type variables
lang VarTypeSubstitute = VarTypeAst + MetaVarTypeAst
  sem substituteVars (subst : Map Name Type) =
  | TyVar t & ty ->
    match mapLookup t.ident subst with Some tyvar then tyvar
    else ty
  | ty ->
    smap_Type_Type (substituteVars subst) ty

  sem substituteMetaVars (subst : Map Name Type) =
  | TyMetaVar t & ty ->
    switch deref t.contents
    case Unbound r then
      match mapLookup r.ident subst with Some tyvar then tyvar else ty
    case Link to then
      substituteMetaVars subst to
    end
  | ty ->
    smap_Type_Type (substituteMetaVars subst) ty
end

-- Returns the argument list in a type application
lang AppTypeGetArgs = AppTypeAst
  sem getTypeArgs =
  | TyApp t ->
    match getTypeArgs t.lhs with (tycon, args) in
    (tycon, snoc args t.rhs)
  | ty ->
    (ty, [])
end

-- Return the type (TyCon) which a constructor (TmConDef) belongs to.
lang ConDefTypeUtils = MExprAst
  sem getConDefType: Type -> Type
  sem getConDefType =
  | ty ->
    let ty = (stripTyAll ty).1 in
    match ty with TyArrow t then
      recursive let getTyLhs = lam ty.
        match ty with TyApp t then getTyLhs t.lhs
        else ty
      in getTyLhs t.to
    else error "Invalid type in getConDefType"
end

-- Returns the arity of a function type
recursive let arityFunType = use MExprAst in lam ty.
  match ty with TyArrow t then addi 1 (arityFunType t.to) else 0
end

let isHigherOrderFunType = use MExprAst in lam ty.
  recursive let rec = lam under: Bool. lam acc. lam ty.
    match ty with TyArrow { from = from, to = to } then
      if under then true else
        let acc = rec true acc from in
        if acc then acc else rec false acc to
    else
      sfold_Type_Type (rec under) acc ty
  in
  rec false false ty

lang Test = MExprAst + MExprConstType + ConDefTypeUtils end

mexpr
use Test in

utest isHigherOrderFunType (tyConst (CInt { val = 1 })) with false in
utest isHigherOrderFunType (tyConst (CGet ())) with false in
utest isHigherOrderFunType (tyConst (CAddi ())) with false in
utest isHigherOrderFunType (tyConst (CMap ())) with true in
utest isHigherOrderFunType (tyConst (CIter ())) with true in

utest match getConDefType (tyall_ "a" (tyall_ "b"
        (tyarrow_ (tyint_) (tyapp_ (tycon_ "Con") (tyvar_ "a")))))
      with TyCon t then t.ident else error "Impossible"
with nameNoSym "Con" in

()
