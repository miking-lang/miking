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
lang MetaVarTypeAst = Ast
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
    match (deref l.contents, deref r.contents) with (Unbound l, Unbound r) then
      nameCmp l.ident r.ident
    else error "cmpTypeH reached non-unwrapped MetaVar!"
end

lang MetaVarTypePrettyPrint = PrettyPrint + MetaVarTypeAst + MonoKindAst
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
      (env, cons '_' idstr)
    case Link ty then
      getTypeStringCode indent env ty
    end
end

lang MetaVarTypeEq = Eq + MetaVarTypeAst
  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyMetaVar _ & rhs ->
    switch (unwrapType lhs, unwrapType rhs)
    case (TyMetaVar l, TyMetaVar r) then
      match (deref l.contents, deref r.contents) with (Unbound n1, Unbound n2) then
        optionBind
          (_eqCheck n1.ident n2.ident biEmpty free.freeTyFlex)
          (lam freeTyFlex.
            eqKind typeEnv {free with freeTyFlex = freeTyFlex} (n1.kind, n2.kind))
      else error "Unwrapped MetaVar was not Unbound!"
    case (! TyMetaVar _, ! TyMetaVar _) then
      eqTypeH typeEnv free lhs rhs
    case _ then None ()
    end
end

let newnmetavar =
  lam str. lam kind. lam level. lam info. use MetaVarTypeAst in TyMetaVar
   { info = info
   , contents = ref (Unbound
     { ident = nameSym str
     , level = level
     , kind = kind
     })
   }
let newmetavar = newnmetavar "a"

let newmonovar =
  use MonoKindAst in newmetavar (Mono ())
let newpolyvar =
  use PolyKindAst in newmetavar (Poly ())
let newrecvar =
  use RecordKindAst in lam fields.
    newmetavar (Record {fields = fields})

let newvar = newpolyvar

-- Substitutes type variables
lang VarTypeSubstitute = VarTypeAst + MetaVarTypeAst
  sem substituteVars : Info -> Map Name Type -> Type -> Type
  sem substituteVars info subst =
  | TyVar t & ty ->
    match mapLookup t.ident subst with Some tyvar then tyvar
    else ty
  | ty ->
    smap_Type_Type (substituteVars info subst) ty

  sem substituteMetaVars (subst : Map Name Type) =
  | TyMetaVar t & ty ->
    switch deref t.contents
    case Unbound r then
      match mapLookup r.ident subst with Some tyvar
      then tyvar
      else smap_Type_Type (substituteMetaVars subst) ty
    case Link to then
      substituteMetaVars subst to
    end
  | ty ->
    smap_Type_Type (substituteMetaVars subst) ty
end

lang AppTypeUtils = AppTypeAst + FunTypeAst
  -- Return the argument list in a type application
  sem getTypeArgs =
  | ty ->
    match getTypeArgsBase [] ty with (args, tycon) in
    (tycon, args)

  sem getTypeArgsBase (args : [Type]) =
  | TyApp t -> getTypeArgsBase (cons t.rhs args) t.lhs
  | ty -> rappAccumL_Type_Type getTypeArgsBase args ty

  -- Construct a type application from a type and an argument list
  sem mkTypeApp ty =
  | args ->
    foldl (lam ty1. lam ty2.
      TyApp {info = mergeInfo (infoTy ty1) (infoTy ty2), lhs = ty1, rhs = ty2})
          ty args

  -- Return the type (TyCon) which a constructor (TmConDef) belongs to.
  sem getConDefType: Type -> Type
  sem getConDefType =
  | ty ->
    match inspectType ty with TyArrow t then (getTypeArgs t.to).0
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

lang Test = MExprAst + MExprConstType + AppTypeUtils end

mexpr
use Test in

utest isHigherOrderFunType (tyConst (CInt { val = 1 })) with false in
utest isHigherOrderFunType (tyConst (CGet ())) with false in
utest isHigherOrderFunType (tyConst (CAddi ())) with false in
utest isHigherOrderFunType (tyConst (CMap ())) with true in
utest isHigherOrderFunType (tyConst (CIter ())) with true in

utest match getConDefType
              (tyall_ "a" (tyall_ "b"
                             (tyarrow_ (tyint_) (tyapp_ (tycon_ "Con") (tyvar_ "a")))))
      with TyCon t then t.ident else error "Impossible"
with nameNoSym "Con" in

()
