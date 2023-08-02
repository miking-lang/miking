include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/const-types.mc"

-- Substitutes type variables
lang VarTypeSubstitute = VarTypeAst
  sem substituteVars (subst : Map Name Type) =
  | TyVar t & ty ->
    match mapLookup t.ident subst with Some tyvar then tyvar
    else ty
  | ty ->
    smap_Type_Type (substituteVars subst) ty
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
lang GetConDefType = MExprAst
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

lang Test = MExprAst + MExprConstType + GetConDefType end

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
