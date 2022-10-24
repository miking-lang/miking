include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/const-types.mc"

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

-- Unwraps type alias `ty` from `aliases`.
recursive let typeUnwrapAlias = use MExprAst in
  lam aliases : Map Name Type. lam ty : Type.
  match ty with TyCon {ident = ident} then
    match mapLookup ident aliases with Some ty then
      typeUnwrapAlias aliases ty
    else ty
  else ty
end

lang Test = MExprAst + MExprConstType end

mexpr
use Test in

utest isHigherOrderFunType (tyConst (CInt { val = 1 })) with false in
utest isHigherOrderFunType (tyConst (CGet ())) with false in
utest isHigherOrderFunType (tyConst (CAddi ())) with false in
utest isHigherOrderFunType (tyConst (CMap ())) with true in
utest isHigherOrderFunType (tyConst (CIter ())) with true in
()
