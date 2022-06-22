include "map.mc"
include "mexpr/ast.mc"

-- Returns the arity of a function type
recursive let arityFunType = use MExprAst in lam ty.
  match ty with TyArrow t then addi 1 (arityFunType t.to) else 0
end

-- Unwraps type alias `ty` from `aliases`.
recursive let typeUnwrapAlias = use MExprAst in
  lam aliases : Map Name Type. lam ty : Type.
  match ty with TyCon {ident = ident} then
    match mapLookup ident aliases with Some ty then
      typeUnwrapAlias aliases ty
    else ty
  else ty
end
