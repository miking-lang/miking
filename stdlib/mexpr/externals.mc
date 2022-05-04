-- Various functions for manipulating externals in MExpr ASTs

include "ast.mc"
include "ast-builder.mc"
include "eq.mc"

include "map.mc"
include "name.mc"
include "sys.mc"

let _error = "Error in externals.mc: not an external in externalsMap"

lang Externals = ExtAst + VarAst

  -- Removes the symbols from all variables referring to externals. Assumes the
  -- program has been symbolized beforehand.
  sem unSymbolizeExternals : Expr -> Expr
  sem unSymbolizeExternals =
  | expr -> unSymbolizeExternalsH (setEmpty nameCmp) expr
  sem unSymbolizeExternalsH : Set Name -> Expr -> Expr
  sem unSymbolizeExternalsH env =
  | TmExt t ->
    let env = setInsert t.ident env in
    let inexpr = unSymbolizeExternalsH env t.inexpr in
    TmExt {{ t with ident = nameNoSym (nameGetStr t.ident) }
               with inexpr = inexpr }
  | TmVar t ->
    if setMem t.ident env then
      TmVar { t with ident = nameNoSym (nameGetStr t.ident) }
    else TmVar t
  | expr -> smap_Expr_Expr (unSymbolizeExternalsH env) expr

  -- Removes the given set of external definitions from the program.
  sem removeExternalDefs : Set String -> Expr -> Expr
  sem removeExternalDefs env =
  | TmExt t ->
    if setMem (nameGetStr t.ident) env then t.inexpr else
    let inexpr = removeExternalDefs env t.inexpr in
    TmExt { t with inexpr = inexpr }
  | expr -> smap_Expr_Expr (removeExternalDefs env) expr

  sem getExternalIds : Expr -> Set String
  sem getExternalIds =
  | expr -> getExternalIdsH (setEmpty cmpString) expr
  sem getExternalIdsH : Set String -> Expr -> Set String
  sem getExternalIdsH acc =
  | TmExt t -> getExternalIdsH (setInsert (nameGetStr t.ident) acc) t.inexpr
  | expr -> sfold_Expr_Expr getExternalIdsH acc expr

end

lang Test = Externals + MExprEq
end

-----------
-- TESTS --
-----------
-- TODO Write some tests
