-- Various functions for manipulating externals in MExpr ASTs

include "ast.mc"
include "boot-parser.mc"
include "ast-builder.mc"
include "eq.mc"

include "map.mc"
include "name.mc"
include "sys.mc"

let _error = "Error in externals.mc: not an external in externalsMap"

lang Externals = ExtAst + VarAst

  -- Removes the given set of external definitions from the program.
  sem removeExternalDefs : Set String -> Expr -> Expr
  sem removeExternalDefs env =
  | TmExt t ->
    let inexpr = removeExternalDefs env t.inexpr in
    if setMem (nameGetStr t.ident) env then inexpr
    else TmExt { t with inexpr = inexpr }
  | expr -> smap_Expr_Expr (removeExternalDefs env) expr

  sem getExternalIds : Expr -> Set String
  sem getExternalIds =
  | expr -> getExternalIdsH (setEmpty cmpString) expr
  sem getExternalIdsH : Set String -> Expr -> Set String
  sem getExternalIdsH acc =
  | TmExt t -> getExternalIdsH (setInsert (nameGetStr t.ident) acc) t.inexpr
  | expr -> sfold_Expr_Expr getExternalIdsH acc expr

end

lang Test = Externals + MExprEq + BootParser
end

-----------
-- TESTS --
-----------
mexpr
use Test in

let parse = parseMExprStringExn
  { defaultBootParserParseMExprStringArg with allowFree = true } in
let ast1 = parse "
  external a: Int -> Int in
  external b: Float -> Float in
  a 1; b 1.0
" in
let ast2 = parse "
  external b: Float -> Float in
  a 1; b 1.0
" in
let ast3 = parse "
  external a: Int -> Int in
  a 1; b 1.0
" in

utest removeExternalDefs (setOfSeq cmpString ["a"]) ast1
with ast2
using eqExpr in

utest removeExternalDefs (setOfSeq cmpString ["b"]) ast1
with ast3
using eqExpr in

utest getExternalIds ast1 with setOfSeq cmpString ["a", "b"]
using setEq in

utest getExternalIds ast2 with setOfSeq cmpString ["b"]
using setEq in

()
