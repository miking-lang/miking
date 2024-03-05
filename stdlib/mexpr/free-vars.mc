-- This file contains language fragments and functions related to free
-- variables.

include "set.mc"
include "name.mc"

include "mexpr/ast.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"

lang FreeVars = Ast
  -- Returns the set of free variables for a given expression. Assumes that the
  -- expression is symbolized.
  sem freeVars : Expr -> Set Name
  sem freeVars =| t -> freeVarsExpr (setEmpty nameCmp) t

  sem freeVarsExpr : Set Name -> Expr -> Set Name
  sem freeVarsExpr acc =
  | t -> sfold_Expr_Expr freeVarsExpr acc t
end

lang VarFreeVars = FreeVars + VarAst
  sem freeVarsExpr acc =
  | TmVar r -> setInsert r.ident acc
end

lang LamFreeVars = FreeVars + LamAst
  sem freeVarsExpr acc =
  | TmLam r ->
    setRemove r.ident (freeVarsExpr acc r.body)
end

lang LetFreeVars = FreeVars + LetAst
  sem freeVarsExpr acc =
  | TmLet r ->
    setRemove r.ident (freeVarsExpr (freeVarsExpr acc r.body) r.inexpr)
end

lang RecLetsFreeVars = FreeVars + RecLetsAst
  sem freeVarsExpr acc =
  | TmRecLets r ->
    let acc = foldl (lam acc. lam b.
      freeVarsExpr acc b.body) (freeVarsExpr acc r.inexpr) r.bindings in
    foldl (lam acc. lam b. setRemove b.ident acc) acc r.bindings
end

lang MatchFreeVars = FreeVars + MatchAst + NamedPat + SeqEdgePat
  sem freeVarsExpr acc =
  | TmMatch r ->
    freeVarsExpr
      (freeVarsExpr
         (bindVarsPat
            (freeVarsExpr acc r.thn)
            r.pat)
         r.els)
      r.target

  sem bindVarsPat : Set Name -> Pat -> Set Name
  sem bindVarsPat acc =
  | PatNamed {ident = PName ident} -> setRemove ident acc
  | pat & (PatSeqEdge {middle = PName ident}) ->
    let acc = setRemove ident acc in
    sfold_Pat_Pat bindVarsPat acc pat
  | pat -> sfold_Pat_Pat bindVarsPat acc pat
end

lang MExprFreeVars =
  VarFreeVars + LamFreeVars + LetFreeVars + RecLetsFreeVars + MatchFreeVars
end

lang TestLang = MExprFreeVars + MExprSym + BootParser end

mexpr

use TestLang in

let parseProgram : String -> Expr =
  lam str.
    let parseArgs =
      {defaultBootParserParseMExprStringArg with allowFree = true}
    in
    let ast = parseMExprStringExn parseArgs str in
    symbolizeExpr {symEnvEmpty with allowFree = true} ast
in

-------------------
-- Test freeVars --
-------------------

let testFreeVars = lam prog.
  let fv = freeVars prog in
  sort cmpString (map nameGetStr (setToSeq fv))
in

let prog = parseProgram "
  lam x. x x y y y
  "
in

utest testFreeVars prog with ["y"] in

let prog = parseProgram "
  let x = z in x x y y y
  "
in

utest testFreeVars prog with ["y", "z"] in

let prog = parseProgram "
  recursive let f = lam x. w f (f x) in
  recursive let g = lam y. z f (g y) in
  w z (f (g u))
  "
in

utest testFreeVars prog with ["u", "w", "z"] in

let prog = parseProgram "
  match u with (x, (y, z)) in
  x y y z z z u w w
  "
in

utest testFreeVars prog with ["u", "w"] in

let prog = parseProgram "
  match t with [x] ++ xs in
    x xs t r
  "
in

utest testFreeVars prog with ["r", "t"] in

let prog = parseProgram "
  match t with [first] ++ mid ++ [last] in
    first mid f r last t
  "
in

utest testFreeVars prog with ["f", "r", "t"] in

()
