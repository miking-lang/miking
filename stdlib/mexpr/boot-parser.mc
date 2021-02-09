-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/info.mc"

let gterm = lam t. lam n. bootParserGetTerm t n 
let gstr = lam t. lam n. nameNoSym (bootParserGetString t n)
let gint = lam t. lam n. addi n  (bootParserGetInt t n)

lang BootParser = MExprAst
  sem parseMExprString =
  | str ->
    let t = bootParserParseMExprString str in
    parseInternal t (bootParserGetId t)

  sem next =
  | t -> parseInternal t (bootParserGetId t)

  sem parseInternal (t:Unknown) =
  | 100 /-TmVar-/ -> TmVar {ident = gstr t 0, ty = TyUnknown(), info = NoInfo()}
  | 101 /-TmLam-/ -> TmLam {ident = gstr t 0, ty = TyUnknown(), info = NoInfo(),
                     body = next (gterm t 0)}
  | 105 /-TmApp-/ -> TmApp {lhs = next (gterm t 0), rhs = next (gterm t 1),
                            ty = TyUnknown(), fi = NoInfo()}     
end


mexpr
use BootParser in

utest parseMExprString "hi"  with 1 in



()
