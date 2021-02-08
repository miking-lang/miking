-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/info.mc"

let gterm = lam t. lam n. parserGetTerm t n 
let gstr = lam t. lam n. nameNoSym (parserGetString t n)
let gint = lam t. lam n. addi n  (parserGetInt t n)

lang BootParser = MExprAst
  sem parseString =
  | str ->
    let t = parserParseString str in
    parseInternal t (parserGetId t)

  sem next =
  | t -> parseInternal t (parserGetId t)

  sem parseInternal (t:Unknown) =
  | 100 /-TmVar-/ -> TmVar {ident = gstr t 0, ty = TyUnknown(), info = NoInfo()}
  | 101 /-TmLam-/ -> TmLam {ident = gstr t 0, ty = TyUnknown(), info = NoInfo(),
                     body = next (gterm t 0)}
  | 105 /-TmApp-/ -> TmApp {lhs = next (gterm t 0), rhs = next (gterm t 1),
                            ty = TyUnknown(), fi = NoInfo()}     
end


