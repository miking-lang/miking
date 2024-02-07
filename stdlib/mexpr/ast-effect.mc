include "effect.mc"

-- MExpr
include "ast.mc"
include "eq.mc"
include "boot-parser.mc"

/-

  This file implements shallow mapping/folding with `Eff a` from
  `effect.mc` over `Expr`s.

  -/

lang AstEffect = Ast + Effect

  -- Perform a computation on the the immediate sub-expressions of an
  -- expression.  Note that this function is capable of emulating
  -- smapAccumL through use of the State effect.
  sem smapEff_Expr_Expr : all a. (Expr -> Eff Expr) -> Expr -> Eff Expr
  sem smapEff_Expr_Expr f =
  | e ->
    let getChildren : Expr -> [Expr] = sfold_Expr_Expr snoc [] in
    let updateChildren : Expr -> [Expr] -> Expr =
      lam e. lam children.
      let f =
        lam acc. lam e.
        match acc with [h] ++ t then (t, h) else ([], e)
      in
      (smapAccumL_Expr_Expr f children e).1
    in
    effMap (updateChildren e)
      (effMapM f (getChildren e))

end

lang TestLang = AstEffect + Writer + Failure + BootParser + MExprEq end

mexpr

use TestLang in

let parse =
  parseMExprString
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in

con CLog : Char -> Log in
let getLog = lam w. match w with CLog c in c in

con IFail : Int -> Failure in
let getFail = lam w. match w with IFail i in i in

let runTest
  : all a. Eff a -> (Either Int a, [Char])
  = lam x.
    runEff (handleWriter getLog (handleFail getFail x))
in

---------------------------------------
-- Test smapEff_Expr_Expr --
---------------------------------------

let prepTest = lam e1. lam e2. runTest (effMap (eqExpr e1) e2) in

-- Renames variables by concatenating its name to itself. variables with names
-- 'y' gives a warning 'b' and variables with names 'z' gives an error 1.
recursive let f : Expr -> Eff Expr
  = lam e.
    match e with TmVar r then
      let name = nameGetStr r.ident in
      let e =
        match name with "z" then fail (IFail 1)
        else
          return
            (TmVar { r with ident = nameSetStr r.ident (concat name name) })
      in
      match name with "y" then
        bind (tell (CLog 'b')) (lam. e)
      else e
    else
      smapEff_Expr_Expr f e
in


-- Test 1
let e = parse "
  let f = lam x. y x in
  (lam u. f u)
  "
in

let expected = parse "
  let f = lam x. yy xx in
  (lam u. ff uu)
  "
in

utest prepTest expected (f e) with (Right true, ['b']) in
---

-- Test 2
let e = parse "
  let f = lam x. y y x in
  (lam u. f)
  "
in

let expected = parse "
  let f = lam x. yy yy xx in
  (lam u. ff)
  "
in

utest prepTest expected (f e) with (Right true, ['b', 'b']) in
---

-- Test 3
let e = parse "
  let f = lam x. z x in
  (lam u. z)
  "
in

utest prepTest e (f e) with (Left 1, []) in
---

-- Test 4
let e = parse "
  let f = lam x. y z x in
  (lam u. z z z)
  "
in

utest prepTest e (f e) with (Left 1, ['b']) in
---

-- Test 5
let e = parse "
  let f = lam x. x x in
  (lam u. y x x)
  "
in

let expected = parse "
  let f = lam x. xx xx in
  (lam u. yy xx xx)
  "
in

utest prepTest expected (f e) with (Right true, ['b']) in
---

()
