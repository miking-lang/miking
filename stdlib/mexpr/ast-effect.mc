include "effect.mc"

-- MExpr
include "ast.mc"
include "eq.mc"
include "boot-parser.mc"

/-

  This file implements shallow mapping/folding with `Eff a` from
  `effect.mc` over `Expr`, `Pat`, and `Type`.

  -/

lang AstEffect = Ast + Effect

  sem smapEffFromTraversal
    : all a. all b. (all acc. ((acc -> a -> (acc, a)) -> acc -> b -> (acc, b)))
    -> (a -> Eff a)
    -> b
    -> Eff b
  sem smapEffFromTraversal smapAccumL f =
  | e ->
    let effMapMChildren : b -> Eff [a] =
      lam x.
      (smapAccumL
         (lam acc. lam a. (effMap2 snoc acc (f a), a))
         (return []) x).0
    in
    let setChildren : b -> [a] -> b =
      lam x. lam children.
      let f =
        lam acc. lam e.
        match acc with [h] ++ t then (t, h) else ([], e)
      in
      (smapAccumL f children x).1
    in
    effMap (setChildren e) (effMapMChildren e)

  -- Perform a computation on the the immediate sub-expressions of an
  -- expression.  Note that this function is capable of emulating
  -- smapAccumL through use of the State effect.
  sem smapEff_Expr_Expr : all a. (Expr -> Eff Expr) -> Expr -> Eff Expr
  sem smapEff_Expr_Expr f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Expr_Expr" f e

  sem smapEff_Expr_Type : all a. (Type -> Eff Type) -> Expr -> Eff Expr
  sem smapEff_Expr_Type f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Expr_Type" f e

  sem smapEff_Expr_Pat : all a. (Pat -> Eff Pat) -> Expr -> Eff Expr
  sem smapEff_Expr_Pat f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Expr_Pat" f e

  sem smapEff_Expr_TypeLabel : all a. (Type -> Eff Type) -> Expr -> Eff Expr
  sem smapEff_Expr_TypeLabel f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Expr_TypeLabel" f e

  sem smapEff_Type_Type : all a. (Type -> Eff Type) -> Type -> Eff Type
  sem smapEff_Type_Type f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Type_Type" f e

  sem smapEff_Pat_Pat : all a. (Pat -> Eff Pat) -> Pat -> Eff Pat
  sem smapEff_Pat_Pat f =
  | e -> smapEffFromTraversal #frozen"smapAccumL_Pat_Pat" f e

end

lang TestLang = AstEffect + Writer + Failure + BootParser + MExprEq

  sem iFail : Int -> Failure
  sem cLog : Char -> Log

  -- Renames variables by concatenating its name to itself. variables with names
  -- 'y' gives a warning 'b' and variables with names 'z' gives an error 1.
  sem f : Expr -> Eff Expr
  sem f =
  | TmVar r ->
      let name = nameGetStr r.ident in
      match name with "z" then fail (iFail 1)
      else
        let newVar =
          TmVar { r with ident = nameSetStr r.ident (concat name name) }
        in
        match name with "y" then
          bind (tell (cLog 'b')) (lam. return newVar)
        else
          return newVar
  | e ->
    smapEff_Expr_Expr f e

end

lang TestLangImpl = TestLang
  syn Failure = | IFail Int
  syn Log = | CLog Char

  sem iFail = | i -> IFail i
  sem cLog = | c -> CLog c
end

mexpr

use TestLangImpl in

let parse =
  parseMExprStringExn
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in

let getLog = lam w. match w with CLog c in c in
let getFail = lam w. match w with IFail i in i in

let runTest
  : all a. Eff a -> (Either Int a, [Char])
  = lam x.
    runEff (handleWriter getLog (handleFail getFail x))
in

----------------------------
-- Test smapEff_Expr_Expr --
----------------------------

let prepTest = lam e1. lam e2. runTest (effMap (eqExpr e1) e2) in


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
