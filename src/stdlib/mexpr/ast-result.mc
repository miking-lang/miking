include "result.mc"

-- MExpr
include "ast.mc"
include "eq.mc"
include "boot-parser.mc"

/-

  This file implements shallow mapping/folding with `Result w e a` from
  `result.mc` over `Expr`s, while propagating as many errors and warnings as
  possible.

  -/

lang AstResult = Ast

  -- Perform a computation on the immediate sub-expressions of an expression,
  -- while simultaneously threading an accumulator. Produces a non-error only if
  -- all individual computations produce a non-error. Preserves all errors and
  -- warnings
  sem smapAccumL_ResultM_Expr_Expr
    : all w. all e. all a.
      (a -> Expr -> (a, Result w e Expr)) -> a -> Expr -> (a, Result w e Expr)
  sem smapAccumL_ResultM_Expr_Expr f acc =
  | e ->
    let withAnnot = result.withAnnotations in
    let consume = result.consume in
    let ok = result.ok in
    let inner = lam acc. lam e.
      match acc with (annot, a) in
      match f a e with (a, res) in
      let e = match consume res with (_, Right e) then e else e in
      ((withAnnot res annot, a), e)
    in
    match smapAccumL_Expr_Expr inner (ok (), acc) e
      with ((annot, acc), e)
    in
    (acc, withAnnot annot (ok e))

  -- Perform a computation on the the immediate sub-expressions of an
  -- expression. Produces a non-error only if all individual computations
  -- produce a non-error. Preserves all errors and warnings.
  sem smap_ResultM_Expr_Expr
    : all w. all e. (Expr -> Result w e Expr) -> Expr -> Result w e Expr
  sem smap_ResultM_Expr_Expr f =| e ->
    (smapAccumL_ResultM_Expr_Expr (lam. lam e. ((), f e)) () e).1
end

lang TestLang = AstResult + BootParser + MExprEq end

mexpr

use TestLang in

let parse =
  parseMExprStringExn
    { _defaultBootParserParseMExprStringArg () with allowFree = true }
in

-- The order of warnings and errors is not significant, thus we call
-- this function on a result to be compared in a utest to get a stable
-- ordering.
let prepTest
  : all a. Result Char Int a -> ([Char], Either [Int] a)
  = lam x.
    match _consume x with (w, r) in
    (sort cmpChar w, eitherBiMap (sort subi) identity r)
in

---------------------------------------
-- Test smapAccumL_ResultM_Expr_Expr --
---------------------------------------

let _prepTest = lam e. lam p.
  (sort cmpString p.0, prepTest (result.map (eqExpr e) p.1))
in

-- Accumulates variable names and renames variables by concatenating its name to
-- itself. Variables with names 'y' gives a warning 'b' and variables with names
-- 'z' gives an error 1.
recursive let f : [String] -> Expr -> ([String], (Result Char Int Expr))
  = lam acc. lam e.
    let ann = result.withAnnotations in
    switch e
    case TmVar r then
      let name = nameGetStr r.ident in
      let acc = cons name acc in
      let e =
        match name with "z" then result.err 1
        else
          result.ok
            (TmVar { r with ident = nameSetStr r.ident (concat name name) })
      in
      switch name
      case "y" then (acc, ann (result.warn 'b') e)
      case _ then (acc, e)
      end
    case e then smapAccumL_ResultM_Expr_Expr f acc e
    end
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

utest _prepTest expected (f [] e) with
  (["f", "u", "x", "y"], (['b'], Right true))
in
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

utest _prepTest expected (f [] e) with
  (["f", "x", "y", "y"], (['b', 'b'], Right true))
in
---

-- Test 3
let e = parse "
  let f = lam x. z x in
  (lam u. z)
  "
in

utest _prepTest e (f [] e) with
  (["x", "z", "z"], ([], Left [1, 1]))
in
---

-- Test 4
let e = parse "
  let f = lam x. z x in
  (lam u. y z z z)
  "
in

utest _prepTest e (f [] e) with
  (["x","y","z","z","z","z"], (['b'], Left [1,1,1,1]))
in
---

---------------------------------------
-- Test smap_ResultM_Expr_Expr --
---------------------------------------

let _prepTest = lam e1. lam e2. prepTest (result.map (eqExpr e1) e2) in

-- Renames variables by concatenating its name to itself. variables with names
-- 'y' gives a warning 'b' and variables with names 'z' gives an error 1.
recursive let f : Expr -> (Result Char Int Expr)
  = lam e.
    let ann = result.withAnnotations in
    switch e
    case TmVar r then
      let name = nameGetStr r.ident in
      let e =
        match name with "z" then result.err 1
        else
          result.ok
            (TmVar { r with ident = nameSetStr r.ident (concat name name) })
      in
      switch name
      case "y" then ann (result.warn 'b') e
      case _ then e
      end
    case e then smap_ResultM_Expr_Expr f e
    end
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

utest _prepTest expected (f e) with (['b'], Right true) in
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

utest _prepTest expected (f e) with (['b', 'b'], Right true) in
---

-- Test 3
let e = parse "
  let f = lam x. z x in
  (lam u. z)
  "
in

utest _prepTest e (f e) with ([], Left [1, 1]) in
---

-- Test 4
let e = parse "
  let f = lam x. z x in
  (lam u. y z z z)
  "
in

utest _prepTest e (f e) with (['b'], Left [1, 1, 1, 1]) in
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

utest _prepTest expected (f e) with (['b'], Right true) in
---

()
