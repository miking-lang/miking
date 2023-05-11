include "result.mc"

-- MExpr
include "ast.mc"
include "eq.mc"
include "boot-parser.mc"

/-

  This file implements shallow mapping/folding with `Result w e a` from
  `result.mc` over `Expr`s, white propagating as many errors and warnings as
  possible.

  -/

lang AstResult = Ast

  -- Perform a computation on the immediate sub-expressions of an expression,
  -- while simultaneously threading an accumulator. An error in the accumulator
  -- causes an immeadiate return and its errors and warnings are propagated to
  -- the expression result, but not vise-versa. For the expression result, it
  -- produces a non-error only if all individual computations produce a
  -- non-error and preserves all errors and warnings.
  sem smapAccumL_ResultM_Expr_Expr
    : all w. all e. all a.
      (a -> Expr -> (Result w e a, Result w e Expr))
       -> a
         -> Expr
           -> (Result w e a, Result w e Expr)
  sem smapAccumL_ResultM_Expr_Expr f acc =
  | e ->
    let withAnnot = result.withAnnotations in
    let consume = result.consume in
    let ok = result.ok in
    let inner = lam acc. lam e.
      match acc with (accAnnot, exprAnnot, acc) in
      match consume accAnnot with (_ , Left _) then
        -- NOTE(oerikss, 2023-05-12 (my birthday! 🎂)): If there is an error in
        -- the accumulator we stop calling the user supplied function `f`.
        ((accAnnot, exprAnnot, acc), e)
      else
        match f acc e with (accRes, exprRes) in
        switch (consume accRes, consume exprRes)
        case ((_, Right acc), (_, Right e)) then
          ((withAnnot accRes accAnnot, withAnnot exprRes exprAnnot, acc), e)
        case ((_, Right acc), _) then
          ((withAnnot accRes accAnnot, withAnnot exprRes exprAnnot, acc), e)
        case ((_, Left _), _) then
          -- NOTE(oerikss, 2023-05-12): If there is an error in the accumulator
          -- we propagate its annotations to the expression result.
          let accRes = withAnnot accRes accAnnot in
          ((accRes, withAnnot accRes (withAnnot exprRes exprAnnot), acc), e)
        end
    in
    match smapAccumL_Expr_Expr inner (ok (), ok (), acc) e
      with ((accAnnot, exprAnnot, acc), e)
    in
    (withAnnot accAnnot (ok acc), withAnnot exprAnnot (ok e))

  -- Perform a computation on the the immediate sub-expressions of an
  -- expression. Produces a non-error only if all individual computations
  -- produce a non-error. Preserves all errors and warnings.
  sem smap_ResultM_Expr_Expr
    : all w. all e. (Expr -> Result w e Expr) -> Expr -> Result w e Expr
  sem smap_ResultM_Expr_Expr f =
  | e ->
    let withAnnot = result.withAnnotations in
    let consume = result.consume in
    let ok = result.ok in
    let inner = lam annot. lam e.
      let res = f e in
      let e = match consume res with (_, Right e) then e else e in
      (withAnnot res annot, e)
    in
    match smapAccumL_Expr_Expr inner (ok ()) e
      with (annot, res)
    in
    withAnnot annot (ok res)

  -- Folds a computation on the the immediate sub-expressions of an
  -- expression. An error causes an immediate return. Preserves all errors and
  -- warnings.
  sem sfold_ResultM_Expr_Expr
    : all w. all e. all a. (a -> Expr -> Result w e a) -> a -> Expr -> Result w e a
  sem sfold_ResultM_Expr_Expr f acc =
  | e ->
    let withAnnot = result.withAnnotations in
    let consume = result.consume in
    let ok = result.ok in
    let inner : (Result w e (), a) -> Expr -> (Result w e (), a)
      = lam acc. lam e.
        match acc with (accAnnot, acc) in
        match consume accAnnot with (_ , Left _) then
          -- NOTE(oerikss, 2023-05-12): If there is an error in the accumulator we
          -- stop calling the user supplied function `f`.
          (accAnnot, acc)
        else
          match f acc e with accRes in
          let acc =
            switch consume accRes
            case (_, Right acc) then acc
            case (_, Left _) then acc
            end
          in
          (withAnnot accRes accAnnot, acc)
    in
    match sfold_Expr_Expr inner (ok (), acc) e with (annot, acc) in
    withAnnot annot (ok acc)
end

lang TestLang = AstResult + BootParser + MExprEq end

mexpr

use TestLang in

let parse =
  parseMExprString
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
  (prepTest (result.map (sort cmpString) p.0),
   prepTest (result.map (eqExpr e) p.1))
in

-- Accumulates variable names and renames variables by concatenating
-- its name to itself. For the accumulator, variables with names 'x' gives the
-- warning 'a' and an accumulator of length greater than 3 gives an error 0. For
-- the expressions, variables with names 'y' gives a warning 'b' and variables
-- with names 'z' gives an error 1.
recursive let f
  : [String] -> Expr -> (Result Char Int [String], (Result Char Int Expr))
  = lam acc. lam e.
    let ann = result.withAnnotations in
    switch e
    case TmVar r then
      let name = nameGetStr r.ident in
      let acc =
        if gti (length acc) 3 then result.err 0
        else result.ok (cons name acc)
      in
      let e =
        match name with "z" then result.err 1
        else
          result.ok
            (TmVar { r with ident = nameSetStr r.ident (concat name name) })
      in
      switch name
      case "x" then (ann (result.warn 'a')  acc, e)
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
  ((['a'], Right ["f", "u", "x", "y"]), (['b'], Right true))
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
  ((['a'], Right ["f", "x", "y", "y"]), (['b', 'b'], Right true))
in
---

-- Test 3
let e = parse "
  let f = lam x. z x in
  (lam u. z)
  "
in

utest _prepTest e (f [] e) with
  ((['a'], Right ["x", "z", "z"]), ([], Left [1, 1]))
in
---

-- Test 4 (Corner case for early return due to an error in accumulator)
let e = parse "
  let f = lam x. z x in
  (lam u. y z z z)
  "
in

utest _prepTest e (f [] e) with
  ((['a'], Left [0]), (['a', 'b'], Left [0, 1, 1, 1]))
in
---

-- Test 5 (Error propagation from error accumulator to an non-error expression)
let e = parse "
  let f = lam x. x x in
  (lam u. y x x)
  "
in

utest _prepTest e (f [] e) with
  ((['a','a','a','a'], Left [0]), (['a','a','a','a','b'], Left [0]))
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


---------------------------------------
-- Test sfold_ResultM_Expr_Expr --
---------------------------------------

let _prepTest = lam res. prepTest (result.map (sort cmpString) res) in

-- Accumulates variable names. Variables with names 'x' gives the warning 'a'
-- and an accumulator of length greater than 3 gives an error 0.
recursive let f : [String] -> Expr -> Result Char Int [String]
  = lam acc. lam e.
    let ann = result.withAnnotations in
    switch e
    case TmVar r then
      let name = nameGetStr r.ident in
      let acc =
        if gti (length acc) 3 then result.err 0
        else result.ok (cons name acc)
      in
      switch name
      case "x" then ann (result.warn 'a')  acc
      case _ then acc
      end
    case e then sfold_ResultM_Expr_Expr f acc e
    end
in

-- Test 1
let e = parse "
  let f = lam x. y x in
  (lam u. f u)
  "
in

utest _prepTest (f [] e) with (['a'], Right ["f", "u", "x", "y"]) in
---

-- Test 2
let e = parse "
  let f = lam x. y y x in
  (lam u. f)
  "
in

utest _prepTest (f [] e) with (['a'], Right ["f", "x", "y", "y"]) in
---

-- Test 3
let e = parse "
  let f = lam x. z x in
  (lam u. z)
  "
in

utest _prepTest (f [] e) with (['a'], Right ["x", "z", "z"]) in
---

-- Test 4 (Corner case for early return due to an error in accumulator)
let e = parse "
  let f = lam x. x x in
  (lam u. x x x)
  "
in

utest _prepTest (f [] e) with (['a','a','a','a','a'], Left [0]) in
---

-- Test 5
let e = parse "
  let f = lam x. x x in
  (lam u. y x x)
  "
in

utest _prepTest (f [] e) with (['a','a','a','a'], Left [0]) in
---


()
