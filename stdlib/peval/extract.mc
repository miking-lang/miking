-- Defines a language fragment to extract all dependencies for the specialize
-- terms. Uses the functions defined in pmexpr/extract.mc and mexpr/extract.mc

include "pmexpr/extract.mc"
include "peval/ast.mc"

include "mexpr/eq.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

include "stringid.mc"
include "name.mc"
include "map.mc"


lang SpecializeExtract = PMExprExtractAccelerate + SpecializeAst

  type SpecializeData = AccelerateData

  type AddIdentifierSpecializeEnv = AddIdentifierAccelerateEnv

  sem addIdentifierToSpecializeTerms =
  | t ->
    let env = {
      functions = mapEmpty nameCmp,
      programIdentifiers = setEmpty cmpSID
    } in
    let env = collectProgramIdentifiers env t in
    match addIdentifierToSpecializeTermsH env t with (env, t) in
    let env : AddIdentifierSpecializeEnv = env in
    (env.functions, t)

  sem addIdentifierToSpecializeTermsH (env : AddIdentifierSpecializeEnv) =
  | TmSpecialize t -> replaceTermWithLet env {e=t.e, info = t.info, ty = tyTm t.e}
  | t -> smapAccumL_Expr_Expr addIdentifierToSpecializeTermsH env t

  sem extractSpecializeTerms : Set Name -> Expr -> Expr
  sem extractSpecializeTerms ids =
  | ast -> extractAst ids ast

  sem extractSeparate : [Name] -> Expr -> Map Name Expr
  sem extractSeparate ids =| ast ->
    foldl (lam m. lam id.
      let idset = setOfSeq nameCmp [id] in
      let extracted = extractSpecializeTerms idset ast in
      mapInsert id extracted m
    ) (mapEmpty nameCmp) ids

end

lang TestLang =
   SpecializeExtract + MExprEq + MExprSym + MExprTypeCheck + MExprPrettyPrint +
   MExprLambdaLift
end

mexpr

-- The below tests are essentially identical to the ones in stdlib/pmexpr/extract.mc
-- But adapted to use 'specialize' instead

use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let extractSpecialize = lam t.
  match addIdentifierToSpecializeTerms t with (specialized, t) in
  let ids = mapMap (lam. ()) specialized in
  let t = liftLambdas t in
  (specialized, extractAccelerateTerms ids t)
in

let noSpecializeCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
match extractSpecialize noSpecializeCalls with (m, ast) in
utest mapSize m with 0 in
utest ast with int_ 0 using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  specialize_ (app_ (var_ "h") (int_ 2))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "h") (int_ 2))),
  int_ 0
]) in
match extractSpecialize t with (m, ast) in

utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  specialize_ (app_ (var_ "g") (int_ 4))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 4))),
  int_ 0
]) in
match extractSpecialize t with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let multipleCallsToSame = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (bindall_ [
    ulet_ "y" (addi_ (var_ "x") (int_ 2)),
    specialize_ (app_ (var_ "f") (var_ "y"))
  ])),
  ulet_ "h" (ulam_ "x" (specialize_ (app_ (var_ "f") (var_ "x")))),
  addi_
    (app_ (var_ "g") (int_ 1))
    (app_ (var_ "h") (int_ 3))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "t" (ulam_ "y" (ulam_ "" (app_ (var_ "f") (var_ "y")))),
  ulet_ "t" (ulam_ "x" (ulam_ "" (app_ (var_ "f") (var_ "x")))),
  int_ 0
]) in
match extractSpecialize multipleCallsToSame with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  addi_
    (specialize_ (app_ (var_ "f") (int_ 1)))
    (specialize_ (app_ (var_ "g") (int_ 0)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "f") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 0))),
  int_ 0
]) in
match extractSpecialize distinctCalls with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "h" (specialize_ (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x"))),
  (specialize_ (app_ (var_ "z") (int_ 1)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "z") (int_ 1))),
  int_ 0
]) in
match extractSpecialize distinctCalls with (m, ast) in
utest ast with extracted using eqExpr in

let specializeVar = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  -- Extraction does not work in this case
  ulet_ "bar" (app_ (var_ "foo") (int_ 1)),
  specialize_ (var_ "bar")
]) in

let expected = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "bar" (app_ (var_ "foo") (int_ 1)),
  ulet_ "t" (ulam_ "t" (app_ (var_ "bar") (int_ 3))),
  int_ 0
]) in


match extractSpecialize specializeVar with (m, ast) in
-- utest ast with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "x" (specialize_ (app_ (var_ "g") (var_ "x"))))],
  app_ (var_ "h") (int_ 3)
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("t", ulam_ "x" (ulam_ "" (app_ (var_ "g") (var_ "x"))))],
  int_ 0
]) in
match extractSpecialize inRecursiveBinding with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let partialCalls = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (specialize_ (app_ (var_ "g") (int_ 1)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1))),
  int_ 0
]) in
match extractSpecialize partialCalls with (m, ast) in
utest ast with extracted using eqExpr in

()

