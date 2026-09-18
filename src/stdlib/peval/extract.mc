-- Defines a language fragment to extract all dependencies for the specialize
-- terms. Uses functions defined in mexpr/extract.mc

include "peval/ast.mc"

include "mexpr/eq.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"

include "stringid.mc"
include "name.mc"
include "map.mc"
include "mexpr/info.mc"
include "set.mc"
include "char.mc"
include "mexpr/pprint.mc"
include "mexpr/ast-builder.mc"


lang SpecializeExtract = MExprExtract + SpecializeAst

  type SpecializeData = {
    identifier : Name,
    bytecodeWrapperId : Name,
    params : [(Name, Type)],
    returnType : Type,
    info : Info
  }

  type AddIdentifierSpecializeEnv = {
    functions : Map Name SpecializeData,
    programIdentifiers : Set SID
  }

  sem collectProgramIdentifiers : AddIdentifierSpecializeEnv -> Expr
                               -> AddIdentifierSpecializeEnv
  sem collectProgramIdentifiers env =
  | TmVar t ->
    let sid = stringToSid (nameGetStr t.ident) in
    {env with programIdentifiers = setInsert sid env.programIdentifiers}
  | t -> sfold_Expr_Expr collectProgramIdentifiers env t

  sem getUniqueIdentifier : Set SID -> Name
  sem getUniqueIdentifier =
  | programIdentifiers ->
    recursive let genstr = lam acc. lam n.
      if eqi n 0 then acc
      else
        let nextchr = randAlphanum () in
        genstr (snoc acc nextchr) (subi n 1)
    in
    let str = genstr "v" 10 in
    if setMem (stringToSid str) programIdentifiers then
      getUniqueIdentifier programIdentifiers
    else nameSym str

  sem replaceTermWithLet (env: AddIdentifierSpecializeEnv) =
  | t ->
    let specializeIdent = getUniqueIdentifier env.programIdentifiers in
    let bytecodeIdent = getUniqueIdentifier env.programIdentifiers in
    let retType = t.ty in
    let info = mergeInfo t.info (infoTm t.e) in
    let paramId = nameSym "x" in
    let paramTy = TyInt {info = info} in
    let functionData = {
      identifier = specializeIdent,
      bytecodeWrapperId = bytecodeIdent,
      params = [(paramId, paramTy)],
      returnType = retType,
      info = info
    } in
    let env = {env with functions = mapInsert specializeIdent functionData env.functions} in
    let funcType = TyArrow {from = paramTy, to = retType, info = info} in
    let specializeLet = TmDecl {
      decl = DeclLet {
        ident = specializeIdent,
        tyAnnot = funcType,
        tyBody = funcType,
        body = TmLam {
          ident = paramId,
          tyAnnot = paramTy,
          tyParam = paramTy,
          body = t.e,
          ty = TyArrow {from = paramTy, to = retType, info = info},
          info = info
        },
        info = info
      },
      inexpr = TmApp {
        lhs = TmVar {ident = specializeIdent, ty = funcType, info = info, frozen = false},
        rhs = TmConst {val = CInt {val = 0}, ty = paramTy, info = info},
        ty = retType,
        info = info
      },
      ty = retType,
      info = info
    } in
    (env, specializeLet)

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

use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let extractSpecialize = lam t.
  match addIdentifierToSpecializeTerms t with (specialized, t) in
  let ids = mapMap (lam. ()) specialized in
  let t = liftLambdas t in
  (specialized, extractSpecializeTerms ids t)
in

let noSpecializeCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))]
  (app_ (var_ "f") (int_ 2)
)) in
match extractSpecialize noSpecializeCalls with (m, ast) in
utest mapSize m with 0 in
utest ast with int_ 0 using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x")))]
  (specialize_ (app_ (var_ "h") (int_ 2))
)) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "h") (int_ 2)))]
  (int_ 0
)) in
match extractSpecialize t with (m, ast) in

utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x")))]
  (specialize_ (app_ (var_ "g") (int_ 4))
)) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 4)))]
  (int_ 0
)) in
match extractSpecialize t with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let multipleCallsToSame = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (bindall_ [
    ulet_ "y" (addi_ (var_ "x") (int_ 2))]
    (specialize_ (app_ (var_ "f") (var_ "y"))
  ))),
  ulet_ "h" (ulam_ "x" (specialize_ (app_ (var_ "f") (var_ "x"))))]
  (addi_
    (app_ (var_ "g") (int_ 1))
    (app_ (var_ "h") (int_ 3))
)) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "t" (ulam_ "y" (ulam_ "" (app_ (var_ "f") (var_ "y")))),
  ulet_ "t" (ulam_ "x" (ulam_ "" (app_ (var_ "f") (var_ "x"))))]
  (int_ 0
)) in
match extractSpecialize multipleCallsToSame with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1)))]
  (addi_
    (specialize_ (app_ (var_ "f") (int_ 1)))
    (specialize_ (app_ (var_ "g") (int_ 0)))
)) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "f") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 0)))]
  (int_ 0
)) in
match extractSpecialize distinctCalls with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "h" (specialize_ (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x")))]
  (specialize_ (app_ (var_ "z") (int_ 1)))
) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1))),
  ulet_ "z" (ulam_ "x" (app_ (var_ "f") (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "z") (int_ 1)))]
  (int_ 0
)) in
match extractSpecialize distinctCalls with (m, ast) in
utest ast with extracted using eqExpr in

let specializeVar = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  -- Extraction does not work in this case
  ulet_ "bar" (app_ (var_ "foo") (int_ 1))]
  (specialize_ (var_ "bar")
)) in

let expected = preprocess (bindall_ [
  ulet_ "foo" (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "bar" (app_ (var_ "foo") (int_ 1)),
  ulet_ "t" (ulam_ "t" (app_ (var_ "bar") (int_ 3)))]
  (int_ 0
)) in


match extractSpecialize specializeVar with (m, ast) in
-- utest ast with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "x" (specialize_ (app_ (var_ "g") (var_ "x"))))]]
  (app_ (var_ "h") (int_ 3)
)) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("t", ulam_ "x" (ulam_ "" (app_ (var_ "g") (var_ "x")))),
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1))))]]
  (int_ 0
)) in
match extractSpecialize inRecursiveBinding with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

let partialCalls = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "h" (specialize_ (app_ (var_ "g") (int_ 1)))
] unit_) in
let extracted = preprocess (bindall_ [
  ulet_ "g" (ulam_ "y" (ulam_ "x" (addi_ (var_ "x") (var_ "y")))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 1)))]
  (int_ 0
)) in
match extractSpecialize partialCalls with (m, ast) in
utest ast with extracted using eqExpr in

()
