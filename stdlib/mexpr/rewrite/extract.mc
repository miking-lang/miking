-- Extracts all functions that accelerate calls within a given AST depend on,
-- and returns the extracted AST together with a map from identifiers of
-- accelerated functions to their types.

include "map.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "mexpr/rewrite/parallel-keywords.mc"
include "mexpr/rewrite/utils.mc"

type AcceleratedFunctionData = {
  identifier : Name,
  bytecodeWrapperId : Name,
  params : [(Name, Info, Type)],
  returnType : Type,
  info : Info
}

type ExtractAccelerateEnv = {
  functions : Map Expr AcceleratedFunctionData,
  used : Map Name (Info, Type),
  programIdentifiers : Set SID
}

-- Generates a random ASCII letter or digit character.
let _randAlphanum : Unit -> Char = lam.
  -- NOTE(larshum, 2021-09-15): The total number of digits or ASCII letters
  -- (lower- and upper-case) is 10 + 26 + 26 = 62.
  let r = randIntU 0 62 in
  if lti r 10 then int2char (addi r 48)
  else if lti r 36 then int2char (addi r 55)
  else int2char (addi r 61)

lang PMExprExtractAccelerate = MExprParallelKeywordMaker + MExprCmp
  sem collectProgramIdentifiers (env : ExtractAccelerateEnv) =
  | TmVar t ->
    let sid = stringToSid (nameGetStr t.ident) in
    {env with programIdentifiers = setInsert sid env.programIdentifiers}
  | t -> sfold_Expr_Expr collectProgramIdentifiers env t

  sem getUniqueIdentifier =
  | programIdentifiers /- : Set SID -> Name -/ ->
    recursive let genstr = lam acc. lam n.
      if eqi n 0 then acc
      else
        let nextchr = _randAlphanum () in
        genstr (snoc acc nextchr) (subi n 1)
    in
    let str = genstr "v" 10 in
    if setMem (stringToSid str) programIdentifiers then
      getUniqueIdentifier programIdentifiers
    else nameSym str

  sem freeVariablesInAccelerateTermH (freeVars : Map Name (Info, Type)) =
  | TmVar t ->
    if mapMem t.ident freeVars then freeVars
    else mapInsert t.ident (t.info, t.ty) freeVars
  | TmUtest t ->
    infoErrorExit t.info "Cannot accelerate utest terms"
  | TmExt t ->
    infoErrorExit t.info "Cannot accelerate external functions"
  | TmAccelerate t ->
    infoErrorExit t.info "Nested accelerate terms are not supported"
  | t -> sfold_Expr_Expr freeVariablesInAccelerateTermH freeVars t

  sem freeVariablesInAccelerateTerm =
  | t -> freeVariablesInAccelerateTermH (mapEmpty nameCmp) t

  sem collectAccelerate (env : ExtractAccelerateEnv) =
  | TmAccelerate t ->
    let isArrowType = lam expr.
      match ty expr with TyArrow _ then true
      else false
    in
    if isArrowType t.e then
      infoErrorExit (infoTm t.e) "Cannot accelerate partially applied function"
    else
      let accelerateIdent = getUniqueIdentifier env.programIdentifiers in
      let bytecodeWrapperIdent = getUniqueIdentifier env.programIdentifiers in

      -- NOTE(larshum, 2021-09-09): The parameters of the accelerate function
      -- are the free variables, that are not of an arrow type, within the
      -- accelerated expression.
      let freeVars = freeVariablesInAccelerateTerm t.e in
      let params =
        mapFoldWithKey
          (lam acc. lam id. lam freeVar : (Info, Type).
            match freeVar.1 with TyArrow _ then acc
            else snoc acc (id, freeVar.0, freeVar.1))
          []
          freeVars
      in
      let info = infoTm t.e in
      let entry = {
        identifier = accelerateIdent,
        bytecodeWrapperId = bytecodeWrapperIdent,
        params = params,
        info = info,
        returnType = ty t.e
      } in

      -- NOTE(larshum, 2021-09-09): The free variables of arrow-type must be
      -- included in the accelerated AST, as they cannot be passed through C.
      let used =
        mapFoldWithKey
          (lam acc. lam paramId. lam paramData : (Info, Type).
            let paramType = paramData.1 in
            match paramType with TyArrow _ then
              mapInsert paramId paramData acc
            else acc)
          env.used
          freeVars
      in
      {{env with functions = mapInsert t.e entry env.functions}
            with used = used}
  | t -> sfold_Expr_Expr collectAccelerate env t

  sem extractAccelerateAst (env : ExtractAccelerateEnv) =
  | TmLet t ->
    let inexpr = extractAccelerateAst env t.inexpr in
    if mapMem t.ident env.used then
      TmLet {t with inexpr = inexpr}
    else inexpr
  | TmRecLets t ->
    let inexpr = extractAccelerateAst env t.inexpr in
    let bindings =
      foldl
        (lam acc. lam bind : RecLetBinding.
          if mapMem bind.ident env.used then snoc acc bind
          else acc)
        []
        t.bindings
    in
    if null bindings then inexpr
    else TmRecLets {{t with bindings = bindings}
                       with inexpr = inexpr}
  | t -> smap_Expr_Expr (extractAccelerateAst env) t

  -- Inserts the accelerated functions at the bottom of the accelerated AST.
  -- This is fine because they are independent of each other, and all their
  -- individual dependencies are in the earlier parts of the AST.
  sem insertAccelerateFunctions (env : ExtractAccelerateEnv) =
  | t /- : Expr -/ ->
    mapFoldWithKey
      (lam acc. lam expr. lam data : AcceleratedFunctionData.
        let functionType =
          foldr
            (lam param : (Name, Info, Type). lam tyAcc : Type.
              TyArrow {from = param.2, to = tyAcc, info = param.1})
            data.returnType
            data.params
        in
        let accelerateFunction =
          TmLet {ident = data.identifier, tyBody = functionType, body = expr,
                 inexpr = unit_, ty = tyunit_, info = data.info}
        in
        bind_ acc accelerateFunction)
      t
      env.functions

  sem extractAccelerate =
  | t ->
    let emptyEnv = {functions = mapEmpty cmpExpr, used = mapEmpty nameCmp,
                    programIdentifiers = setEmpty cmpSID} in
    let env = collectProgramIdentifiers emptyEnv t in
    let env = collectAccelerate env t in
    let acceleratedAst = extractAccelerateAst env t in
    let acceleratedAst = insertAccelerateFunctions env acceleratedAst in
    (env.functions, acceleratedAst)
end

lang TestLang = PMExprExtractAccelerate + MExprEq + MExprTypeAnnot

mexpr

use MExprPrettyPrint in
use TestLang in

let preprocess = lam t.
  typeAnnot (symbolize t)
in

let noAccelerateCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
let x : (Map Name Type, Expr) = extractAccelerate noAccelerateCalls in
utest mapSize x.0 with 0 in
utest x.1 with unit_ using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  accelerate_ (app_ (var_ "h") (int_ 2))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate t in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  accelerate_ (app_ (var_ "g") (int_ 4))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (app_ (var_ "f") (var_ "x")) (int_ 2))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate t in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

let multipleCallsToSame = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (bindall_ [
    ulet_ "y" (addi_ (var_ "x") (int_ 2)),
    accelerate_ (app_ (var_ "f") (var_ "y"))
  ])),
  ulet_ "h" (ulam_ "x" (accelerate_ (app_ (var_ "f") (var_ "x")))),
  addi_
    (app_ (var_ "g") (int_ 1))
    (app_ (var_ "h") (int_ 3))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate multipleCallsToSame in
utest mapSize x.0 with 2 in
utest x.1 with extracted using eqExpr in

let distinctCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  addi_
    (accelerate_ (app_ (var_ "f") (int_ 1)))
    (accelerate_ (app_ (var_ "g") (int_ 0)))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 3))),
  ulet_ "g" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate distinctCalls in
utest mapSize x.0 with 2 in
utest x.1 with extracted using eqExpr in

let inRecursiveBinding = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("h", ulam_ "x" (accelerate_ (app_ (var_ "g") (var_ "x"))))],
  app_ (var_ "h") (int_ 3)
]) in
let extracted = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ureclets_ [
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1))))],
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate inRecursiveBinding in
utest mapSize x.0 with 1 in
printLn (expr2str x.1);
-- utest x.1 with extracted using eqExpr in

()
