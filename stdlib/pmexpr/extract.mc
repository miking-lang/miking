-- Extracts all functions that accelerate calls within a given AST depend on,
-- and returns the extracted AST together with a map from identifiers of
-- accelerated functions to their types.

include "map.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-annot.mc"
include "pmexpr/ast.mc"
include "pmexpr/utils.mc"

type AccelerateData = {
  identifier : Name,
  bytecodeWrapperId : Name,
  params : [(Name, Type)],
  returnType : Type,
  info : Info
}

type AddIdentifierAccelerateEnv = {
  functions : Map Expr AccelerateData,
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

lang PMExprExtractAccelerate = PMExprAst + MExprLambdaLift
  sem collectProgramIdentifiers (env : AddIdentifierAccelerateEnv) =
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
    -- NOTE(larshum, 2021-09-15): Start the string with a hard-coded alphabetic
    -- character to avoid ending up with a digit in the first position.
    let str = genstr "v" 10 in
    if setMem (stringToSid str) programIdentifiers then
      getUniqueIdentifier programIdentifiers
    else nameSym str

  -- Adds identifiers to accelerate terms and collects information on the
  -- accelerated terms. An accelerate term 'accelerate e' is rewritten as
  -- 'let t = lam x : Int. accelerate e x in t 0', where t is a name containing
  -- a globally unique string within the AST. This format makes accelerate work
  -- even when there are no free variables, and it ensures that the term will
  -- be lambda lifted to the top of the program.
  sem addIdentifierToAccelerateTerms =
  | t ->
    let env = {
      functions = mapEmpty nameCmp,
      programIdentifiers = setEmpty cmpSID
    } in
    let env = collectProgramIdentifiers env t in
    match addIdentifierToAccelerateTermsH env t with (env, t) then
      let env : AddIdentifierAccelerateEnv = env in
      (env.functions, t)
    else never

  sem addIdentifierToAccelerateTermsH (env : AddIdentifierAccelerateEnv) =
  | TmAccelerate t ->
    let accelerateIdent = getUniqueIdentifier env.programIdentifiers in
    let bytecodeIdent = getUniqueIdentifier env.programIdentifiers in
    let retType = t.ty in
    let info = infoTm t.e in
    let paramId = nameSym "x" in
    let paramTy = TyInt {info = info} in
    let functionData : AccelerateData = {
      identifier = accelerateIdent,
      bytecodeWrapperId = bytecodeIdent,
      params = [(paramId, paramTy)],
      returnType = retType,
      info = info} in
    let env = {env with functions = mapInsert accelerateIdent functionData env.functions} in
    let funcType = TyArrow {from = paramTy, to = retType, info = info} in
    let accelerateLet =
      TmLet {
        ident = accelerateIdent,
        tyBody = funcType,
        body = TmLam {ident = paramId, tyIdent = paramTy,
                      body = t.e, ty = retType, info = info},
        inexpr = TmApp {
          lhs = TmVar {ident = accelerateIdent, ty = funcType, info = info},
          rhs = TmConst {val = CInt {val = 0}, ty = paramTy, info = info},
          ty = retType,
          info = info},
        ty = retType, info = info}
    in
    (env, accelerateLet)
  | t -> smapAccumL_Expr_Expr addIdentifierToAccelerateTermsH env t

  sem collectIdentifiersExprH (bound : Set Name) (used : Set Name) =
  | TmVar t ->
    if setMem t.ident bound then used
    else setInsert t.ident used
  | TmLam t ->
    let bound = setInsert t.ident bound in
    collectIdentifiersExprH bound used t.body
  | t -> sfold_Expr_Expr (collectIdentifiersExprH bound) used t

  sem collectIdentifiersExpr (used : Set Name) =
  | t -> collectIdentifiersExprH (setEmpty nameCmp) used t

  sem collectIdentifiersType (used : Set Name) =
  | TyVar t -> setInsert t.ident used
  | t -> sfold_Type_Type collectIdentifiersType used t

  -- Construct an extracted AST from the given AST, containing all terms that
  -- are used by the accelerate terms.
  sem extractAccelerateTerms (accelerated : Set Name) =
  | t ->
    match extractAccelerateTermsH accelerated t with (_, t) then
      t
    else never

  sem extractAccelerateTermsH (used : Set Name) =
  | TmLet t ->
    match extractAccelerateTermsH used t.inexpr with (used, inexpr) then
      if setMem t.ident used then
        let used = collectIdentifiersType used t.tyBody in
        let used = collectIdentifiersExpr used t.body in
        (used, TmLet {t with inexpr = inexpr})
      else
        (used, inexpr)
    else never
  | TmRecLets t ->
    let bindingIdents = map (lam bind : RecLetBinding. bind.ident) t.bindings in
    recursive let dfs = lam g. lam visited. lam ident.
      if setMem ident visited then visited
      else
        let visited = setInsert ident visited in
        foldl
          (lam visited. lam ident.
            dfs g visited ident)
          visited
          (digraphSuccessors ident g)
    in
    let collectBindIdents = lam used. lam bind : RecLetBinding.
      let used = collectIdentifiersType used bind.tyBody in
      collectIdentifiersExpr used bind.body
    in
    match extractAccelerateTermsH used t.inexpr with (used, inexpr) then
      -- Construct a call graph, reusing functions from lambda lifting. By
      -- using DFS on this graph, we find the bindings that are used.
      let g : Digraph Name Int = digraphEmpty nameCmp eqi in
      let g = addGraphVertices g (TmRecLets t) in
      let g =
        foldl
          (lam g. lam bind : RecLetBinding.
            addGraphCallEdges bind.ident g bind.body)
          g t.bindings in
      let visited = setEmpty nameCmp in
      let usedIdents =
        foldl
          (lam visited. lam ident.
            if setMem ident used then
              dfs g visited ident
            else visited)
          visited bindingIdents in
      let usedBinds =
        filter
          (lam bind : RecLetBinding. setMem bind.ident usedIdents)
          t.bindings in
      let used = foldl collectBindIdents used usedBinds in
      if null usedBinds then (used, inexpr)
      else (used, TmRecLets {{t with bindings = usedBinds}
                                with inexpr = inexpr})
    else never
  | TmType t ->
    match extractAccelerateTermsH used t.inexpr with (used, inexpr) then
      if setMem t.ident used then (used, TmType {t with inexpr = inexpr})
      else (used, inexpr)
    else never
  | TmConDef t -> extractAccelerateTermsH used t.inexpr
  | TmUtest t -> extractAccelerateTermsH used t.next
  | TmExt t -> extractAccelerateTermsH used t.inexpr
  | t -> (used, unit_)

  -- NOTE(larshum, 2021-09-17): All accelerated terms are given a dummy
  -- parameter, so that expressions without free variables can also be
  -- accelerated (also for lambda lifting). Here we remove this dummy parameter
  -- for all accelerate terms with at least one free variable parameter.
  sem eliminateDummyParameter (solutions : Map Name Type)
                              (accelerated : Map Name AccelerateData) =
  | ast ->
    let ast = eliminateDummyParameterH solutions accelerated ast in
    let accelerated =
      mapMapWithKey
        (lam accId : Name. lam accData : AccelerateData.
          match mapLookup accId solutions with Some fv then
            if gti (mapSize fv) 0 then
              {accData with params = mapBindings fv}
            else accData
          else accData)
        accelerated in
    (accelerated, ast)

  sem eliminateDummyParameterH (solutions : Map Name (Map Name Type))
                               (accelerated : Map Name AccelerateData) =
  | TmLet t ->
    let inexpr = eliminateDummyParameterH solutions accelerated t.inexpr in
    if mapMem t.ident accelerated then
      match mapLookup t.ident solutions with Some idSols then
        if gti (mapSize idSols) 0 then
          TmLet {{{t with tyBody = eliminateInnermostParameterType t.tyBody}
                     with body = eliminateInnermostLambda t.body}
                     with inexpr = inexpr}
        else TmLet {t with inexpr = inexpr}
      else TmLet {t with inexpr = inexpr}
    else TmLet {t with inexpr = inexpr}
  | t -> smap_Expr_Expr (eliminateDummyParameterH solutions accelerated) t

  sem eliminateInnermostParameterType =
  | TyArrow {from = TyInt _, to = to & !(TyArrow _)} -> to
  | TyArrow t -> TyArrow {t with to = eliminateInnermostParameterType t.to}
  | t -> infoErrorExit (infoTy t) "Unexpected type of accelerate function body"

  sem eliminateInnermostLambda =
  | TmLam {body = body & !(TmLam _)} -> body
  | TmLam t -> TmLam {t with body = eliminateInnermostLambda t.body}
  | t -> infoErrorExit (infoTm t) "Unexpected structure of accelerate body"
end

lang TestLang =
  PMExprExtractAccelerate + MExprEq + MExprSym + MExprTypeAnnot +
  MExprLambdaLift + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t.
  typeAnnot (symbolize t)
in

let extractAccelerate = lam t.
  match addIdentifierToAccelerateTerms t with (accelerated, t) then
    let ids = mapMap (lam. ()) accelerated in
    let t = liftLambdas t in
    (accelerated, extractAccelerateTerms ids t)
  else never
in

let noAccelerateCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
let x : (Map Name AccelerateData, Expr) = extractAccelerate noAccelerateCalls in
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
  ulet_ "t" (ulam_ "t" (app_ (var_ "h") (int_ 2))),
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
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 4))),
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
  ulet_ "t" (ulam_ "y" (ulam_ "" (app_ (var_ "f") (var_ "y")))),
  ulet_ "t" (ulam_ "x" (ulam_ "" (app_ (var_ "f") (var_ "x")))),
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
  ulet_ "t" (ulam_ "t" (app_ (var_ "f") (int_ 1))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "g") (int_ 0))),
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
    ("g", ulam_ "x" (app_ (var_ "f") (addi_ (var_ "x") (int_ 1)))),
    ("t", ulam_ "x" (ulam_ "" (app_ (var_ "g") (var_ "x"))))],
  unit_
]) in
let x : (Map Name Type, Expr) = extractAccelerate inRecursiveBinding in
utest mapSize x.0 with 1 in
utest x.1 with extracted using eqExpr in

()
