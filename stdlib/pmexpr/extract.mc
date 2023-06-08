-- Extracts all functions that accelerate calls within a given AST depend on,
-- and returns the extracted AST together with a map from identifiers of
-- accelerated functions to their types.

include "map.mc"
include "name.mc"
include "set.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/extract.mc"
include "mexpr/lamlift.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "pmexpr/ast.mc"
include "pmexpr/utils.mc"

lang PMExprExtractAccelerate = PMExprAst + MExprExtract
  syn CopyStatus =
  | CopyBoth ()
  | CopyToAccelerate ()
  | CopyFromAccelerate ()
  | NoCopy ()

  sem omitCopyTo : CopyStatus -> CopyStatus
  sem omitCopyTo =
  | CopyBoth _ -> CopyFromAccelerate ()
  | CopyToAccelerate _ -> NoCopy ()
  | status -> status

  sem omitCopyFrom : CopyStatus -> CopyStatus
  sem omitCopyFrom =
  | CopyBoth _ -> CopyToAccelerate ()
  | CopyFromAccelerate _ -> NoCopy ()
  | status -> status

  sem copyStatusTo : CopyStatus -> Bool
  sem copyStatusTo =
  | CopyBoth _ | CopyToAccelerate _ -> true
  | _ -> false

  sem copyStatusFrom : CopyStatus -> Bool
  sem copyStatusFrom =
  | CopyBoth _ | CopyFromAccelerate _ -> true
  | _ -> false

  type AccelerateData = {
    identifier : Name,
    bytecodeWrapperId : Name,
    params : [(Name, Type)],
    paramCopyStatus : [CopyStatus],
    returnType : Type,
    info : Info
  }

  type AddIdentifierAccelerateEnv = {
    functions : Map Name AccelerateData,
    programIdentifiers : Set SID
  }

  sem collectProgramIdentifiers : AddIdentifierAccelerateEnv -> Expr
                               -> AddIdentifierAccelerateEnv
  sem collectProgramIdentifiers env =
  | TmVar t ->
    let sid = stringToSid (nameGetStr t.ident) in
    {env with programIdentifiers = setInsert sid env.programIdentifiers}
  | t -> sfold_Expr_Expr collectProgramIdentifiers env t

  sem getUniqueIdentifier =
  | programIdentifiers /- : Set SID -> Name -/ ->
    recursive let genstr = lam acc. lam n.
      if eqi n 0 then acc
      else
        let nextchr = randAlphanum () in
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
  -- 'let t = lam _x : Int. e in t 0', where t is a name containing a globally
  -- unique string within the AST. This format makes accelerate work even when
  -- there are no free variables, and it ensures that the term will be lambda
  -- lifted to the top of the program.
  sem addIdentifierToAccelerateTerms =
  | t ->
    let env = {
      functions = mapEmpty nameCmp,
      programIdentifiers = setEmpty cmpSID
    } in
    let env = collectProgramIdentifiers env t in
    match addIdentifierToAccelerateTermsH env t with (env, t) in
    let env : AddIdentifierAccelerateEnv = env in
    (env.functions, t)

  sem replaceTermWithLet (env : AddIdentifierAccelerateEnv) =
  | t ->
    let accelerateIdent = getUniqueIdentifier env.programIdentifiers in
    let bytecodeIdent = getUniqueIdentifier env.programIdentifiers in
    let retType = t.ty in
    let info = mergeInfo t.info (infoTm t.e) in
    let paramId = nameSym "x" in
    let paramTy = TyInt {info = info} in
    let functionData : AccelerateData = {
      identifier = accelerateIdent,
      bytecodeWrapperId = bytecodeIdent,
      params = [(paramId, paramTy)],
      paramCopyStatus = [CopyBoth ()],
      returnType = retType,
      info = info} in
    let env = {env with functions = mapInsert accelerateIdent functionData env.functions} in
    let funcType = TyArrow {from = paramTy, to = retType, info = info} in
    let accelerateLet =
      TmLet {
        ident = accelerateIdent,
        tyAnnot = funcType,
        tyBody = funcType,
        body = TmLam {
          ident = paramId, tyAnnot = paramTy, tyParam = paramTy, body = t.e,
          ty = TyArrow {from = paramTy, to = retType, info = info},
          info = info},
        inexpr = TmApp {
          lhs = TmVar {ident = accelerateIdent, ty = funcType, info = info, frozen = false},
          rhs = TmConst {val = CInt {val = 0}, ty = paramTy, info = info},
          ty = retType,
          info = info},
        ty = retType, info = info}
    in
    (env, accelerateLet)

  sem addIdentifierToAccelerateTermsH (env : AddIdentifierAccelerateEnv) =
  | TmAccelerate t -> replaceTermWithLet env t
  | t -> smapAccumL_Expr_Expr addIdentifierToAccelerateTermsH env t

  -- Construct an extracted AST from the given AST, containing all terms that
  -- are used by the accelerate terms.
  sem extractAccelerateTerms : Set Name -> Expr -> Expr
  sem extractAccelerateTerms accelerated =
  | t -> extractAst accelerated t

  -- NOTE(larshum, 2021-09-17): All accelerated terms are given a dummy
  -- parameter, so that expressions without free variables can also be
  -- accelerated (also for lambda lifting). Here we remove this dummy parameter
  -- for all accelerate terms with at least one free variable parameter.
  sem eliminateDummyParameter : Map Name (Map Name Type)
                             -> Map Name AccelerateData
                             -> Expr -> (Map Name AccelerateData, Expr)
  sem eliminateDummyParameter solutions accelerated =
  | ast ->
    let ast = eliminateDummyParameterH solutions accelerated ast in
    let accelerated =
      mapMapWithKey
        (lam accId : Name. lam accData : AccelerateData.
          match mapLookup accId solutions with Some fv then
            if gti (mapSize fv) 0 then
              let params = mapBindings fv in
              let copyStatus = create (length params) (lam. CopyBoth ()) in
              {{accData with params = params}
                        with paramCopyStatus = copyStatus}
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
  | TmRecLets t ->
    let isAccelerateBinding = lam bind : RecLetBinding.
      if mapMem bind.ident accelerated then
        match mapLookup bind.ident solutions with Some idSols then
          true
        else false
      else false
    in
    let eliminateBinding = lam acc. lam bind : RecLetBinding.
      if mapMem bind.ident accelerated then
        match mapLookup bind.ident solutions with Some idSols then
          match
            if gti (mapSize idSols) 0 then
              let tyBody = eliminateInnermostParameterType bind.tyBody in
              let body = eliminateInnermostLambda bind.body in
              (tyBody, body)
            else (bind.tyBody, bind.body)
          with (tyBody, body) in
          TmLet {
            ident = bind.ident,
            tyAnnot = tyBody,
            tyBody = tyBody,
            body = body,
            inexpr = acc,
            ty = tyTm acc,
            info = bind.info}
        else acc
      else acc
    in
    let inexpr = eliminateDummyParameterH solutions accelerated t.inexpr in
    match partition isAccelerateBinding t.bindings with (accelerated, bindings) in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = foldl eliminateBinding inexpr accelerated}
  | t -> smap_Expr_Expr (eliminateDummyParameterH solutions accelerated) t

  sem eliminateInnermostParameterType =
  | TyArrow {from = TyInt _, to = to & !(TyArrow _)} -> to
  | TyArrow t -> TyArrow {t with to = eliminateInnermostParameterType t.to}
  | t -> errorSingle [infoTy t] "Unexpected type of accelerate function body"

  sem eliminateInnermostLambda =
  | TmLam {body = body & !(TmLam _)} -> body
  | TmLam t -> TmLam {t with body = eliminateInnermostLambda t.body}
  | t -> errorSingle [infoTm t] "Unexpected structure of accelerate body"
end

lang TestLang =
  PMExprExtractAccelerate + MExprEq + MExprSym + MExprTypeCheck +
  MExprLambdaLift + MExprPrettyPrint
end

mexpr

use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let extractAccelerate = lam t.
  match addIdentifierToAccelerateTerms t with (accelerated, t) in
  let ids = mapMap (lam. ()) accelerated in
  let t = liftLambdas t in
  (accelerated, extractAccelerateTerms ids t)
in

let noAccelerateCalls = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  app_ (var_ "f") (int_ 2)
]) in
match extractAccelerate noAccelerateCalls with (m, ast) in
utest mapSize m with 0 in
utest ast with int_ 0 using eqExpr in

let t = preprocess (bindall_ [
  ulet_ "f" (ulam_ "x" (addi_ (var_ "x") (int_ 1))),
  ulet_ "g" (ulam_ "x" (muli_ (var_ "x") (int_ 2))),
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  accelerate_ (app_ (var_ "h") (int_ 2))
]) in
let extracted = preprocess (bindall_ [
  ulet_ "h" (ulam_ "x" (subi_ (int_ 1) (var_ "x"))),
  ulet_ "t" (ulam_ "t" (app_ (var_ "h") (int_ 2))),
  int_ 0
]) in
match extractAccelerate t with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

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
  int_ 0
]) in
match extractAccelerate t with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

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
  int_ 0
]) in
match extractAccelerate multipleCallsToSame with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

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
  int_ 0
]) in
match extractAccelerate distinctCalls with (m, ast) in
utest mapSize m with 2 in
utest ast with extracted using eqExpr in

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
  int_ 0
]) in
match extractAccelerate inRecursiveBinding with (m, ast) in
utest mapSize m with 1 in
utest ast with extracted using eqExpr in

()
