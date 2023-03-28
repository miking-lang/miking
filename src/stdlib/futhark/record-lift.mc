-- Lifts record parameters which are only used in projections by replacing them
-- with parameters representing the projected fields.
--
-- This transformation is important for aliasing reasons. If we only use a
-- subset of the fields in a record, but the full record is passed, then all
-- fields will be considered aliased. This may prevent elimination of
-- unnecessary copying in in-place updates, which may significantly degrade the
-- performance.

-- TODO(larshum, 2021-11-01): Does this work for nested records?

include "stringid.mc"
include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

let _collectAppTargetAndArgs = use FutharkAst in
  lam e : FutExpr.
  recursive let work = lam args : [FutExpr]. lam e : FutExpr.
    match e with FEApp {lhs = !(FEApp _) & lhs, rhs = rhs} then
      (lhs, cons rhs args)
    else match e with FEApp t then
      work (cons t.rhs args) t.lhs
    else (e, args)
  in work [] e

let _constructAppSeq = use FutharkAst in
  lam target : FutExpr. lam args : [FutExpr].
  foldl
    (lam acc : FutExpr. lam arg : FutExpr.
      let ty =
        match tyFutTm acc with FTyArrow t then
          t.to
        else FTyUnknown {info = infoFutTm acc} in
      let info = mergeInfo (infoFutTm acc) (infoFutTm arg) in
      FEApp {lhs = acc, rhs = arg, ty = ty, info = info})
    target
    args

lang FutharkRecordParamLift = FutharkAst
  type ParamData = (Name, FutType)

  type FunctionReplaceData = {
    -- Contains the type of the function after replacing record parameters with a
    -- record field parameters.
    newType : FutType,

    -- The sequence of parameter names and type, as expected by the function
    -- prior to the record parameter lifting.
    oldParams : [ParamData],

    -- Maps the name of a replaced record parameter to the parameters of the
    -- fields that replaced it.
    paramReplace : Map Name (Map SID ParamData)
  }

  sem updateParams : FunctionReplaceData -> FutExpr -> [FutExpr] -> Info -> FutExpr
  sem updateParams data target args =
  | info ->
    let data : FunctionReplaceData = data in
    let nargs = length args in
    let nparams = length data.oldParams in
    let addedArgs =
      if lti nargs nparams then
        let diff = subi nparams nargs in
        create diff (lam i.
          let idx = addi i nargs in
          let param : ParamData = get data.oldParams idx in
          FEVar {ident = nameSym "x", ty = param.1, info = info})
      else [] in
    let args = concat args addedArgs in
    let appArgs : [FutExpr] =
      join
        (map
          (lam argParam : (FutExpr, ParamData).
            let argExpr = argParam.0 in
            let param = argParam.1 in
            match mapLookup param.0 data.paramReplace with Some fields then
              mapValues
                (mapMapWithKey
                  (lam k : SID. lam v : ParamData.
                    FEProj {
                      target = argExpr, label = k, ty = v.1,
                      info = infoFutTm argExpr})
                  fields)
            else [argExpr])
          (zip args data.oldParams)) in
    let target = withTypeFutTm data.newType target in
    foldr
      (lam extraArg : FutExpr. lam acc : FutExpr.
        let info = mergeInfo (infoFutTm extraArg) (infoFutTm acc) in
        match extraArg with FEVar t then
          FELam {ident = t.ident, body = acc, info = info,
                 ty = FTyArrow {from = tyFutTm extraArg,
                                to = tyFutTm acc,
                                info = info}}
        else errorSingle [info] "")
      (_constructAppSeq target appArgs)
      addedArgs

  sem updateApplicationParameters : Map Name FunctionReplaceData -> FutExpr -> FutExpr
  sem updateApplicationParameters replaceMap =
  | FEVar t ->
    match mapLookup t.ident replaceMap with Some data then
      let data : FunctionReplaceData = data in
      updateParams data (FEVar t) [] t.info
    else FEVar t
  | app & (FEApp t) ->
    match _collectAppTargetAndArgs app with (target, args) in
    match target with FEVar {ident = id} then
      match mapLookup id replaceMap with Some data then
        updateParams data target args t.info
      else smap_FExpr_FExpr (updateApplicationParameters replaceMap) app
    else smap_FExpr_FExpr (updateApplicationParameters replaceMap) app
  | t -> smap_FExpr_FExpr (updateApplicationParameters replaceMap) t

  sem collectRecordFields (paramReplace : Map Name (Map SID ParamData)) =
  | FEVar t ->
    if mapMem t.ident paramReplace then
      mapRemove t.ident paramReplace
    else paramReplace
  | FEApp t ->
    match t.rhs with FEVar {ident = id} then
      if mapMem id paramReplace then
        mapRemove id (collectRecordFields paramReplace t.lhs)
      else sfold_FExpr_FExpr collectRecordFields paramReplace (FEApp t)
    else sfold_FExpr_FExpr collectRecordFields paramReplace (FEApp t)
  | FEProj t ->
    match t.target with FEVar {ident = id} then
      match mapLookup id paramReplace with Some usedFields then
        let fieldId = nameSym (concat (nameGetStr id) (sidToString t.label)) in
        let usedFields = mapInsert t.label (fieldId, t.ty) usedFields in
        mapInsert id usedFields paramReplace
      else sfold_FExpr_FExpr collectRecordFields paramReplace (FEProj t)
    else sfold_FExpr_FExpr collectRecordFields paramReplace (FEProj t)
  | FERecordUpdate t ->
    match t.rec with FEVar {ident = id} then
      mapRemove id paramReplace
    else paramReplace
  | t -> sfold_FExpr_FExpr collectRecordFields paramReplace t

  sem replaceProjections (paramReplace : Map Name (Map SID ParamData)) =
  | FEProj t ->
    match t.target with FEVar {ident = id} then
      match mapLookup id paramReplace with Some usedFields then
        match mapLookup t.label usedFields with Some data then
          let data : ParamData = data in
          FEVar {ident = data.0, ty = data.1, info = t.info}
        else
          -- NOTE(larshum 2021-10-29): This case should never be reached, as all
          -- record projections found here should also be found in the
          -- collection phase. If we were to get here, there is a bug in the
          -- implementation. What would be a good error message here?
          errorSingle [t.info] "Failed to replace record with its fields"
      else smap_FExpr_FExpr (replaceProjections paramReplace) (FEProj t)
    else smap_FExpr_FExpr (replaceProjections paramReplace) (FEProj t)
  | t -> smap_FExpr_FExpr (replaceProjections paramReplace) t

  sem liftRecordParametersDecl (replaceMap : Map Name FunctionReplaceData) =
  | FDeclFun t ->
    -- 1. Update calls to functions in body for which the parameters have been
    -- updated, by using the replaceMap.
    let body = updateApplicationParameters replaceMap t.body in

    -- 2. Collect record parameters of the function. Stop immediately if there
    -- are no such parameters.
    let paramReplace : Map Name (Map SID ParamData) =
      foldl
        (lam replace. lam param : (Name, FutType).
          match param.1 with FTyRecord _ then
            mapInsert param.0 (mapEmpty cmpSID) replace
          else replace)
        (mapEmpty nameCmp)
        t.params in
    if mapIsEmpty paramReplace then
      (replaceMap, FDeclFun {t with body = body})
    else
      -- 3. Collect record fields which should replace each record parameter. A
      -- record parameter should be replaced by a (subset) of its fields if it is
      -- only used in record projections. If no such parameters are found, the
      -- following steps are not necessary.
      let paramReplace = collectRecordFields paramReplace body in

      -- 4. Construct a new sequence of parameters by replacing record parameters
      -- with fields.
      let newParams : [(Name, FutType)] =
        join
          (map
            (lam param : (Name, FutType).
              match mapLookup param.0 paramReplace with Some fieldReplacements then
                map
                  (lam entry : (SID, ParamData). entry.1)
                  (mapBindings fieldReplacements)
              else [param])
            t.params) in

      -- 5. Replace applicable record projections on record parameters, in the
      -- function body, with the corresponding record field parameter.
      let newBody = replaceProjections paramReplace body in

      -- 6. Store the applied replacements of the function, so that we can
      -- easily update calls in step 1 on later functions.
      let newFunctionType =
        foldr
          (lam param : (Name, FutType). lam accType : FutType. 
            let info = mergeInfo (infoFutTy accType) (infoFutTy param.1) in
            FTyArrow {from = param.1, to = accType, info = info})
          t.ret newParams in
      let functionReplaceData = {
        newType = newFunctionType, oldParams = t.params,
        paramReplace = paramReplace} in
      let replaceMap = mapInsert t.ident functionReplaceData replaceMap in
      let declFun = FDeclFun {{t with params = newParams}
                                 with body = newBody} in
      (replaceMap, declFun)
  | t -> (replaceMap, t)

  sem liftRecordParameters =
  | FProg t ->
    let replaceMap : Map Name FunctionReplaceData = mapEmpty nameCmp in
    match mapAccumL liftRecordParametersDecl replaceMap t.decls
    with (_, decls) then
      FProg {t with decls = decls}
    else never
end

mexpr

use FutharkRecordParamLift in
use FutharkPrettyPrint in

let main = nameSym "main" in
let prog : [FutDecl] -> FutExpr -> FutProg = lam decls. lam mainBody.
  let mainDecl = FDeclFun {
    ident = main, entry = true, typeParams = [], params = [],
    ret = tyFutTm mainBody, body = mainBody, info = NoInfo ()
  } in
  FProg {decls = snoc decls mainDecl}
in

let f = nameSym "f" in
let r = nameSym "r" in
let x = nameSym "x" in
let a = nameSym "ra" in
let recordTy = futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)] in
let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = futIntTy_, info = NoInfo (),
  body = withTypeFutTm futIntTy_ (futRecordProj_ (nFutVar_ r) "a")} in
let mainBody = futBindall_ [
  nFutLet_ x recordTy (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]),
  futApp_ (nFutVar_ f) (withTypeFutTm recordTy (nFutVar_ x))] in
let projOneField = prog [fDecl] mainBody in

let fDeclFieldOnly = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(a, futIntTy_)],
  ret = futIntTy_, info = NoInfo (),
  body = nFutVar_ a} in
let mainFieldBody = futBindall_ [
  nFutLet_ x recordTy (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]),
  futApp_ (nFutVar_ f) (futRecordProj_ (nFutVar_ x) "a")] in
let expected = prog [fDeclFieldOnly] mainFieldBody in

utest printFutProg (liftRecordParameters projOneField)
with printFutProg expected using eqString in

-- NOTE(larshum, 2021-10-31): For simplicity, even if all fields of a record
-- parameter are used in projections within the function, the record is lifted.
let b = nameSym "rb" in
let fDeclAll = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = futIntTy_, info = NoInfo (),
  body = withTypeFutTm futIntTy_ (
    futAdd_
      (withTypeFutTm futIntTy_ (futRecordProj_ (nFutVar_ r) "a"))
      (futApp_ (futConst_ (FCFloat2Int ()))
               (withTypeFutTm futFloatTy_ (futRecordProj_ (nFutVar_ r) "b"))))} in
let projAllFields = prog [fDeclAll] mainBody in

let fDeclAllFields = FDeclFun {
  ident = f, entry = false, typeParams = [], ret = futIntTy_, info = NoInfo (),
  params = [(a, futIntTy_), (b, futFloatTy_)],
  body = withTypeFutTm futIntTy_ (
    futAdd_
      (nFutVar_ a)
      (futApp_ (futConst_ (FCFloat2Int ()))
               (nFutVar_ b)))} in
let mainAllBody = futBindall_ [
  nFutLet_ x recordTy (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]),
  futAppSeq_ (nFutVar_ f)
    [ futRecordProj_ (nFutVar_ x) "a",
      futRecordProj_ (nFutVar_ x) "b" ]] in
let expected = prog [fDeclAllFields] mainAllBody in

utest printFutProg (liftRecordParameters projAllFields)
with printFutProg expected using eqString in

let fRecordUpdate = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = recordTy, info = NoInfo (),
  body = futRecordUpdate_ (nFutVar_ r) "a" (futInt_ 2)} in
let recordUpdate = prog [fRecordUpdate] mainBody in

utest printFutProg (liftRecordParameters recordUpdate)
with printFutProg recordUpdate using eqString in

let g = nameSym "g" in
let gDeclAppProj = FDeclFun {
  ident = g, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = futIntTy_, info = NoInfo (),
  body = withTypeFutTm futIntTy_ (futRecordProj_ (nFutVar_ r) "a")} in
let fDeclCallG = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = futIntTy_, info = NoInfo (),
  body = futApp_ (nFutVar_ g) (nFutVar_ r)} in
let functionAppWithProj = prog [gDeclAppProj, fDeclCallG] mainBody in

let a2 = nameSym "ra" in
let gDeclAppVar = FDeclFun {
  ident = g, entry = false, typeParams = [], params = [(a, futIntTy_)],
  ret = futIntTy_, info = NoInfo (),
  body = nFutVar_ a} in
let fDeclCallGField = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(a2, futIntTy_)],
  ret = futIntTy_, info = NoInfo (),
  body = futApp_ (nFutVar_ g) (nFutVar_ a2)} in
let expected = prog [gDeclAppVar, fDeclCallGField] mainFieldBody in

utest printFutProg (liftRecordParameters functionAppWithProj)
with printFutProg expected using eqString in

let x = nameSym "x" in
let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [], ret = futIntTy_, info = NoInfo (),
  params = [(x, futIntTy_), (r, recordTy)],
  body =
    futAdd_
      (nFutVar_ x)
      (withTypeFutTm futIntTy_ (futRecordProj_ (nFutVar_ r) "a"))} in
let gDecl = FDeclFun {
  ident = g, entry = false, typeParams = [], params = [], info = NoInfo (),
  ret = futArrowTy_ recordTy futIntTy_,
  body = futApp_ (nFutVar_ f) (futInt_ 1)} in
let mainBody =
  futApp_
    (nFutVar_ g)
    (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]) in
let partialApp = prog [fDecl, gDecl] mainBody in

let x2 = nameSym "x" in
let fDeclField = FDeclFun {
  ident = f, entry = false, typeParams = [], ret = futIntTy_, info = NoInfo (),
  params = [(x, futIntTy_), (a, futIntTy_)],
  body = futAdd_ (nFutVar_ x) (nFutVar_ a)} in
let gDeclWrapped = FDeclFun {
  ident = g, entry = false, typeParams = [], params = [], info = NoInfo (),
  ret = futArrowTy_ recordTy futIntTy_,
  body = nFutLam_ x2 (
    futAppSeq_ (nFutVar_ f) [futInt_ 1, futRecordProj_ (nFutVar_ x2) "a"])} in
let expected = prog [fDeclField, gDeclWrapped] mainBody in

utest printFutProg (liftRecordParameters partialApp)
with printFutProg expected using eqString in

()
