-- Finds record parameters which are only used in projections, and replaces
-- such record parameters with parameters represeting the projected fields.
--
-- This transformation is important for aliasing reasons. If we only use a
-- subset of the fields in a record, but the full record is passed, then all
-- fields will be considered aliased. This may prevent elimination of
-- unnecessary copying in in-place updates, which may significantly degrade the
-- performance.

include "stringid.mc"
include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

type ParamData = (Name, FutType)

type FunctionReplaceData = {
  -- Contains the type of the function after replacing record parameters with a
  -- record field parameters.
  newType : FutType,

  -- Contains the new sequence of parameters to the function.
  newParams : [ParamData],

  -- Maps the name of a replaced record parameter to the parameters of the
  -- fields that replaced it.
  paramReplace : Map Name (Map SID ParamData)
}

lang FutharkReplaceRecordParamWithFields = FutharkAst
  sem collectAppTargetAndArgs (args : [FutExpr]) =
  | FEApp {lhs = !(FEApp _) & lhs, rhs = rhs} ->
    (lhs, cons rhs args)
  | FEApp t ->
    collectAppTargetAndArgs (cons t.rhs args) t.lhs
  | t -> (t, args)

  sem updateApplicationParameters (replaceMap : Map Name FunctionReplaceData) =
  | FEApp t ->
    match collectAppTargetAndArgs [] (FEApp t) with (target, params) then
      -- TODO(larshum, 2021-10-29): Use the collected
      FEApp t
    else never
  | t -> smap_FExpr_FExpr (updateApplicationParameters replaceMap) t

  sem collectRecordFields (paramReplace : Map Name (Map SID ParamData)) =
  | FEApp t ->
    match t.rhs with FEVar {ident = id} then
      -- NOTE(larshum, 2021-10-29): Passing a record parameter to another
      -- function means all its fields are indirectly used.
      if mapMem id paramReplace then
        mapRemove id (collectRecordFields paramReplace t.lhs)
      else sfold_FExpr_FExpr collectRecordFields paramReplace (FEApp t)
    else sfold_FExpr_FExpr collectRecordFields paramReplace (FEApp t)
  | FERecordProj t ->
    match t.rec with FEVar {ident = id} then
      match mapLookup id paramReplace with Some usedFields then
        let fieldId = nameSym (concat (nameGetStr id) (sidToString t.key)) in
        let usedFields = mapInsert t.key (fieldId, t.ty) usedFields in
        mapInsert id usedFields paramReplace
      else sfold_FExpr_FExpr collectRecordFields paramReplace (FERecordProj t)
    else sfold_FExpr_FExpr collectRecordFields paramReplace (FERecordProj t)
  | FERecordUpdate t ->
    -- NOTE(larshum, 2021-10-29): A record update indirectly involves all
    -- fields of the record.
    match t.rec with FEVar {ident = id} then
      mapRemove id paramReplace
    else paramReplace
  | t -> sfold_FExpr_FExpr collectRecordFields paramReplace t

  sem replaceProjections (paramReplace : Map Name (Map SID ParamData)) =
  | FERecordProj t ->
    match t.rec with FEVar {ident = id} then
      match mapLookup id paramReplace with Some usedFields then
        match mapLookup t.key usedFields with Some data then
          let data : ParamData = data in
          FEVar {ident = data.0, ty = data.1, info = t.info}
        else
          -- TODO(larshum 2021-10-29): This case should never be reached, as all
          -- record projections found here should also be found in the
          -- collection phase. If we were to get here, there is a bug in the
          -- implementation. What would be a good error message here?
          infoErrorExit t.info "Failed to replace record with its fields"
      else smap_FExpr_FExpr (replaceProjections paramReplace) (FERecordProj t)
    else smap_FExpr_FExpr (replaceProjections paramReplace) (FERecordProj t)
  | t -> smap_FExpr_FExpr (replaceProjections paramReplace) t

  sem replaceRecordParametersDecl (replaceMap : Map Name FunctionReplaceData) =
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
      (replaceMap, FDeclFun t)
    else
      -- 3. Collect record fields which should replace each record parameter. A
      -- record parameter should be replaced by a (subset) of its fields if it is
      -- only used in record projections. If no such parameters are found, the
      -- following steps are not necessary.
      let paramReplace = collectRecordFields paramReplace t.body in

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
      let newBody = replaceProjections paramReplace t.body in

      -- 6. Store the applied replacements of the function, so that we can
      -- easily update calls in step 1 on later functions.
      let newFunctionType =
        foldr
          (lam param : (Name, FutType). lam accType : FutType. 
            let info = mergeInfo (infoFutTy accType) (infoFutTy param.1) in
            FTyArrow {from = param.1, to = accType, info = info})
          t.ret newParams in
      let functionReplaceData = {
        newType = newFunctionType, newParams = newParams,
        paramReplace = paramReplace} in
      let replaceMap = mapInsert t.ident functionReplaceData replaceMap in
      let declFun = FDeclFun {{t with params = newParams}
                                 with body = newBody} in
      (replaceMap, declFun)
  | t -> (t, replaceMap)

  sem replaceRecordParameters =
  | FProg t ->
    let replaceMap : Map Name FunctionReplaceData = mapEmpty nameCmp in
    match mapAccumL replaceRecordParametersDecl replaceMap t.decls
    with (_, decls) then
      FProg {t with decls = decls}
    else never
end

mexpr

use FutharkReplaceRecordParamWithFields in
use FutharkPrettyPrint in

let main = nameSym "main" in
let prog : [FutDecl] -> FutExpr -> FutProg = lam decls. lam mainBody.
  let mainDecl = FDeclFun {
    ident = main, entry = true, typeParams = [], params = [],
    ret = tyFutTm mainBody, body = mainBody, info = NoInfo ()
  } in
  FProg {decls = snoc decls mainDecl}
in

-- NOTE(larshum, 2021-10-29): Should replace this with an example in PMExpr
-- which is translated to Futhark, so that we can rely on type annot to
-- propagate types as expected.
let f = nameSym "f" in
let r = nameSym "r" in
let x = nameSym "x" in
let a = nameSym "ra" in
let recordTy = futRecordTy_ [("a", futIntTy_), ("b", futFloatTy_)] in
let fDecl = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(r, recordTy)],
  ret = futIntTy_, info = NoInfo (),
  body = withTypeFutTm futIntTy_ (futRecordProj_ (nFutVar_ r) "a")} in
let fDeclFieldOnly = FDeclFun {
  ident = f, entry = false, typeParams = [], params = [(a, futIntTy_)],
  ret = futIntTy_, info = NoInfo (),
  body = nFutVar_ a} in
let projOneField = prog [fDecl] (futBindall_ [
  nFutLet_ x recordTy (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]),
  futApp_ (nFutVar_ f) (nFutVar_ x)
]) in

let expected = prog [fDeclFieldOnly] (futBindall_ [
  nFutLet_ x recordTy (futRecord_ [("a", futInt_ 4), ("b", futFloat_ 2.5)]),
  futApp_ (nFutVar_ f) (futRecordProj_ (nFutVar_ x) "a")
]) in

printLn "";
printLn (printFutProg (replaceRecordParameters projOneField));
printLn (printFutProg expected);
--utest printFutProg (replaceRecordParameters projOneField)
--with printFutProg expected using eqString in

()
