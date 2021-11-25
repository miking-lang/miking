-- Performs a very conservative form of alias analysis of arrays in Futhark AST
-- to identify places where copying of an array in-place update can be
-- eliminated.
--
-- Note that PMExpr does not support expressing that an array is unique. Thus,
-- we have to assume all array parameters are aliased. As a consequence, we can
-- only eliminate the copy for an array that is initialized within the local
-- function.

include "futhark/ast.mc"
include "futhark/ast-builder.mc"
include "futhark/pprint.mc"

type Alias
con AliasName : Name -> Alias
con AliasField : (Alias, SID) -> Alias

recursive let aliasCmp = lam l : Alias. lam r : Alias.
  let t = (l, r) in
  match t with (AliasName ln, AliasName rn) then nameCmp ln rn
  else match t with (AliasField lf, AliasField rf) then
    let c = aliasCmp lf.0 rf.0 in
    if eqi c 0 then cmpSID lf.1 rf.1
    else c
  else subi (constructorTag l) (constructorTag r)
end

-- We use names to represent a unique array value within the local function.
type ArrayID = Name

type AliasResult
con EmptyAliasResult : () -> AliasResult
con LeafAliasResult : ArrayID -> AliasResult
con RecordAliasResult : Map SID AliasResult -> AliasResult

let getAliasResultIdentifiers : AliasResult -> Set Name = lam r.
  recursive let work = lam acc : Set Name. lam result : AliasResult.
    match result with EmptyAliasResult () then acc
    else match result with LeafAliasResult arrayId then
      setInsert arrayId acc
    else match result with RecordAliasResult binds then
      mapFoldWithKey
        (lam acc : Set Name. lam. lam v : AliasResult. work acc v)
        acc binds
    else never
  in work (setEmpty nameCmp) r
  
type FutharkAliasAnalysisEnv = {
  -- Maps an identifier to the value or values it is mapped to, depending on
  -- whether it represents a record or a base type.
  aliases : Map Name AliasResult,

  -- Set of expired identifiers that may not be used in future parts of the
  -- program.
  expired : Set Name,

  -- Maintains a set of chains that have been used for in-place updates. As a
  -- way to simplify the analysis, a chain may be used in at most one in-place
  -- update.
  inPlaceUpdates : Set ArrayID
}

recursive let addBindingAliasesToEnv = use FutharkAst in
  lam env : FutharkAliasAnalysisEnv.
  lam pat : FutPat. lam alias : AliasResult.
  let t = (pat, alias) in
  match t with (FPRecord {bindings = patBinds}, RecordAliasResult aliasBinds) then
    mapFoldWithKey
      (lam env. lam k : SID. lam alias : AliasResult.
        match mapLookup k patBinds with Some pat then
          addBindingAliasesToEnv env pat alias
        else env)
      env aliasBinds
  else match t with (FPNamed {ident = PName id}, result) then
    {env with aliases = mapInsert id result env.aliases}
  else env
end

lang FutharkAliasAnalysis = FutharkAst
  sem aliasAnalysisLetBody (env : FutharkAliasAnalysisEnv) =
  | FEVar t ->
    match mapLookup t.ident env.aliases with Some result then
      (result, {env with expired = setInsert t.ident env.expired})
    else (EmptyAliasResult (), env)
  | FERecord t ->
    match
      mapFoldWithKey
        (lam acc. lam k : SID. lam v : FutExpr.
          match acc with (aliasResult, env) in
          match aliasAnalysisLetBody env v with (fieldResult, env) in
          (mapInsert k fieldResult aliasResult, env))
        (mapEmpty cmpSID, env) t.fields
    with (binds, env) in
    (RecordAliasResult binds, env)
  | FEArrayAccess {array = FEVar {ident = _}, index = index} ->
    -- NOTE(larshum, 2021-11-24): This operation does not alias the accessed
    -- array.
    aliasAnalysisLetBody env index
  | FEArrayUpdate {array = FEApp {lhs = FEConst {val = FCCopy ()},
                                  rhs = FEVar {ident = updateId}},
                   value = value} ->
    match aliasAnalysisLetBody env value with (_, env) in
    let env : FutharkAliasAnalysisEnv = env in
    match mapLookup updateId env.aliases with Some result then
      if setMem updateId env.expired then (EmptyAliasResult (), env)
      else
        match result with LeafAliasResult arrayId then
          let env : FutharkAliasAnalysisEnv = env in
          -- NOTE(larshum, 2021-11-19): We only allow at most one in-place
          -- update per array alias, to simplify implementation.
          if setMem arrayId env.inPlaceUpdates then (EmptyAliasResult (), env)
          else
            let inPlaceUpdates = setInsert arrayId env.inPlaceUpdates in
            let env = {{env with inPlaceUpdates = inPlaceUpdates}
                            with expired = setInsert updateId env.expired} in
            (result, env)
        else (EmptyAliasResult (), env)
    else (EmptyAliasResult (), env)
  | FEForEach {param = (pat, FEVar {ident = accId}),
               seq = FEVar {ident = seqId}, body = body} ->
    let env =
      match mapLookup seqId env.aliases with Some (LeafAliasResult _) then
        -- NOTE(larshum, 2021-11-19): If we iterate over an array in a
        -- for-loop, it cannot be used for in-place updates within the loop, so
        -- we conservatively mark it as expired.
        {env with expired = setInsert seqId env.expired}
      else env in
    let env =
      match mapLookup accId env.aliases with Some result then
        let t = (pat, result) in
        match t with (FPNamed {ident = PName id}, LeafAliasResult _) then
          {{env with aliases = mapInsert id result env.aliases}
                with expired = setInsert accId env.expired}
        else match t with (FPRecord t, RecordAliasResult binds) then
          let env = {env with expired = setInsert accId env.expired} in
          addBindingAliasesToEnv env pat result
        else env
      else env in
    aliasAnalysisExpr env body
  | FEApp {lhs = FEConst {val = FCFlatten ()}, rhs = FEVar {ident = id}} ->
    match mapLookup id env.aliases with Some aliasResult then
      (aliasResult, env)
    else (EmptyAliasResult (), env)
  | FEArray _
  | FEApp {lhs = FEConst {val = FCIota () | FCIndices ()}}
  | FEApp {lhs = FEApp {lhs = FEConst {val = FCMap () | FCTabulate () |
                                             FCReplicate () | FCConcat ()}}}
  | FEApp {lhs = FEApp {lhs = FEApp {lhs = FEConst {val = FCMap2 ()}}}} ->
    -- NOTE(larshum, 2021-11-19): The above intrinsics introduce a fresh array,
    -- which is guaranteed not to be aliased. We create a new identifier to
    -- represent this underlying array.
    let arrayId = nameSym "" in
    (LeafAliasResult arrayId, env)
  | t ->
    -- NOTE(larshum, 2021-11-19: For other kinds of expressions, it is possible
    -- that multiple aliases of the same array are created. To be conservative,
    -- we ignore the resulting array identifiers, but update the environment to
    -- take any variables used in the expression into account.
    let f = lam env. lam t : FutExpr.
      match aliasAnalysisLetBody env t with (_, env) in
      env
    in
    let env = sfold_FExpr_FExpr f env t in
    (EmptyAliasResult (), env)

  sem aliasAnalysisExpr (env : FutharkAliasAnalysisEnv) =
  | FELet t ->
    match aliasAnalysisLetBody env t.body with (result, env) in
    let env : FutharkAliasAnalysisEnv = env in
    let env = {env with aliases = mapInsert t.ident result env.aliases} in
    aliasAnalysisExpr env t.inexpr
  | FEVar t ->
    match mapLookup t.ident env.aliases with Some result then
      if setMem t.ident env.expired then (EmptyAliasResult (), env)
      else (result, env)
    else (EmptyAliasResult (), env)
  | FERecord t ->
    match
      mapFoldWithKey
        (lam acc. lam k : SID. lam v : FutExpr.
          match acc with (aliasResult, env) in
          match aliasAnalysisLetBody env v with (fieldResult, env) in
          (mapInsert k fieldResult aliasResult, env))
        (mapEmpty cmpSID, env) t.fields
    with (binds, env) in
    (RecordAliasResult binds, env)
  | t -> (EmptyAliasResult (), env)

  sem eliminateCopyInArrayUpdate (env : FutharkAliasAnalysisEnv)
                                 (safeArrays : Set Name) =
  | FEArrayUpdate ({array = FEApp {lhs = FEConst {val = FCCopy ()},
                                   rhs = FEVar ({ident = updateId} & var)}} & t) ->
    match mapLookup updateId env.aliases with Some (LeafAliasResult arrayId) then
      if setMem arrayId safeArrays then
        FEArrayUpdate {t with array = FEVar var}
      else FEArrayUpdate t
    else FEArrayUpdate t
  | t -> smap_FExpr_FExpr (eliminateCopyInArrayUpdate env safeArrays) t

  sem aliasAnalysisDecl =
  | FDeclFun t ->
    let emptyEnv : FutharkAliasAnalysisEnv = {
      aliases = mapEmpty nameCmp,
      expired = setEmpty nameCmp,
      inPlaceUpdates = setEmpty nameCmp} in
    match aliasAnalysisExpr emptyEnv t.body with (res, env) in
    let env : FutharkAliasAnalysisEnv = env in
    -- NOTE(larshum, 2021-11-19): Use the array identifiers of the resulting
    -- term and the environment to determine which, if any, in-place array
    -- updates can have their copy expression eliminated.
    let resultIdents = setToSeq (getAliasResultIdentifiers res) in
    let safeIdents =
      foldl
        (lam acc. lam ident : Name.
          if setMem ident env.inPlaceUpdates then
            setInsert ident acc
          else acc)
        (setEmpty nameCmp) resultIdents in
    let body = eliminateCopyInArrayUpdate env safeIdents t.body in
    FDeclFun {t with body = body}
  | t -> t

  sem aliasAnalysis =
  | FProg t ->
    FProg {t with decls = map aliasAnalysisDecl t.decls}
end

mexpr

use FutharkAliasAnalysis in
use FutharkPrettyPrint in

let f = nameSym "f" in
let s = nameSym "s" in
let prog = lam body : FutExpr.
  let decl = FDeclFun {
    ident = f, entry = false, typeParams = [],
    params = [(s, futUnsizedArrayTy_ futIntTy_)], info = NoInfo (),
    ret = futUnsizedArrayTy_ futIntTy_, body = body} in
  FProg {decls = [decl]}
in

let t1 = futArrayUpdate_ (futCopy_ (nFutVar_ s)) (futInt_ 0) (futInt_ 0) in
utest printFutProg (aliasAnalysis (prog t1)) with printFutProg (prog t1)
using eqString in

let idx = nameSym "idx" in
let i = nameSym "i" in
let t = nameSym "t" in
let tt = nameSym "t1" in
let ttt = nameSym "t2" in
let t2 = futBindall_ [
  nFutLet_ idx (futUnsizedArrayTy_ futIntTy_) (futIndices_ (nFutVar_ s)),
  nFutLet_ t (futUnsizedArrayTy_ futIntTy_) (
    futForEach_ (nFutPvar_ ttt, nFutVar_ s) i (nFutVar_ idx) (futBindall_ [
      nFutLet_ tt (futUnsizedArrayTy_ futIntTy_) (
        futArrayUpdate_ (futCopy_ (nFutVar_ ttt)) (futInt_ 0) (futInt_ 0)),
      nFutVar_ tt])),
  nFutVar_ t] in
utest printFutProg (aliasAnalysis (prog t2)) with printFutProg (prog t2)
using eqString in

let s2 = nameSym "s2" in
let t3 = futBindall_ [
  nFutLet_ s2 (futUnsizedArrayTy_ futIntTy_) (
    futReplicate_ (futLength_ (nFutVar_ s)) (futInt_ 1)),
  nFutLet_ idx (futUnsizedArrayTy_ futIntTy_) (futIndices_ (nFutVar_ s)),
  nFutLet_ t (futUnsizedArrayTy_ futIntTy_) (
    futForEach_ (nFutPvar_ ttt, nFutVar_ s2) i (nFutVar_ idx) (futBindall_ [
      nFutLet_ tt (futUnsizedArrayTy_ futIntTy_) (
        futArrayUpdate_ (futCopy_ (nFutVar_ ttt)) (futInt_ 0) (futInt_ 0)),
      nFutVar_ tt])),
  nFutVar_ t] in
let expected = futBindall_ [
  nFutLet_ s2 (futUnsizedArrayTy_ futIntTy_) (
    futReplicate_ (futLength_ (nFutVar_ s)) (futInt_ 1)),
  nFutLet_ idx (futUnsizedArrayTy_ futIntTy_) (futIndices_ (nFutVar_ s)),
  nFutLet_ t (futUnsizedArrayTy_ futIntTy_) (
    futForEach_ (nFutPvar_ ttt, nFutVar_ s2) i (nFutVar_ idx) (futBindall_ [
      nFutLet_ tt (futUnsizedArrayTy_ futIntTy_) (
        futArrayUpdate_ (nFutVar_ ttt) (futInt_ 0) (futInt_ 0)),
      nFutVar_ tt])),
  nFutVar_ t] in
utest printFutProg (aliasAnalysis (prog t3)) with printFutProg (prog expected)
using eqString in

let r = nameSym "r" in
let arrayTy = futUnsizedArrayTy_ futIntTy_ in
let recTy = futRecordTy_ [("a", arrayTy), ("b", arrayTy)] in
let a = nameSym "a" in
let b = nameSym "b" in
let recPat = futPrecord_ [
  ("a", nFutPvar_ a),
  ("b", nFutPvar_ b)] in
let t4 = futBindall_ [
  nFutLet_ r recTy (
    futRecord_ [
      ("a", futIota_ (nFutVar_ s)),
      ("b", futArraySlice_ (nFutVar_ s) (futInt_ 0) (futInt_ 3))]),
  nFutLet_ idx arrayTy (futIndices_ (nFutVar_ s)),
  nFutLet_ t recTy (
    futForEach_ (recPat, nFutVar_ r) i (nFutVar_ idx) (futBindall_ [
      nFutLet_ tt arrayTy (
        futArrayUpdate_ (futCopy_ (nFutVar_ a)) (futInt_ 0) (futInt_ 1)),
      nFutLet_ ttt arrayTy (
        futArrayUpdate_ (futCopy_ (nFutVar_ b)) (futInt_ 0) (futInt_ 1)),
      futRecord_ [("a", nFutVar_ tt), ("b", nFutVar_ ttt)]])),
  nFutVar_ t] in
let expected = futBindall_ [
  nFutLet_ r recTy (
    futRecord_ [
      ("a", futIota_ (nFutVar_ s)),
      ("b", futArraySlice_ (nFutVar_ s) (futInt_ 0) (futInt_ 3))]),
  nFutLet_ idx arrayTy (futIndices_ (nFutVar_ s)),
  nFutLet_ t recTy (
    futForEach_ (recPat, nFutVar_ r) i (nFutVar_ idx) (futBindall_ [
      nFutLet_ tt arrayTy (
        futArrayUpdate_ (nFutVar_ a) (futInt_ 0) (futInt_ 1)),
      nFutLet_ ttt arrayTy (
        futArrayUpdate_ (futCopy_ (nFutVar_ b)) (futInt_ 0) (futInt_ 1)),
      futRecord_ [("a", nFutVar_ tt), ("b", nFutVar_ ttt)]])),
  nFutVar_ t] in
utest printFutProg (aliasAnalysis (prog t4)) with printFutProg (prog expected)
using eqString in

let f = nameSym "f" in
let passArrayAliasToFunction = futBindall_ [
  nFutLet_ s2 arrayTy (futReplicate_ (futLength_ (nFutVar_ s)) (futInt_ 1)),
  nFutLet_ t arrayTy (futApp_ (nFutVar_ f) (nFutVar_ s2)),
  nFutLet_ tt arrayTy (futArrayUpdate_ (futCopy_ (nFutVar_ s2)) (futInt_ 0) (futInt_ 1)),
  nFutVar_ tt] in
utest printFutProg (aliasAnalysis (prog passArrayAliasToFunction))
with printFutProg (prog passArrayAliasToFunction)
using eqString in

()
