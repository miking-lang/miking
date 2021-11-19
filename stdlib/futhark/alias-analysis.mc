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
          -- TODO: recurse through pattern and alias result together, and add
          -- aliases as they are found (recursion needed because we may have
          -- nested records here)
          env
        else env
      else env in
    aliasAnalysisExpr env body
  | FEArray _
  | FEApp {lhs = FEConst {val = FCIota () | FCIndices ()}}
  | FEApp {lhs = FEApp {lhs = FEConst {val = FCMap () | FCTabulate () |
                                             FCReplicate () | FCConcat ()}}}
  | FEApp {lhs = FEApp {lhs = FEApp {lhs = FEConst {val = FCMap2 ()}}}} ->
    -- NOTE(larshum, 2021-11-19): The below expressions introduce a new array.
    let arrayId = nameSym "" in
    (LeafAliasResult arrayId, env)
  | t -> (EmptyAliasResult (), env)

  sem aliasAnalysisExpr (env : FutharkAliasAnalysisEnv) =
  | FELet t ->
    -- NOTE(larshum, 2021-11-19): We also need to update the counter here
    match aliasAnalysisLetBody env t.body with (result, env) in
    let env : FutharkAliasAnalysisEnv = env in
    let env = {env with aliases = mapInsert t.ident result env.aliases} in
    aliasAnalysisExpr env t.inexpr
  | FEVar t ->
    match mapLookup t.ident env.aliases with Some result then
      if setMem t.ident env.expired then (EmptyAliasResult (), env)
      else (result, env)
    else (EmptyAliasResult (), env)
  | t -> (EmptyAliasResult (), env)

  sem eliminateCopyInArrayUpdate (env : FutharkAliasAnalysisEnv)
                                 (safeArrays : Set Name) =
  | FEArrayUpdate ({array = FEApp {lhs = FEConst {val = FCCopy ()},
                                   rhs = FEVar ({ident = updateId} & var)}} & t) ->
    match mapLookup updateId env.aliases with Some (LeafAliasResult arrayId) then
      if setMem arrayId safeArrays then
        printLn (join ["Eliminated copy of in-place array update"]);
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

()
