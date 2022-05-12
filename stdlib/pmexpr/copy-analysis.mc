
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"

-- Performs an analysis to determine whether copying of tensors can be omitted.
-- This analysis is currently only applied on top-level expressions.
lang PMExprCopyAnalysis = PMExprAst + PMExprExtractAccelerate
  type CopyAnalysisEnv = {
    accelerateData : Map Name AccelerateData,
    usedAfter : Set Name,
    uninit : Set Name
  }

  sem initCopyAnalysisEnv : Map Name AccelerateData -> CopyAnalysisEnv
  sem initCopyAnalysisEnv =
  | accelerateData ->
    { accelerateData = accelerateData, usedAfter = setEmpty nameCmp
    , uninit = setEmpty nameCmp }

  sem findUnusedAfterAccelerate : Map Name AccelerateData -> Expr -> Map Name AccelerateData
  sem findUnusedAfterAccelerate accelerateData =
  | t ->
    let env = initCopyAnalysisEnv accelerateData in
    let env = findUnusedAfterAccelerateH env t in
    let env : CopyAnalysisEnv = findUninitializedTensorParameters env t in
    env.accelerateData

  sem findUnusedAfterAccelerateH : CopyAnalysisEnv -> Expr -> CopyAnalysisEnv
  sem findUnusedAfterAccelerateH env =
  | TmLet (t & {body = TmLam _}) ->
    let env = findUnusedAfterAccelerateH env t.inexpr in
    findUsedInExpr env t.body
  | TmLet t ->
    let env : CopyAnalysisEnv = findUnusedAfterAccelerateH env t.inexpr in
    let f = lam x : (CopyStatus, Expr).
      match x with (copyStatus, arg) in
      match arg with TmVar {ident = ident} then
        -- NOTE(larshum, 2022-04-11): If the identifier is not used after the
        -- accelerate call, we don't have to copy it back from the accelerated
        -- code. Assumes we're on the top-level only.
        if setMem ident env.usedAfter then copyStatus
        else omitCopyFrom copyStatus
      else copyStatus
    in
    match collectAppArguments t.body with (fun, args) in
    match fun with TmVar {ident = ident} then
      match mapLookup ident env.accelerateData with Some ad then
        let ad : AccelerateData = ad in
        let copyStatus = map f (zip ad.paramCopyStatus args) in
        let ad = {ad with paramCopyStatus = copyStatus} in
        let accelerateData = mapInsert ident ad env.accelerateData in
        let env = {env with accelerateData = accelerateData} in
        findUsedInExpr env t.body
      else findUsedInExpr env t.body
    else findUsedInExpr env t.body
  | TmRecLets t ->
    let findUnusedAfterAccelerateBind = lam env. lam bind : RecLetBinding.
      findUsedInExpr env bind.body
    in
    let env = findUnusedAfterAccelerateH env t.inexpr in
    foldl findUnusedAfterAccelerateBind env t.bindings
  | TmType t -> findUnusedAfterAccelerateH env t.inexpr
  | TmConDef t -> findUnusedAfterAccelerateH env t.inexpr
  | TmUtest t -> findUnusedAfterAccelerateH env t.next
  | TmExt t -> findUnusedAfterAccelerateH env t.inexpr
  | t -> findUsedInExpr env t

  sem findUsedInExpr : CopyAnalysisEnv -> Expr -> CopyAnalysisEnv
  sem findUsedInExpr env =
  | TmVar t ->
    let env : CopyAnalysisEnv = env in
    {env with usedAfter = setInsert t.ident env.usedAfter}
  | t -> sfold_Expr_Expr findUsedInExpr env t

  sem findUninitializedTensorParameters : CopyAnalysisEnv -> Expr -> CopyAnalysisEnv
  sem findUninitializedTensorParameters env =
  | TmLet (t & {body = TmLam _}) ->
    findUninitializedTensorParameters env t.inexpr
  | TmLet (t & {body = TmApp {
      lhs = TmConst {val = CTensorCreateUninitInt _ |
                           CTensorCreateUninitFloat _}}}) ->
    let env : CopyAnalysisEnv = env in
    let env = {env with uninit = setInsert t.ident env.uninit} in
    findUninitializedTensorParameters env t.inexpr
  | TmLet t ->
    let env : CopyAnalysisEnv = env in
    let f = lam x : (CopyStatus, Expr).
      match x with (status, arg) in
      match arg with TmVar {ident = ident} then
        -- NOTE(larshum, 2022-04-11): Omit copying values to the accelerated
        -- code if they contain uninitialized values (currently only applies to
        -- tensor data).
        if setMem ident env.uninit then omitCopyTo status
        else status
      else status
    in
    match collectAppArguments t.body with (fun, args) in
    let env =
      match fun with TmVar {ident = ident} then
        match mapLookup ident env.accelerateData with Some ad then
          let ad : AccelerateData = ad in
          let copyStatus = map f (zip ad.paramCopyStatus args) in
          let ad = {ad with paramCopyStatus = copyStatus} in
          let accelerateData = mapInsert ident ad env.accelerateData in
          {env with accelerateData = accelerateData}
        else env
      else env
    in
    findUninitializedTensorParameters env t.inexpr
  | TmRecLets t -> findUninitializedTensorParameters env t.inexpr
  | TmType t -> findUninitializedTensorParameters env t.inexpr
  | TmConDef t -> findUninitializedTensorParameters env t.inexpr
  | TmUtest t -> findUninitializedTensorParameters env t.next
  | TmExt t -> findUninitializedTensorParameters env t.inexpr
  | _ -> env
end
