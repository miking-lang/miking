
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

  sem eliminateTensorCopying
    : Map Name AccelerateData -> Expr -> Map Name AccelerateData
  sem eliminateTensorCopying accelerateData =
  | t ->
    let env = initCopyAnalysisEnv accelerateData in
    let env = findUninitializedTensorParameters env t in
    env.accelerateData

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
