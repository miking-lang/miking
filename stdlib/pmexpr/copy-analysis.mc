
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"
include "pmexpr/utils.mc"

-- Performs analyses to determine whether copying of tensors can be omitted. The
-- current implementation only applies to tensors used in very specific ways,
-- and only considers the top-level of the code.
lang PMExprTensorCopyAnalysis = PMExprAst + PMExprExtractAccelerate
  type CopyAnalysisEnv = {
    accelerateData : Map Name AccelerateData,
    uninitTensors : Set Name
  }

  sem initCopyAnalysisEnv : Map Name AccelerateData -> Expr -> CopyAnalysisEnv
  sem initCopyAnalysisEnv accelerateData =
  | t ->
    { accelerateData = accelerateData
    , uninitTensors = findUninitializedTensors (setEmpty nameCmp) t }

  -- Finds the identifiers of tensors that are allocated using the
  -- uninitialized constants.
  sem findUninitializedTensors : Set Name -> Expr -> Set Name
  sem findUninitializedTensors tensors =
  | TmLet t ->
    let tensors =
      match t.body with TmApp {lhs = TmConst {val = CTensorCreateUninitInt _ |
                                                    CTensorCreateUninitFloat _}} then
        setInsert t.ident tensors
      else tensors in
    findUninitializedTensors tensors t.inexpr
  | TmRecLets t -> findUninitializedTensors tensors t.inexpr
  | TmType t -> findUninitializedTensors tensors t.inexpr
  | TmConDef t -> findUninitializedTensors tensors t.inexpr
  | TmUtest t -> findUninitializedTensors tensors t.next
  | TmExt t -> findUninitializedTensors tensors t.inexpr
  | _ -> tensors

  sem eliminateTensorCopying
    : Map Name AccelerateData -> Expr -> Map Name AccelerateData
  sem eliminateTensorCopying accelerateData =
  | t ->
    let env = initCopyAnalysisEnv accelerateData t in
    let env = omitCopyUninitialized env t in
    let env = findAccelerateExclusiveTensors env t in
    env.accelerateData

  -- Omits copying tensors that are uninitialized, and whose first use occurs
  -- inside an accelerated expression.
  sem omitCopyUninitialized : CopyAnalysisEnv -> Expr -> CopyAnalysisEnv
  sem omitCopyUninitialized env =
  | t -> omitCopyUninitializedH env (setEmpty nameCmp) t

  sem omitCopyUninitializedH : CopyAnalysisEnv -> Set Name -> Expr -> CopyAnalysisEnv
  sem omitCopyUninitializedH env used =
  | TmLet t ->
    let f = lam x : (CopyStatus, Expr).
      match x with (status, arg) in
      match arg with TmVar {ident = ident} then
        -- NOTE(larshum, 2022-08-01): If the tensor is uninitialized and it has
        -- not been used yet, its data does not need to be copied.
        if setMem ident (setSubtract env.uninitTensors used) then
          omitCopyTo status
        else status
      else status in
    match collectAppArguments t.body with (fun, args) in
    let env =
      match fun with TmVar {ident = ident} then
        match mapLookup ident env.accelerateData with Some ad then
          let copyStatus = map f (zip ad.paramCopyStatus args) in
          let ad = {ad with paramCopyStatus = copyStatus} in
          let accelerateData = mapInsert ident ad env.accelerateData in
          {env with accelerateData = accelerateData}
        else env
      else env in
    let used =
      -- NOTE(larshum, 2022-08-01): Do not collect variables from the body of
      -- an accelerate binding.
      if mapMem t.ident env.accelerateData then used
      else setUnion (collectVariables t.body) used in
    omitCopyUninitializedH env used t.inexpr
  | TmRecLets t ->
    let collectBindingVariables = lam used. lam binding.
      setUnion (collectVariables binding.body) used in
    let used = foldl collectBindingVariables used t.bindings in
    omitCopyUninitializedH env used t.inexpr
  | TmType t -> omitCopyUninitializedH env used t.inexpr
  | TmConDef t -> omitCopyUninitializedH env used t.inexpr
  | TmUtest t -> omitCopyUninitializedH env used t.next
  | TmExt t -> omitCopyUninitializedH env used t.inexpr
  | _ -> env

  sem collectVariables : Expr -> Set Name
  sem collectVariables =
  | t -> collectVariablesH (setEmpty nameCmp) t

  sem collectVariablesH : Set Name -> Expr -> Set Name
  sem collectVariablesH vars =
  | TmVar t -> setInsert t.ident vars
  | t -> sfold_Expr_Expr collectVariablesH vars t

  -- Finds tensors that are exclusively used within an accelerate expression,
  -- after their definition. Such tensors do not need to be copied back to the
  -- OCaml code.
  sem findAccelerateExclusiveTensors : CopyAnalysisEnv -> Expr -> CopyAnalysisEnv
  sem findAccelerateExclusiveTensors env =
  | t ->
    let used = collectVariablesUsedOutsideAccelerate env (setEmpty nameCmp) t in
    findAccelerateExclusiveTensorsH env used t

  sem _isTensorCreateConstant : Const -> Bool
  sem _isTensorCreateConstant =
  | CTensorCreateUninitInt _ | CTensorCreateUninitFloat _ | CTensorCreateInt _
  | CTensorCreateFloat _ | CTensorCreate _ -> true
  | _ -> false

  sem findAccelerateExclusiveTensorsH : CopyAnalysisEnv -> Set Name -> Expr
                                     -> CopyAnalysisEnv
  sem findAccelerateExclusiveTensorsH env used =
  | TmLet t ->
    let f = lam x : (CopyStatus, Expr).
      match x with (status, arg) in
      match arg with TmVar {ident = ident} then
        -- NOTE(larshum, 2022-08-01): If the variable is not used outside
        -- accelerate expressions (after initialization), we omit copying it
        -- from the accelerated code to OCaml.
        if setMem ident used then status
        else omitCopyFrom status
      else status in
    match collectAppArguments t.body with (fun, args) in
    let env =
      match fun with TmVar {ident = ident} then
        match mapLookup ident env.accelerateData with Some ad then
          let copyStatus = map f (zip ad.paramCopyStatus args) in
          let ad = {ad with paramCopyStatus = copyStatus} in
          let accelerateData = mapInsert ident ad env.accelerateData in
          {env with accelerateData = accelerateData}
        else env
      else env in
    findAccelerateExclusiveTensorsH env used t.inexpr
  | TmRecLets t -> findAccelerateExclusiveTensorsH env used t.inexpr
  | TmType t -> findAccelerateExclusiveTensorsH env used t.inexpr
  | TmConDef t -> findAccelerateExclusiveTensorsH env used t.inexpr
  | TmUtest t -> findAccelerateExclusiveTensorsH env used t.next
  | TmExt t -> findAccelerateExclusiveTensorsH env used t.inexpr
  | _ -> env

  -- Collects a set of all variables that are used outside of accelerate
  -- expressions, i.e. by ignoring the definitions of accelerate bindings and
  -- the variables used in calls to accelerate bindings.
  sem collectVariablesUsedOutsideAccelerate : CopyAnalysisEnv -> Set Name
                                           -> Expr -> Set Name
  sem collectVariablesUsedOutsideAccelerate env used =
  | app & (TmApp _) ->
    match collectAppArguments app with (fun, args) in
    match fun with TmVar {ident = ident} then
      if mapMem ident env.accelerateData then used
      else collectVariables app
    else collectVariables app
  | TmLet t ->
    let used =
      if mapMem t.ident env.accelerateData then used
      else setUnion (collectVariables t.body) used in
    collectVariablesUsedOutsideAccelerate env used t.inexpr
  | TmRecLets t ->
    let collectBindingVariables = lam used. lam binding.
      if mapMem binding.ident env.accelerateData then used
      else setUnion (collectVariables binding.body) used in
    let used = foldl collectBindingVariables used t.bindings in
    collectVariablesUsedOutsideAccelerate env used t.inexpr
  | TmType t -> collectVariablesUsedOutsideAccelerate env used t.inexpr
  | TmConDef t -> collectVariablesUsedOutsideAccelerate env used t.inexpr
  | TmUtest t -> collectVariablesUsedOutsideAccelerate env used t.next
  | TmExt t -> collectVariablesUsedOutsideAccelerate env used t.inexpr
  | _ -> used
end
