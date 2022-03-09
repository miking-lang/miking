include "c/compile.mc"
include "cuda/ast.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "pmexpr/wrapper.mc"

lang CudaCWrapperBase = PMExprCWrapper + CudaAst + MExprAst + MExprCCompile
  syn TargetWrapperEnv =
  | CudaTargetEnv {
      -- Provides a mapping from the name of the C wrapper function to a CUDA
      -- wrapper function which handles interaction with CUDA kernels. Note
      -- that the name of the C wrapper function must be globally unique as it
      -- will be called from the OCaml code, while that of the CUDA wrapper
      -- does not, since it is called from a function stored in the same file.
      wrapperMap : Map Name Name,
      
      -- Reversed type environment from type lifting. Enables looking up the
      -- name of the replacement of a lifted type.
      revTypeEnv : Map Type Name,

      -- C compiler environment, used to compile MExpr types to the C
      -- equivalents.
      compileCEnv : CompileCEnv}

  sem getCudaType (env : TargetWrapperEnv) =
  | TyRecord {labels = []} -> CTyVoid ()
  | ty & (TySeq _ | TyTensor _ | TyRecord _) ->
    match env with CudaTargetEnv cenv in
    match mapLookup ty cenv.revTypeEnv with Some id then
      CTyVar {id = id}
    else error "Reverse type lookup failed in CUDA wrapper generation"
  | ty ->
    match env with CudaTargetEnv cenv in
    compileType cenv.compileCEnv ty
end

-- Translate the general C representation to one that is specific to CUDA. This
-- includes wrapping sequences in structs containing their length.
lang CToCudaWrapper = CudaCWrapperBase
  sem _generateCToCudaWrapperArgH (env : CWrapperEnv) (gpuIdent : Name) (ty : Type) =
  | SeqRepr t ->
    let cudaType = getCudaType env.targetEnv ty in
    let declStmt = CSDef {ty = cudaType, id = Some gpuIdent, init = None ()} in
    -- TODO(larshum, 2022-03-09): Update this part to add support
    -- multi-dimensional sequences.
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _seqLenKey},
      rhs = CEVar {id = t.sizeIdent}}} in
    let setSeqStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _seqKey},
      rhs = CEVar {id = t.dataIdent}}} in
    [declStmt, setLenStmt, setSeqStmt]
  | TensorRepr t ->
    let cudaType = getCudaType env.targetEnv ty in
    let declStmt = CSDef {ty = cudaType, id = Some gpuIdent, init = None ()} in
    let setTensorDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _tensorDataKey},
      rhs = CEVar {id = t.dataIdent}}} in
    let setTensorRankStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _tensorRankKey},
      rhs = CEVar {id = t.rankIdent}}} in

    -- NOTE(larshum, 2022-03-09): The current C representation of tensors
    -- supports at most 3 dimensions, so we verify that the provided tensor
    -- does not exceed this at runtime (the tensor rank is not known at
    -- compile-time).
    let printErrorStmt = CSExpr {expr = CEApp {
      fun = _printf,
      args = [
        CEString {s = "Tensors with rank at most 3 are supported, found %ld\n"},
        CEVar {id = t.rankIdent}]}} in
    let exitErrorStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "exit",
      args = [CEInt {i = 1}]}} in
    let checkRankStmt = CSIf {
      cond = CEBinOp {
        op = COLe (),
        lhs = CEVar {id = t.rankIdent},
        rhs = CEInt {i = 3}},
      thn = [],
      els = [printErrorStmt, exitErrorStmt]} in

    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let setTensorDimStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _tensorDimsKey},
        rhs = CEVar {id = i}},
      rhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = t.dimsIdent},
        rhs = CEVar {id = i}}}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = i},
        rhs = CEInt {i = 1}}}} in
    let setTensorDimsLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = CEVar {id = t.rankIdent}},
      body = [setTensorDimStmt, iterIncrementStmt]} in

    let setTensorOffsetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = _tensorOffsetKey},
      rhs = CEInt {i = 0}}} in
    [ declStmt, setTensorDataStmt, setTensorRankStmt, checkRankStmt
    , iterInitStmt, setTensorDimsLoopStmt, setTensorOffsetStmt ]
  | RecordRepr t ->
    match ty with TyRecord rec in
    let setField = lam idx : Int. lam fieldLabel : (CDataRepr, SID).
      match fieldLabel with (field, label) in
      let tmpIdent = nameSym "cuda_tmp" in
      let fieldType : Type =
        match mapLookup label rec.fields with Some ty then
          ty
        else error "Record type label not found among fields"
      in
      let fieldCudaType = getCudaType env.targetEnv fieldType in
      let initTmpIdentStmt = CSDef {
        ty = fieldCudaType, id = Some tmpIdent, init = None ()} in
      let stmts = _generateCToCudaWrapperArgH env tmpIdent fieldType field in
      let labelId = nameNoSym (sidToString label) in
      let fieldAssignStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = gpuIdent}, id = labelId},
        rhs = CEVar {id = tmpIdent}}} in
      join [[initTmpIdentStmt], stmts, [fieldAssignStmt]]
    in
    let cudaType = getCudaType env.targetEnv ty in
    let declStmt = CSDef {ty = cudaType, id = Some gpuIdent, init = None ()} in
    let fieldStmts = join (mapi setField (zip t.fields rec.labels)) in
    cons declStmt fieldStmts
  | BaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some gpuIdent,
      init = Some (CIExpr {expr = CEVar {id = t.ident}})}]

  sem generateCToCudaWrapperArg (env : CWrapperEnv) (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    let stmts = _generateCToCudaWrapperArgH env arg.gpuIdent arg.mexprType
                                            arg.cData in
    concat accStmts stmts

  sem generateCToCudaWrapper =
  | env ->
    let env : CWrapperEnv = env in
    foldl (generateCToCudaWrapperArg env) [] env.arguments
end

lang CudaCallWrapper = CudaCWrapperBase
  sem _generateDeallocArg (arg : ArgData) =
  | SeqRepr t ->
    [CSExpr {expr = CEApp {
      fun = _getIdentExn "free",
      args = [CEVar {id = t.dataIdent}]}}]
  | _ -> []

  sem generateCudaWrapperCall =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv cenv in

    -- Declare pointer to return value
    let return : ArgData = env.return in
    let returnType = return.mexprType in
    let cudaType = getCudaType env.targetEnv returnType in

    let args : [CExpr] =
      map
        (lam arg : ArgData.
          let var = CEVar {id = arg.gpuIdent} in
          match arg.cData with BaseTypeRepr _ then
            CEUnOp {op = CODeref (), arg = var}
          else var)
        env.arguments in
    let cudaWrapperId =
      match mapLookup env.functionIdent cenv.wrapperMap with Some id then id
      else error "Internal compiler error: No function defined for wrapper map" in
    let callStmts =
      match return.cData with RecordRepr {fields = []} then
        let wrapperCallStmt = CSExpr {expr = CEApp {
          fun = cudaWrapperId, args = args}} in
        [wrapperCallStmt]
      else
        let returnDecl = CSDef {
          ty = cudaType, id = Some return.gpuIdent, init = None ()} in
        let cudaWrapperCallStmt = CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEVar {id = return.gpuIdent},
          rhs = CEApp {fun = cudaWrapperId, args = args}}} in
        [returnDecl, cudaWrapperCallStmt]
    in

    -- Deallocate argument parameters
    let deallocStmts =
      join
        (map
          (lam arg : ArgData. _generateDeallocArg arg arg.cData)
          env.arguments) in

    concat callStmts deallocStmts
end

lang CudaToCWrapper = CudaCWrapperBase
  sem _generateCudaToCWrapperH (env : CWrapperEnv) (srcIdent : Name) (ty : Type) =
  | SeqRepr t ->
    let fieldAccess = lam key.
      CEMember {lhs = CEVar {id = srcIdent}, id = key} in
    -- TODO(larshum, 2022-03-09): Add support for multi-dimensional sequences.
    -- This includes setting the dimensions
    let dimIdent = head t.dimIdents in
    let dataType = CTyPtr {ty = t.elemTy} in
    let setDimStmt = CSDef {
      ty = CTyInt64 (), id = Some dimIdent,
      init = Some (CIExpr {expr = fieldAccess _seqLenKey})} in
    let setSizeStmt = CSDef {
      ty = CTyInt64 (), id = Some t.sizeIdent,
      init = Some (CIExpr {expr = CEVar {id = dimIdent}})} in
    let setDataStmt = CSDef {
      ty = dataType, id = Some t.dataIdent,
      init = Some (CIExpr {expr = fieldAccess _seqKey})} in
    [setDimStmt, setSizeStmt, setDataStmt]
  | TensorRepr t ->
    let fieldAccess = lam key.
      CEMember {lhs = CEVar {id = srcIdent}, id = key} in
    let dataType = CTyPtr {ty = t.elemTy} in
    let setTensorDataStmt = CSDef {
      ty = dataType, id = Some t.dataIdent,
      init = Some (CIExpr {expr = CEBinOp {
        op = COAdd (),
        lhs = fieldAccess _tensorDataKey,
        rhs = fieldAccess _tensorOffsetKey}})} in
    let setTensorRankStmt = CSDef {
      ty = CTyInt64 (), id = Some t.rankIdent,
      init = Some (CIExpr {expr = fieldAccess _tensorRankKey})} in
    let initTensorDimsStmt = CSDef {
      ty = CTyArray {ty = CTyInt64 (), size = Some (CEVar {id = t.rankIdent})},
      id = Some t.dimsIdent, init = None ()} in

    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let subScriptExpr = lam target.
      CEBinOp {
        op = COSubScript (),
        lhs = target,
        rhs = CEVar {id = i}} in
    let setTensorDimStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = subScriptExpr (CEVar {id = t.dimsIdent}),
      rhs = subScriptExpr (fieldAccess _tensorDimsKey)}} in
    let incrementIterStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = i},
        rhs = CEInt {i = 1}}}} in
    let setTensorDimsLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = CEVar {id = t.rankIdent}},
      body = [setTensorDimStmt, incrementIterStmt]} in

    [ setTensorDataStmt, setTensorRankStmt, initTensorDimsStmt, iterInitStmt
    , setTensorDimsLoopStmt ]
  | RecordRepr t ->
    if null t.fields then []
    else
      match ty with TyRecord rec in
      let wrapField = lam idx : Int. lam fieldLabels : (CDataRepr, SID).
        match fieldLabels with (field, label) in
        let fieldSrcIdent = nameSym "c_tmp" in
        let fieldType : Type =
          match mapLookup label rec.fields with Some ty then
            ty
          else error "Record typel abel not found among fields"
        in
        let fieldCudaType = getCudaType env.targetEnv fieldType in
        let labelId = nameNoSym (sidToString label) in
        let initFieldStmt = CSDef {
          ty = fieldCudaType, id = Some fieldSrcIdent,
          init = Some (CIExpr {expr = CEMember {
            lhs = CEVar {id = srcIdent},
            id = labelId}})} in
        let innerStmts = _generateCudaToCWrapperH env fieldSrcIdent fieldType field in
        cons initFieldStmt innerStmts
      in
      join (mapi wrapField (zip t.fields rec.labels))
  | BaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some t.ident,
      init = Some (CIExpr {expr = CEUnOp {
        op = COAddrOf (),
        arg = CEVar {id = srcIdent}}})}]

  sem generateCudaToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    _generateCudaToCWrapperH env return.gpuIdent return.mexprType return.cData
end

lang CudaCWrapper = CToCudaWrapper + CudaCallWrapper + CudaToCWrapper + Cmp
  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv (wrapperMap : Map Name Name) =
  | compileCEnv ->
    let compileCEnv : CompileCEnv = compileCEnv in
    let tupleSwap = lam t : (a, b). match t with (x, y) in (y, x) in
    let revTypeEnv = mapFromSeq cmpType (map tupleSwap compileCEnv.typeEnv) in
    let targetEnv = CudaTargetEnv {
      wrapperMap = wrapperMap, compileCEnv = compileCEnv,
      revTypeEnv = revTypeEnv} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  sem generateMarshallingCode =
  | env ->
    let stmt1 = generateOCamlToCWrapper env in
    let stmt2 = generateCToCudaWrapper env in
    let stmt3 = generateCudaWrapperCall env in
    let stmt4 = generateCudaToCWrapper env in
    let stmt5 = generateCToOCamlWrapper env in
    join [stmt1, stmt2, stmt3, stmt4, stmt5]

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode (accelerated : Map Name AccelerateData)
                          (wrapperMap : Map Name Name) =
  | compileCEnv ->
    let env = generateInitWrapperEnv wrapperMap compileCEnv in
    match generateWrapperCodeH env accelerated with (env, entryPointWrappers) in
    CuPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"caml/alloc.h\"",
        "\"caml/bigarray.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops =
        map
          (lam top : CTop. CuTTop {attrs = [CuAExternC ()], top = top})
          entryPointWrappers}
end
