include "cuda/ast.mc"
include "cuda/compile.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "mexpr/record.mc"
include "pmexpr/wrapper.mc"

let _tensorIntervalTypeId = nameNoSym "TInterval"
let _tensorIntervalId = nameNoSym "id"
let _tensorIntervalBegin = nameNoSym "begin"
let _tensorIntervalEnd = nameNoSym "end"
let _tensorIntervalRank = nameNoSym "rank"
let _tensorIntervalDims = nameNoSym "dims"
let _tensorIntervalNext = nameNoSym "next"
let _tensorIntervalOmitCopyTo = nameNoSym "omitCopyTo"
let _tensorIntervalOmitCopyFrom = nameNoSym "omitCopyFrom"
let _tensorIntervalCudaElemType = nameNoSym "elementType"

let _topTensorTypeId = nameNoSym "TTensor"
let _topTensorId = nameNoSym "id"
let _topTensorOCaml = nameNoSym "ocaml"
let _topTensorCuda = nameNoSym "cuda"
let _topTensorSize = nameNoSym "size"
let _topTensorPred = nameNoSym "pred"
let _topTensorOmitCopyTo = nameNoSym "omitCopyTo"
let _topTensorOmitCopyFrom = nameNoSym "omitCopyFrom"
let _topTensorCudaElemType = nameNoSym "elementType"

let _tensorHeadId = nameNoSym "head"
let _tensorStartId = nameNoSym "start"
let _tensorCountId = nameNoSym "tensor_count"
let _tensorIntervalsId = nameNoSym "intervals"
let _tensorTopMapId = nameNoSym "top_map"
let _tensorNmainId = nameNoSym "nmain"
let _tensorTopsId = nameNoSym "top_tensors"

let _intervalCmpBegin = nameNoSym "cmp_interval_begin"
let _intervalCmpId = nameNoSym "cmp_interval_id"

let _cudaErrorCheckStmt =
  use CudaAst in
  CSExpr {expr = CEApp {
    fun = _CUDA_UTILS_CHECK_CUDA_ERROR,
    args = []
  }}

lang CudaCWrapperBase = PMExprCWrapper + CudaAst + MExprAst + CudaCompile
  syn CDataRepr =
  | CudaSeqRepr {ident : Name, data : CDataRepr, elemTy : CType, ty : CType}
  | CudaTensorRepr {ident : Name, data : CDataRepr, elemTy : CType, ty : CType}
  | CudaRecordRepr {ident : Name, labels : [SID], fields : [CDataRepr], ty : CType}
  | CudaDataTypeRepr {ident : Name, constrs : Map Name (CType, CDataRepr), ty : CType}
  | CudaBaseTypeRepr {ident : Name, ty : CType}

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
      compileCEnv : CompileCEnv,

      -- Determines the maximum rank of a tensor. Larger values result in more
      -- memory usage per tensor.
      tensorMaxRank : Int}

  sem lookupTypeIdent : TargetWrapperEnv -> Type -> Option Type
  sem lookupTypeIdent env =
  | (TyRecord t) & tyrec ->
    if mapIsEmpty t.fields then None ()
    else
    match env with CudaTargetEnv cenv in
    let fields : Option [(SID, Type)] =
      optionMapM
        (lam f : (SID, Type).
          match f with (key, ty) in
          match lookupTypeIdent env ty with Some ty then
            Some (key, ty)
          else None ())
        (tyRecordOrderedFields tyrec) in
    match fields with Some fieldsSeq then
      let fields = mapFromSeq cmpSID fieldsSeq in
      let ty = TyRecord {t with fields = fields} in
      optionMap
        (lam id. nitycon_ id t.info)
        (mapLookup ty cenv.revTypeEnv)
    else None ()
  | ty & (TySeq {ty = elemTy} | TyTensor {ty = elemTy}) ->
    let elemTy =
      match lookupTypeIdent env elemTy with Some ty then ty
      else elemTy in
    let ty =
      match ty with TySeq t then TySeq {t with ty = elemTy}
      else match ty with TyTensor t then TyTensor {t with ty = elemTy}
      else never in
    match env with CudaTargetEnv cenv in
    match mapLookup ty cenv.revTypeEnv with Some id then
      Some (nitycon_ id (infoTy ty))
    else None ()
  | ty & (TyVariant _) ->
    match env with CudaTargetEnv cenv in
    match mapLookup ty cenv.revTypeEnv with Some id then
      Some (nitycon_ id (infoTy ty))
    else None ()
  | TyAlias t -> lookupTypeIdent env t.content
  | ty -> Some ty

  sem getCudaType : TargetWrapperEnv -> Type -> CType
  sem getCudaType env =
  | ty & (TyRecord {fields = fields}) ->
    match env with CudaTargetEnv cenv in
    if mapIsEmpty fields then CTyVoid ()
    else match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      if any (nameEq id) cenv.compileCEnv.ptrTypes then
        CTyPtr {ty = CTyVar {id = id}}
      else CTyVar {id = id}
    else
      errorSingle [infoTy ty]
        "Reverse type lookup failed when generating CUDA wrapper code"
  | ty & (TySeq _ | TyTensor _ | TyVariant _) ->
    match env with CudaTargetEnv cenv in
    match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      if any (nameEq id) cenv.compileCEnv.ptrTypes then
        CTyPtr {ty = CTyVar {id = id}}
      else CTyVar {id = id}
    else
      errorSingle [infoTy ty]
        "Reverse type lookup failed when generating CUDA wrapper code"
  | ty ->
    match env with CudaTargetEnv cenv in
    compileType cenv.compileCEnv ty

  sem getOcamlTensorType : TargetWrapperEnv -> Type -> CType
  sem getOcamlTensorType env =
  | TyFloat _ -> CTyDouble ()
  | TyInt _ -> CTyInt64 ()
  | ty -> errorSingle [infoTy ty] "Type is not supported for CUDA tensors"

  sem _generateCDataRepresentation : CWrapperEnv -> Type -> CDataRepr
  sem _generateCDataRepresentation env =
  | ty & (TySeq t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let elemTy = _unwrapType cenv.compileCEnv.typeEnv t.ty in
    CudaSeqRepr {
      ident = nameSym "cuda_seq_tmp",
      data = _generateCDataRepresentation env elemTy,
      elemTy = getCudaType env.targetEnv t.ty, ty = getCudaType env.targetEnv ty}
  | ty & (TyTensor t) ->
    CudaTensorRepr {
      ident = nameSym "cuda_tensor_tmp",
      data = _generateCDataRepresentation env t.ty,
      elemTy = getCudaType env.targetEnv t.ty,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyRecord t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let labels = tyRecordOrderedLabels ty in
    let fields : [CDataRepr] =
      map
        (lam label : SID.
          match mapLookup label t.fields with Some ty then
            let ty = _unwrapType cenv.compileCEnv.typeEnv ty in
            _generateCDataRepresentation env ty
          else errorSingle [t.info] "Inconsistent labels in record type")
        labels in
    CudaRecordRepr {
      ident = nameSym "cuda_rec_tmp", labels = labels, fields = fields,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyVariant t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let constrs : Map Name (CType, CDataRepr) =
      mapMapWithKey
        (lam constrId : Name. lam constrTy : Type.
          let constrTy = _unwrapType cenv.compileCEnv.typeEnv constrTy in
          ( getCudaType env.targetEnv constrTy
          , _generateCDataRepresentation env constrTy ))
        t.constrs in
    CudaDataTypeRepr {
      ident = nameSym "cuda_adt_tmp", constrs = constrs,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyCon _) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let ty = _unwrapType cenv.compileCEnv.typeEnv ty in
    match ty with TyCon _ then errorSingle [infoTy ty] "Could not unwrap type"
    else _generateCDataRepresentation env ty
  | TyAlias t ->
    _generateCDataRepresentation env t.content
  | ty ->
    CudaBaseTypeRepr {
      ident = nameSym "cuda_tmp",
      ty = getCudaType env.targetEnv ty}

  -- Applies an operation on all tensors contained in an expression of a given
  -- data representation.
  sem mapTensorsToStmts : CWrapperEnv
                       -> (CWrapperEnv -> CExpr -> CExpr -> [CStmt])
                       -> CExpr -> CDataRepr -> [CStmt]
  sem mapTensorsToStmts env tensorFn src =
  | CudaSeqRepr t ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let innerSrc = CEApp {
      fun = _getIdentExn "Field",
      args = [src, iter]} in
    let stmts = mapTensorsToStmts env tensorFn innerSrc t.data in
    if null stmts then []
    else
      let iterInitStmt = CSDef {
        ty = CTyInt64 (), id = Some iterId,
        init = Some (CIExpr {expr = CEInt {i = 0}})} in
      let iterIncrementStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = iter,
        rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
      let lenExpr = CEApp {fun = _getIdentExn "Wosize_val", args = [src]} in
      let loopStmt = CSWhile {
        cond = CEBinOp {op = COLt (), lhs = iter, rhs = lenExpr},
        body = snoc stmts iterIncrementStmt} in
      [iterInitStmt, loopStmt]
  | CudaRecordRepr t ->
    foldl
      (lam acc. lam field : (SID, (Int, CDataRepr)).
        match field with (key, (idx, fieldRepr)) in
        let fieldId = nameNoSym (sidToString key) in
        let innerSrc = CEApp {
          fun = _getIdentExn "Field",
          args = [src, CEInt {i = idx}]} in
        let stmts = mapTensorsToStmts env tensorFn innerSrc fieldRepr in
        concat acc stmts)
      [] (zip t.labels (create (length t.fields) (lam i. (i, get t.fields i))))
  | CudaDataTypeRepr t ->
    let counter = ref 0 in
    mapFoldWithKey
      (lam acc. lam constrId. lam constrTyData.
        match constrTyData with (constrTy, constrData) in
        let constrExpr = _accessMember t.ty src constrId in
        let count = deref counter in
        modref counter (addi count 1);
        let stmts = mapTensorsToStmts env tensorFn constrExpr constrData in
        if null stmts then acc
        else
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = _accessMember t.ty src _constrKey,
                rhs = CEInt {i = count}},
              thn = stmts,
              els = acc} ])
      [] t.constrs
  | CudaBaseTypeRepr _ -> []
  | CudaTensorRepr t ->
    let elemTypeId =
      match t.elemTy with CTyInt64 _ | CTyDouble _ then 0
      else match t.elemTy with CTyInt32 _ then 1
      else match t.elemTy with CTyFloat _ then 2
      else never in
    let elemType = CEInt {i = elemTypeId} in
    tensorFn env elemType src
end

lang CudaTensorWrapper = CudaCWrapperBase
  sem generateGlobalTensorTops : CompileCEnv -> [CuTop]
  sem generateGlobalTensorTops =
  | env ->
    let dimsSize = CEInt {i = env.options.tensorMaxRank} in
    let intervalSelfRef = CTyPtr {
      ty = CTyStruct {id = Some _tensorIntervalTypeId, mem = None ()}} in
    let intervalType = CTyStruct {
      id = Some _tensorIntervalTypeId,
      mem = Some ([
        (CTyInt64 (), Some _tensorIntervalId),
        (CTyInt64 (), Some _tensorIntervalBegin),
        (CTyInt64 (), Some _tensorIntervalEnd),
        (CTyInt64 (), Some _tensorIntervalRank),
        (CTyArray {ty = CTyInt64 (), size = Some dimsSize}, Some _tensorIntervalDims),
        (intervalSelfRef, Some _tensorIntervalNext),
        (CTyInt (), Some _tensorIntervalOmitCopyTo),
        (CTyInt (), Some _tensorIntervalOmitCopyFrom),
        (CTyInt (), Some _tensorIntervalCudaElemType)])} in
    let intervalDefTop = CuTTop {
      attrs = [],
      top = CTTyDef {ty = intervalType, id = _tensorIntervalTypeId}} in
    let constVoidPtrTy = CTyConst {ty = CTyPtr {ty = CTyVoid ()}} in
    let lhs = nameSym "lhs" in
    let rhs = nameSym "rhs" in
    let l = nameSym "l" in
    let r = nameSym "r" in
    let intervalType = CTyPtr {ty = CTyVar {id = _tensorIntervalTypeId}} in
    let beginField = lam t.
      CEArrow {lhs = CEVar {id = t}, id = _tensorIntervalBegin} in
    let idField = lam t.
      CEArrow {lhs = CEVar {id = t}, id = _tensorIntervalId} in
    let intervalCmpBeginTop = CuTTop {
      attrs = [],
      top = CTFun {
        ret = CTyInt (), id = _intervalCmpBegin,
        params = [(constVoidPtrTy, lhs), (constVoidPtrTy, rhs)],
        body = [
          CSDef {
            ty = intervalType, id = Some l,
            init = Some (CIExpr {expr = CECast {
              ty = intervalType, rhs = CEVar {id = lhs}}})},
          CSDef {
            ty = intervalType, id = Some r,
            init = Some (CIExpr {expr = CECast {
              ty = intervalType, rhs = CEVar {id = rhs}}})},
          CSRet {val = Some (CEBinOp {
            op = COSub (),
            lhs = CEBinOp {op = COGt (), lhs = beginField l, rhs = beginField r},
            rhs = CEBinOp {op = COLt (), lhs = beginField l, rhs = beginField r}})}]}} in
    let intervalCmpIdTop = CuTTop {
      attrs = [],
      top = CTFun {
        ret = CTyInt (), id = _intervalCmpId,
        params = [(constVoidPtrTy, lhs), (constVoidPtrTy, rhs)],
        body = [
          CSDef {
            ty = intervalType, id = Some l,
            init = Some (CIExpr {expr = CECast {
              ty = intervalType, rhs = CEVar {id = lhs}}})},
          CSDef {
            ty = intervalType, id = Some r,
            init = Some (CIExpr {expr = CECast {
              ty = intervalType, rhs = CEVar {id = rhs}}})},
          CSRet {val = Some (CEBinOp {
            op = COSub (),
            lhs = CEBinOp {op = COGt (), lhs = idField l, rhs = idField r},
            rhs = CEBinOp {op = COLt (), lhs = idField l, rhs = idField r}})}]}} in
    let topTensorSelfRef = CTyPtr {
      ty = CTyStruct {id = Some _topTensorTypeId, mem = None ()}} in
    let topTensorType = CTyStruct {
      id = Some _topTensorTypeId,
      mem = Some ([
        (CTyInt64 (), Some _topTensorId),
        (CTyPtr {ty = CTyVoid ()}, Some _topTensorOCaml),
        (CTyPtr {ty = CTyVoid ()}, Some _topTensorCuda),
        (CTyInt64 (), Some _topTensorSize),
        (topTensorSelfRef, Some _topTensorPred),
        (CTyInt (), Some _topTensorOmitCopyTo),
        (CTyInt (), Some _topTensorOmitCopyFrom),
        (CTyInt (), Some _topTensorCudaElemType)])} in
    let topTensorDefTop = CuTTop {
      attrs = [],
      top = CTTyDef {ty = topTensorType, id = _topTensorTypeId}} in
    [intervalDefTop, intervalCmpBeginTop, intervalCmpIdTop, topTensorDefTop]

  sem _generateTensorIntervalArgStmts : CWrapperEnv -> [CStmt] -> ArgData
                                     -> [CStmt]
  sem _generateTensorIntervalArgStmts env acc =
  | {mexprIdent = mid, copyStatus = cs, gpuIdent = gid, cData = cdata} ->
    let incrementStmt = lam id.
      CSExpr {expr = CEBinOp {
        op = COAssign (), lhs = CEVar {id = id},
        rhs = CEBinOp {
          op = COAdd (), lhs = CEVar {id = id}, rhs = CEInt {i = 1}}}} in
    let tensorFn = lam env. lam elemType. lam tensor.
      let tid = nameSym "t" in
      let t = CEVar {id = tid} in
      let intervalType = CTyVar {id = _tensorIntervalTypeId} in
      let intervalInitStmt = CSDef {
        ty = CTyPtr {ty = intervalType}, id = Some tid,
        init = Some (CIExpr {expr = CECast {
          ty = CTyPtr {ty = intervalType},
          rhs = CEApp {
            fun = _malloc, args = [CESizeOfType {ty = intervalType}]}}})} in
      let intervalIdStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalId},
        rhs = CEVar {id = _tensorCountId}}} in
      let tensorCountIncrement = incrementStmt _tensorCountId in
      let intervalRankStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalRank},
        rhs = CEArrow {
          lhs = CEApp {
            fun = _getIdentExn "Caml_ba_array_val",
            args = [tensor]},
          id = _bigarrayNumDimsKey}}} in
      let intervalBeginStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalBegin},
        rhs = CECast {
          ty = CTyInt64 (),
          rhs = CEApp {
            fun = _getIdentExn "Caml_ba_data_val",
            args = [tensor]}}}} in
      let iterId = nameSym "i" in
      let iter = CEVar {id = iterId} in
      let iterInitStmt = CSDef {
        ty = CTyInt64 (), id = Some iterId,
        init = Some (CIExpr {expr = CEInt {i = 0}})} in
      let sizeId = nameSym "n" in
      let size = CEVar {id = sizeId} in
      let sizeInitStmt = CSDef {
        ty = CTyInt64 (), id = Some sizeId,
        init = Some (CIExpr {expr = CESizeOfType {ty = CTyInt64 ()}})} in

      let dimsSetStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEArrow {lhs = t, id = _tensorIntervalDims},
          rhs = iter},
        rhs = CEBinOp {
          op = COSubScript (),
          lhs = CEArrow {
            lhs = CEApp {
              fun = _getIdentExn "Caml_ba_array_val",
              args = [tensor]},
            id = _bigarrayDimKey},
          rhs = iter}}} in
      let multiplySizeStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = size,
        rhs = CEBinOp {
          op = COMul (),
          lhs = size,
          rhs = CEBinOp {
            op = COSubScript (),
            lhs = CEArrow {
              lhs = CEApp {
                fun = _getIdentExn "Caml_ba_array_val",
                args = [tensor]},
              id = _bigarrayDimKey},
            rhs = iter}}}} in
      let iterIncrement = incrementStmt iterId in
      let loopCond = CEBinOp {
        op = COLt (),
        lhs = iter,
        rhs = CEArrow {
          lhs = CEApp {
            fun = _getIdentExn "Caml_ba_array_val",
            args = [tensor]},
          id = _bigarrayNumDimsKey}} in
      let dimLoopStmt = CSWhile {
        cond = loopCond,
        body = [dimsSetStmt, multiplySizeStmt, iterIncrement]} in

      let intervalEndStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalEnd},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CECast {
            ty = CTyInt64 (),
            rhs = CEArrow {lhs = t, id = _tensorIntervalBegin}},
          rhs = size}}} in
      let headNextStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = CEVar {id = _tensorHeadId}, id = _tensorIntervalNext},
        rhs = t}} in
      let intervalOmitCopyToStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalOmitCopyTo},
        rhs = CEInt {i = if copyStatusTo cs then 0 else 1}}} in
      let intervalOmitCopyFromStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalOmitCopyFrom},
        rhs = CEInt {i = if copyStatusFrom cs then 0 else 1}}} in
      let intervalElementTypeStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEArrow {lhs = t, id = _tensorIntervalCudaElemType},
        rhs = elemType}} in
      let headUpdateStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = _tensorHeadId}, rhs = t}} in
      [ intervalInitStmt, intervalIdStmt, tensorCountIncrement
      , intervalRankStmt, intervalBeginStmt, iterInitStmt, sizeInitStmt
      , dimLoopStmt, intervalEndStmt, headNextStmt, intervalOmitCopyToStmt
      , intervalOmitCopyFromStmt, intervalElementTypeStmt, headUpdateStmt ]
    in
    let src = CEVar {id = mid} in
    concat acc (mapTensorsToStmts env tensorFn src cdata)

  sem generateTensorIntervalStmts : CWrapperEnv -> [CStmt]
  sem generateTensorIntervalStmts =
  | env ->
    let counterInit = CSDef {
      ty = CTyInt64 (), id = Some _tensorCountId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let tensorIntervalType = CTyVar {id = _tensorIntervalTypeId} in
    let startInterval = CSDef {
      ty = tensorIntervalType, id = Some _tensorStartId,
      init = None ()} in
    let start = CEVar {id = _tensorStartId} in
    let startIntervalNextNull = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = start, id = _tensorIntervalNext},
      rhs = CEVar {id = _getIdentExn "NULL"}}} in
    let headInitStmt = CSDef {
      ty = CTyPtr {ty = tensorIntervalType}, id = Some _tensorHeadId,
      init = Some (CIExpr {expr = CEUnOp {op = COAddrOf (), arg = start}})} in
    concat
      [counterInit, startInterval, startIntervalNextNull, headInitStmt]
      (foldl (_generateTensorIntervalArgStmts env) [] env.arguments)

  sem generateIntervalSort : CWrapperEnv -> [CStmt]
  sem generateIntervalSort =
  | env ->
    let intervalType = CTyVar {id = _tensorIntervalTypeId} in
    let intervalsArrayInitStmt = CSDef {
      ty = CTyPtr {ty = intervalType}, id = Some _tensorIntervalsId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = intervalType},
        rhs = CEApp {
          fun = _malloc,
          args = [CEBinOp {
            op = COMul (),
            lhs = CEVar {id = _tensorCountId},
            rhs = CESizeOfType {ty = intervalType}}]}}})} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let setHeadNullStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = CEVar {id = _tensorHeadId}, id = _tensorIntervalNext},
      rhs = CEVar {id = _getIdentExn "NULL"}}} in
    let currId = nameSym "curr" in
    let currIntervalStmt = CSDef {
      ty = CTyPtr {ty = intervalType}, id = Some currId,
      init = Some (CIExpr {expr = CEMember {
        lhs = CEVar {id = _tensorStartId},
        id = _tensorIntervalNext}})} in

    let intervalsSetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorIntervalsId},
        rhs = iter},
      rhs = CEUnOp {
        op = CODeref (),
        arg = CEVar {id = currId}}}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let tempId = nameSym "temp_ptr" in
    let tempIntervalPtrStmt = CSDef {
      ty = CTyPtr {ty = CTyVar {id = _tensorIntervalTypeId}},
      id = Some tempId,
      init = Some (CIExpr {expr = CEVar {id = currId}})} in
    let nextStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = CEVar {id = currId},
      rhs = CEArrow {
        lhs = CEVar {id = currId},
        id = _tensorIntervalNext}}} in
    let freeTempPtrStmt = CSExpr {expr = CEApp {
      fun = _free, args = [CEVar {id = tempId}]}} in
    let loopStmt = CSWhile {
      cond = CEVar {id = currId},
      body = [ intervalsSetStmt, iterIncrementStmt, tempIntervalPtrStmt
             , nextStmt, freeTempPtrStmt ]} in

    let qsortStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "qsort",
      args = [
        CEVar {id = _tensorIntervalsId},
        CEVar {id = _tensorCountId},
        CESizeOfType {ty = CTyVar {id = _tensorIntervalTypeId}},
        CEVar {id = _intervalCmpBegin}]}} in

    [ intervalsArrayInitStmt, iterStmt, setHeadNullStmt, currIntervalStmt
    , loopStmt, qsortStmt ]

  sem generateTopTensorConstruction : CWrapperEnv -> [CStmt]
  sem generateTopTensorConstruction =
  | env ->
    let incrementStmt = lam var.
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = var,
        rhs = CEBinOp {op = COAdd (), lhs = var, rhs = CEInt {i = 1}}}} in
    let sizeExpr = CEBinOp {
      op = COMul (), lhs = CEVar {id = _tensorCountId},
      rhs = CESizeOfType {ty = CTyInt64 ()}} in
    let topMapInitStmt = CSDef {
      ty = CTyPtr {ty = CTyInt64 ()}, id = Some _tensorTopMapId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = CTyInt64 ()},
        rhs = CEApp {fun = _getIdentExn "malloc", args = [sizeExpr]}}})} in
    let mainCountId = nameSym "top_count" in
    let mainCount = CEVar {id = mainCountId} in
    let mainCountStmt = CSDef {
      ty = CTyInt64 (), id = Some mainCountId,
      init = Some (CIExpr {expr = CEVar {id = _tensorCountId}})} in
    let fstId = nameSym "fst" in
    let fst = CEVar {id = fstId} in
    let topTensorType = CTyVar {id = _topTensorTypeId} in
    let fstTopTensorDeclStmt = CSDef {
      ty = CTyPtr {ty = topTensorType}, id = Some fstId, init = None ()} in
    let stackId = nameSym "stack" in
    let stack = CEVar {id = stackId} in
    let tensorStackInitStmt = CSDef {
      ty = CTyPtr {ty = topTensorType}, id = Some stackId,
      init = Some (CIExpr {expr = CEVar {id = _getIdentExn "NULL"}})} in
    let fstInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = fst,
      rhs = CECast {
        ty = CTyPtr {ty = topTensorType},
        rhs = CEApp {
          fun = _malloc,
          args = [CESizeOfType {ty = topTensorType}]}}}} in
    let stackInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = stack, rhs = fst}} in
    let fstIdSetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _tensorIntervalId},
      rhs = CEVar {id = mainCountId}}} in
    let firstIntervalExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorIntervalsId},
      rhs = CEInt {i = 0}} in
    let topMapSetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorTopMapId},
        rhs = CEMember {lhs = firstIntervalExpr, id = _topTensorId}},
      rhs = CEInt {i = 0}}} in
    let incrementMainStmt = incrementStmt mainCount in
    let fstOCamlStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorOCaml},
      rhs = CECast {
        ty = CTyPtr {ty = CTyVoid ()},
        rhs = CEMember {
          lhs = firstIntervalExpr, id = _tensorIntervalBegin}}}} in
    let fstSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorSize},
      rhs = CEBinOp {
        op = COSub (),
        lhs = CECast {
          ty = CTyInt64 (),
          rhs = CEMember {lhs = firstIntervalExpr, id = _tensorIntervalEnd}},
        rhs = CECast {
          ty = CTyInt64 (),
          rhs = CEMember {
            lhs = firstIntervalExpr, id = _tensorIntervalBegin}}}}} in
    let fstPredStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorPred},
      rhs = CEVar {id = _getIdentExn "NULL"}}} in
    let fstOmitCopyToStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorOmitCopyTo},
      rhs = CEMember {lhs = firstIntervalExpr, id = _tensorIntervalOmitCopyTo}}} in
    let fstOmitCopyFromStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorOmitCopyFrom},
      rhs = CEMember {lhs = firstIntervalExpr, id = _tensorIntervalOmitCopyFrom}}} in
    let fstElemSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = fst, id = _topTensorCudaElemType},
      rhs = CEMember {lhs = firstIntervalExpr, id = _tensorIntervalCudaElemType}}} in
    let fstCondInitStmt = CSIf {
      cond = CEBinOp {
        op = COGt (),
        lhs = CEVar {id = _tensorCountId},
        rhs = CEInt {i = 0}},
      thn = [ fstInitStmt, stackInitStmt, fstIdSetStmt, topMapSetStmt
            , incrementMainStmt, fstOCamlStmt, fstSizeStmt, fstPredStmt
            , fstOmitCopyToStmt, fstOmitCopyFromStmt, fstElemSizeStmt ],
      els = []} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in

    let intervalExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorIntervalsId},
      rhs = iter} in
    let overlappingCondExpr = CEBinOp {
      op = COGe (),
      lhs = CEBinOp {
        op = COAdd (),
        lhs = CECast {
          ty = CTyInt64 (),
          rhs = CEArrow {lhs = stack, id = _topTensorOCaml}},
        rhs = CEArrow {lhs = stack, id = _topTensorSize}},
      rhs = CEMember {
        lhs = intervalExpr, id = _tensorIntervalBegin}} in
    let thnTopMapUpdateStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorTopMapId},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalId}},
      rhs = CEBinOp {
        op = COSub (),
        lhs = CEArrow {lhs = stack, id = _topTensorId},
        rhs = CEVar {id = _tensorCountId}}}} in
    let maxIfStmt = CSIf {
      cond = CEBinOp {
        op = COGt (),
        lhs = CEMember {lhs = intervalExpr, id = _tensorIntervalEnd},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CECast {
            ty = CTyInt64 (),
            rhs = CEArrow {lhs = stack, id = _topTensorOCaml}},
          rhs = CEArrow {lhs = stack, id = _topTensorSize}}},
      thn = [
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEArrow {lhs = stack, id = _topTensorSize},
          rhs = CEBinOp {
            op = COSub (),
            lhs = CECast {
              ty = CTyInt64 (),
              rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalEnd}},
            rhs = CECast {
              ty = CTyInt64 (),
              rhs = CEArrow {lhs = stack, id = _topTensorOCaml}}}}}],
      els = []} in
    let nextId = nameSym "next" in
    let next = CEVar {id = nextId} in
    let nextInitStmt = CSDef {
      ty = CTyPtr {ty = topTensorType}, id = Some nextId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = topTensorType},
        rhs = CEApp {
          fun = _malloc,
          args = [CESizeOfType {ty = topTensorType}]}}})} in
    let nextIdStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorId},
      rhs = mainCount}} in
    let elsTopMapUpdateStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorTopMapId},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalId}},
      rhs = CEBinOp {
        op = COSub (),
        lhs = CEArrow {lhs = next, id = _topTensorId},
        rhs = CEVar {id = _tensorCountId}}}} in
    let mainIncrementStmt = incrementStmt mainCount in
    let nextOCamlStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorOCaml},
      rhs = CECast {
        ty = CTyPtr {ty = CTyVoid ()},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalBegin}}}} in
    let nextSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorSize},
      rhs = CEBinOp {
        op = COSub (),
        lhs = CECast {
          ty = CTyInt64 (),
          rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalEnd}},
        rhs = CECast {
          ty = CTyInt64 (),
          rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalBegin}}}}} in
    let nextPredStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorPred},
      rhs = stack}} in
    let nextOmitCopyToStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorOmitCopyTo},
      rhs = CEInt {i = 1}}} in
    let nextOmitCopyFromStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorOmitCopyFrom},
      rhs = CEInt {i = 1}}} in
    let nextElementTypeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = next, id = _topTensorCudaElemType},
      rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalCudaElemType}}} in
    let stackUpdateStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = stack, rhs = next}} in
    let condStmt = CSIf {
      cond = overlappingCondExpr,
      thn = [thnTopMapUpdateStmt, maxIfStmt],
      els = [ nextInitStmt, nextIdStmt, elsTopMapUpdateStmt, mainIncrementStmt
            , nextOCamlStmt, nextSizeStmt, nextPredStmt, nextOmitCopyToStmt
            , nextOmitCopyFromStmt, nextElementTypeStmt, stackUpdateStmt ]} in
    let updateTopOmitCopyToStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = stack, id = _topTensorOmitCopyTo},
      rhs = CEBinOp {
        op = COAnd (),
        lhs = CEArrow {lhs = stack, id = _topTensorOmitCopyTo},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalOmitCopyTo}}}} in
    let updateTopOmitCopyFromStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEArrow {lhs = stack, id = _topTensorOmitCopyFrom},
      rhs = CEBinOp {
        op = COAnd (),
        lhs = CEArrow {lhs = stack, id = _topTensorOmitCopyFrom},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalOmitCopyFrom}}}} in
    let iterIncrementStmt = incrementStmt iter in
    let loopCondExpr = CEBinOp {
      op = COLt (), lhs = iter, rhs = CEVar {id = _tensorCountId}} in
    let loopStmt = CSWhile {
      cond = loopCondExpr,
      body = [ condStmt, updateTopOmitCopyToStmt, updateTopOmitCopyFromStmt
             , iterIncrementStmt ]} in

    -- Construct an array containing the top-level tensors from the linked-list
    -- structure used to represent the stack.
    let nmainInitStmt = CSDef {
      ty = CTyInt64 (), id = Some _tensorNmainId,
      init = Some (CIExpr {expr = CEBinOp {
        op = COSub (),
        lhs = mainCount, rhs = CEVar {id = _tensorCountId}}})} in
    let topTensorSize = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = _tensorNmainId},
      rhs = CESizeOfType {ty = topTensorType}} in
    let topTensorsInitStmt = CSDef {
      ty = CTyPtr {ty = topTensorType},
      id = Some _tensorTopsId,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = topTensorType},
        rhs = CEApp {fun = _malloc, args = [topTensorSize]}}})} in
    let iterSetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {
        op = COSub (),
        lhs = CEVar {id = _tensorNmainId},
        rhs = CEInt {i = 1}}}} in

    let topTensorsSetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (), lhs = CEVar {id = _tensorTopsId}, rhs = iter},
      rhs = CEUnOp {op = CODeref (), arg = stack}}} in
    let tempPtrId = nameSym "temp_ptr" in
    let tempPtrStmt = CSDef {
      ty = CTyPtr {ty = topTensorType}, id = Some tempPtrId,
      init = Some (CIExpr {expr = stack})} in
    let stackUpdateStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = stack,
      rhs = CEArrow {lhs = stack, id = _topTensorPred}}} in
    let deallocStmt = CSExpr {expr = CEApp {
      fun = _free,
      args = [CEVar {id = tempPtrId}]}} in
    let iterDecrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = iter,
      rhs = CEBinOp {op = COSub (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let topTensorLoopStmt = CSWhile {
      cond = stack,
      body = [ topTensorsSetStmt, tempPtrStmt, stackUpdateStmt, deallocStmt
             , iterDecrementStmt ]} in

    [ topMapInitStmt, mainCountStmt, fstTopTensorDeclStmt, tensorStackInitStmt
    , fstCondInitStmt, iterInitStmt, loopStmt, nmainInitStmt
    , topTensorsInitStmt, iterSetStmt, topTensorLoopStmt ]

  sem generateTensorCudaAlloc : CWrapperEnv -> [CStmt]
  sem generateTensorCudaAlloc =
  | env ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let next = CEBinOp {
      op = COSubScript (), lhs = CEVar {id = _tensorTopsId}, rhs = iter} in
    let accessField = lam id. CEMember {lhs = next, id = id} in
    let addrOfCudaData = CEUnOp {
      op = COAddrOf (), arg = accessField _topTensorCuda} in
    let mallocManagedStmt = CSExpr {expr = CEApp {
      fun = _cudaMallocManaged,
      args = [addrOfCudaData, accessField _topTensorSize]}} in
    let memcpyStmt = CSExpr {expr = CEApp {
      fun = _CUDA_UTILS_COPY_OCAML_CUDA,
      args = [
        accessField _topTensorOCaml,
        accessField _topTensorCuda,
        accessField _topTensorSize,
        accessField _topTensorCudaElemType]}} in
    let copyCondition = CEBinOp {
      op = COEq (),
      lhs = accessField _topTensorOmitCopyTo,
      rhs = CEInt {i = 0}} in
    let condMemcpyStmt = CSIf {
      cond = copyCondition,
      thn = [memcpyStmt, _cudaErrorCheckStmt],
      els = []} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let allocLoopCond = CEBinOp {
      op = COLt (), lhs = iter, rhs = CEVar {id = _tensorNmainId}} in
    let allocCopyLoop = CSWhile {
      cond = allocLoopCond,
      body = [ mallocManagedStmt, _cudaErrorCheckStmt, condMemcpyStmt
             , iterIncrementStmt ]} in
    let qsortIntervalsStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "qsort",
      args = [
        CEVar {id = _tensorIntervalsId},
        CEVar {id = _tensorCountId},
        CESizeOfType {ty = CTyVar {id = _tensorIntervalTypeId}},
        CEVar {id = _intervalCmpId}]}} in
    [iterInitStmt, allocCopyLoop, qsortIntervalsStmt]

  sem generateTensorCudaDealloc : CWrapperEnv -> [CStmt]
  sem generateTensorCudaDealloc =
  | env ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let next = CEBinOp {
      op = COSubScript (), lhs = CEVar {id = _tensorTopsId}, rhs = iter} in
    let accessField = lam id. CEMember {lhs = next, id = id} in
    let copyCondition = CEBinOp {
      op = COEq (),
      lhs = accessField _topTensorOmitCopyFrom,
      rhs = CEInt {i = 0}} in
    let memcpyStmt = CSExpr {expr = CEApp {
      fun = _CUDA_UTILS_COPY_CUDA_OCAML,
      args = [
        accessField _topTensorCuda,
        accessField _topTensorOCaml,
        accessField _topTensorSize,
        accessField _topTensorCudaElemType]}} in
    let condMemcpyStmt = CSIf {
      cond = copyCondition,
      thn = [memcpyStmt, _cudaErrorCheckStmt],
      els = []} in
    let freeStmt = CSExpr {expr = CEApp {
      fun = _cudaFree,
      args = [accessField _topTensorCuda]}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let loopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (), lhs = iter, rhs = CEVar {id = _tensorNmainId}},
      body = [ condMemcpyStmt, freeStmt, _cudaErrorCheckStmt
             , iterIncrementStmt ]} in
    let freeTopsStmt = CSExpr {expr = CEApp {
      fun = _free,
      args = [CEVar {id = _tensorTopsId}]}} in
    [iterInitStmt, loopStmt, freeTopsStmt]
end

lang OCamlToCudaWrapper = CudaCWrapperBase
  sem _generateOCamlToCudaWrapperStmts : CWrapperEnv -> CExpr -> Name
                                      -> CDataRepr -> [CStmt]
  sem _generateOCamlToCudaWrapperStmts env src dstIdent =
  | CudaSeqRepr t ->
    let seqInitExpr =
      match t.ty with CTyPtr {ty = ty} then
        let sizeExpr = CESizeOfType {ty = ty} in
        Some (CECast {ty = t.ty, rhs = CEApp {fun = _malloc, args = [sizeExpr]}})
      else None () in
    let seqDefStmt = CSDef {
      ty = t.ty, id = Some dstIdent,
      init = optionMap (lam e. CIExpr {expr = e}) seqInitExpr} in
    let dst = CEVar {id = dstIdent} in
    let seqLenExpr = _accessMember t.ty dst _seqLenKey in
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = seqLenExpr, rhs = _wosize src}} in
    let elemTy = t.elemTy in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = _wosize src,
      rhs = CESizeOfType {ty = elemTy}} in
    let allocSeqStmt = CSExpr {expr = CEApp {
      fun = _cudaMallocManaged,
      args = [
        CEUnOp {op = COAddrOf (), arg = _accessMember t.ty dst _seqKey},
        sizeExpr]}} in

    let iterIdent = nameSym "i" in
    let iter = CEVar {id = iterIdent} in
    let iterDefStmt = CSDef {
      ty = CTyInt64 (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let fieldDstExpr = CEBinOp {
      op = COSubScript (),
      lhs = _accessMember t.ty dst _seqKey,
      rhs = iter} in
    let fieldUpdateStmts =
      match elemTy with CTyFloat _ | CTyDouble _ then
        [ CSExpr {expr = CEBinOp {
            op = COAssign (),
            lhs = fieldDstExpr,
            rhs = CECast {
              ty = elemTy,
              rhs = CEApp {
                fun = _getIdentExn "Double_field",
                args = [src, iter]}}}} ]
      else
        let fieldId = nameSym "cuda_seq_temp" in
        let fieldExpr = CEApp {fun = _getIdentExn "Field", args = [src, iter]} in
        let fieldDefStmt = CSDef {
          ty = elemTy, id = Some fieldId,
          init = Some (CIExpr {expr = fieldExpr})} in
        let stmts = _generateOCamlToCudaWrapperStmts env fieldExpr fieldId t.data in
        let fieldUpdateStmt = CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = fieldDstExpr,
          rhs = CEVar {id = fieldId}}} in
        snoc stmts fieldUpdateStmt in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let dataCopyLoopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = seqLenExpr},
      body = snoc fieldUpdateStmts iterIncrementStmt} in
    [ seqDefStmt, setLenStmt, allocSeqStmt, _cudaErrorCheckStmt, iterDefStmt, dataCopyLoopStmt ]
  | CudaTensorRepr t ->
    match env.targetEnv with CudaTargetEnv cenv in
    let bigarrayValId = _getIdentExn "Caml_ba_array_val" in
    let dst = CEVar {id = dstIdent} in
    let tensorDefStmt = CSDef {ty = t.ty, id = Some dstIdent, init = None ()} in
    let setTensorIdStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorIdKey,
      rhs = CEVar {id = _tensorCountId}}} in
    let incrementTensorCountStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = _tensorCountId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = _tensorCountId},
        rhs = CEInt {i = 1}}}} in

    let tensorIdExpr = _accessMember t.ty dst _tensorIdKey in
    let intervalExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorIntervalsId},
      rhs = tensorIdExpr} in
    let setTensorRankStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorRankKey,
      rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalRank}}} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let updateDimsStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = _accessMember t.ty dst _tensorDimsKey,
        rhs = iter},
      rhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = intervalExpr, id = _tensorIntervalDims},
        rhs = iter}}} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let updateDimsLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (), lhs = iter,
        rhs = _accessMember t.ty dst _tensorRankKey},
      body = [updateDimsStmt, iterIncrementStmt]} in
    let setTensorSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorSizeKey,
      rhs = CEBinOp {
        op = COSub (),
        lhs = CEMember {lhs = intervalExpr, id = _tensorIntervalEnd},
        rhs = CEMember {lhs = intervalExpr, id = _tensorIntervalBegin}}}} in
    let topMapAccessExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorTopMapId},
      rhs = tensorIdExpr} in
    let mainTensorsExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = _tensorTopsId},
      rhs = topMapAccessExpr} in
    let offsetExpr = CEBinOp {
      op = COSub (),
      lhs = CEMember {lhs = intervalExpr, id = _tensorIntervalBegin},
      rhs = CECast {
        ty = CTyInt64 (),
        rhs = CEMember {lhs = mainTensorsExpr, id = _topTensorOCaml}}} in
    let setTensorDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorDataKey,
      rhs = CECast {
        ty = CTyPtr {ty = t.elemTy},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CECast {
            ty = CTyInt64 (),
            rhs = CEMember {lhs = mainTensorsExpr, id = _topTensorCuda}},
          rhs = offsetExpr}}}} in
    [ tensorDefStmt, setTensorIdStmt, incrementTensorCountStmt
    , setTensorRankStmt, iterInitStmt, updateDimsLoopStmt, setTensorSizeStmt
    , setTensorDataStmt ]
  | CudaRecordRepr t ->
    let dst = CEVar {id = dstIdent} in
    let generateMarshallingField : [CStmt] -> (CDataRepr, Int) -> [CStmt] =
      lam acc. lam fieldIdx.
      match fieldIdx with (field, idx) in
      let valueType = CTyVar {id = _getIdentExn "value"} in
      let srcExpr = CEApp {
        fun = _getIdentExn "Field",
        args = [src, CEInt {i = idx}]} in
      let labelId : Name = nameNoSym (sidToString (get t.labels idx)) in
      let fieldDstIdent = nameSym "cuda_rec_field" in
      let innerStmts = _generateOCamlToCudaWrapperStmts env srcExpr fieldDstIdent field in
      let fieldUpdateStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = _accessMember t.ty dst labelId,
        rhs = CEVar {id = fieldDstIdent}}} in
      join [acc, innerStmts, [fieldUpdateStmt]]
    in
    let indexedFields = create (length t.fields) (lam i. (get t.fields i, i)) in
    let recordInitExpr =
      match t.ty with CTyPtr {ty = ty} then
        let sizeExpr = CESizeOfType {ty = ty} in
        Some (CECast {ty = t.ty, rhs = CEApp {fun = _malloc, args = [sizeExpr]}})
      else None () in
    let recordDefStmt = CSDef {
      ty = t.ty, id = Some dstIdent,
      init = optionMap (lam e. CIExpr {expr = e}) recordInitExpr} in
    cons
      recordDefStmt
      (foldl generateMarshallingField [] indexedFields)
  | CudaDataTypeRepr t ->
    let sizeExpr = CESizeOfType {ty = t.ty} in
    let tagValExpr = CEApp {fun = nameNoSym "Tag_val", args = [src]} in
    let unknownTagStmt = CSExpr {expr = CEApp {
      fun = _printf,
      args = [
        CEString {s = "Unknown constructor with tag %d\n"},
        tagValExpr]}} in
    let dst = CEVar {id = dstIdent} in
    let dstAllocStmt = CSDef {
      ty = t.ty, id = Some dstIdent,
      init = Some (CIExpr {expr = CECast {
        ty = t.ty,
        rhs = CEApp {
          fun = _malloc,
          args = [CESizeOfType {ty = _stripPointer t.ty}]}}})} in
    let dst = CEVar {id = dstIdent} in
    -- NOTE(larshum, 2022-03-29): Use a counter to keep track of which
    -- constructor we are currently at.
    let counter = ref 0 in
    let constructorInitStmt =
      mapFoldWithKey
        (lam acc : CStmt. lam constrId : Name. lam v : (CType, CDataRepr).
          match v with (constrTy, constrData) in
          let setConstrStmt = CSExpr {expr = CEBinOp {
            op = COAssign (),
            lhs = CEArrow {lhs = dst, id = _constrKey},
            rhs = CEVar {id = constrId}}} in
          let innerId = nameSym "cuda_constr_inner_tmp" in
          let getFieldFirst : CExpr -> CExpr = lam expr.
            CEApp {fun = _getIdentExn "Field", args = [expr, CEInt {i = 0}]} in
          let srcExpr =
            match constrData with CudaRecordRepr _ then src
            else getFieldFirst src in
          let setTempStmts =
            _generateOCamlToCudaWrapperStmts env srcExpr innerId constrData in
          let setValueStmt = CSExpr {expr = CEBinOp {
            op = COAssign (),
            lhs = CEArrow {lhs = dst, id = constrId},
            rhs = CEVar {id = innerId}}} in
          let body = join [[setConstrStmt], setTempStmts, [setValueStmt]] in
          let count = deref counter in
          (modref counter (addi count 1));
          CSIf {
            cond = CEBinOp {
              op = COEq (),
              lhs = tagValExpr,
              rhs = CEInt {i = count}},
            thn = body, els = [acc]})
        unknownTagStmt t.constrs in
    [dstAllocStmt, constructorInitStmt]
  | CudaBaseTypeRepr t ->
    [ CSDef {ty = t.ty, id = Some dstIdent, init = Some (CIExpr {expr = CEApp {
        fun = ocamlToCConversionFunctionIdent t.ty,
        args = [src]}})} ]

  sem _generateOCamlToCudaWrapperArg : CWrapperEnv -> [CStmt] -> ArgData -> [CStmt]
  sem _generateOCamlToCudaWrapperArg env acc =
  | {mexprIdent = mid, copyStatus = cs, gpuIdent = gid, cData = cdata} ->
    let src = CEVar {id = mid} in
    concat acc (_generateOCamlToCudaWrapperStmts env src gid cdata)

  sem generateOCamlToCudaWrapper : CWrapperEnv -> [CStmt]
  sem generateOCamlToCudaWrapper =
  | env ->
    let resetTensorCountStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = _tensorCountId}, rhs = CEInt {i = 0}}} in
    let freeTopMap = CSExpr {expr = CEApp {
      fun = _free, args = [CEVar {id = _tensorTopMapId}]}} in
    let freeIntervals = CSExpr {expr = CEApp {
      fun = _free, args = [CEVar {id = _tensorIntervalsId}]}} in
    join [ [resetTensorCountStmt]
         , foldl (_generateOCamlToCudaWrapperArg env) [] env.arguments
         , [freeTopMap, freeIntervals] ]
end

lang CudaCallWrapper = CudaCWrapperBase
  sem generateCudaWrapperCall : CWrapperEnv -> [CStmt]
  sem generateCudaWrapperCall =
  | env ->
    match env.targetEnv with CudaTargetEnv cenv in
    let return : ArgData = env.return in
    let returnType = return.mexprType in
    let cudaType = getCudaType env.targetEnv returnType in
    let args : [CExpr] =
      map
        (lam arg : ArgData. CEVar {id = arg.gpuIdent})
        env.arguments in
    let cudaWrapperId =
      match mapLookup env.functionIdent cenv.wrapperMap with Some id then id
      else error "Internal compiler error: No function defined for wrapper map" in
    match return.cData with CudaRecordRepr {fields = []} then
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
end

lang CudaToOCamlWrapper = CudaCWrapperBase
  sem _generateCudaToOCamlWrapperH : CWrapperEnv -> CExpr -> CExpr -> CDataRepr
                                  -> [CStmt]
  sem _generateCudaToOCamlWrapperH env src dst =
  | CudaSeqRepr t ->
    let lengthExpr = _accessMember t.ty src _seqLenKey in
    let tagExpr =
      match t.elemTy with CTyFloat _ | CTyDouble _ then
        CEVar {id = _getIdentExn "Double_array_tag"}
      else CEInt {i = 0} in
    let seqAllocStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = src,
      rhs = CEApp {
        fun = _getIdentExn "caml_alloc", args = [lengthExpr, tagExpr]}}} in
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let srcExpr = CEBinOp {op = COSubScript (), lhs = dst, rhs = iter} in
    let fieldStoreStmts =
      match t.elemTy with CTyFloat _ | CTyDouble _ then
        [ CSExpr {expr = CEApp {
            fun = _getIdentExn "Store_double_field",
            args = [dst, iter, srcExpr]}} ]
      else
        let fieldId = nameSym "cuda_seq_temp" in
        let field = CEVar {id = fieldId} in
        let fieldDefStmt = CSDef {
          ty = t.elemTy, id = Some fieldId, init = None ()} in
        let innerStmts = _generateCudaToOCamlWrapperH env srcExpr field t.data in
        let storeFieldStmt = CSExpr {expr = CEApp {
          fun = _getIdentExn "Store_field",
          args = [dst, iter, CEVar {id = fieldId}]}} in
        join [[fieldDefStmt], innerStmts, [storeFieldStmt]] in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let storeLoopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = lengthExpr},
      body = snoc fieldStoreStmts iterIncrementStmt} in
    [seqAllocStmt, iterInitStmt, storeLoopStmt]
  | CudaTensorRepr t ->
    error "Tensors cannot be returned from accelerated code"
  | CudaRecordRepr t ->
    if null t.fields then []
    else
      let wrapField = lam idx : Int. lam field : CDataRepr.
        let labelId = nameNoSym (sidToString (get t.labels idx)) in
        let fieldSrcExpr = _accessMember t.ty src labelId in
        let tempId = nameSym "cuda_rec_tmp" in
        let temp = CEVar {id = tempId} in
        let fieldStmts = _generateCudaToOCamlWrapperH env fieldSrcExpr temp field in
        let storeStmt = CSExpr {expr = CEApp {
          fun = _getIdentExn "Store_field",
          args = [dst, CEInt {i = idx}, temp]}} in
        snoc fieldStmts storeStmt
      in
      let recordAllocStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = dst,
        rhs = CEApp {
          fun = _getIdentExn "caml_alloc",
          args = [CEInt {i = length t.fields}, CEInt {i = 0}]}}} in
      let fieldStmts = join (mapi wrapField t.fields) in
      cons recordAllocStmt fieldStmts
  | CudaDataTypeRepr t ->
    error "Data types cannot be returned from accelerated code"
  | CudaBaseTypeRepr t ->
    [ CSExpr {
        expr = CEBinOp {
          op = COAssign (),
          lhs = dst,
          rhs = CEApp {
            fun = cToOCamlConversionFunctionIdent t.ty,
            args = [CECast {ty = t.ty, rhs = src}]}}} ]

  sem generateCudaToOCamlWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    let src = CEVar {id = return.gpuIdent} in
    let dst = CEVar {id = return.mexprIdent} in
    _generateCudaToOCamlWrapperH env src dst return.cData
end

lang CudaCWrapper =
  CudaTensorWrapper + OCamlToCudaWrapper + CudaCallWrapper +
  CudaToOCamlWrapper + Cmp

  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv : Map Name Name -> CompileCEnv -> Int -> CWrapperEnv
  sem generateInitWrapperEnv wrapperMap compileCEnv =
  | tensorMaxRank ->
    let compileCEnv : CompileCEnv = compileCEnv in
    let tupleSwap = lam t : (Name, Type). match t with (x, y) in (y, x) in
    let revTypeEnv = mapFromSeq cmpType (map tupleSwap compileCEnv.typeEnv) in
    let targetEnv = CudaTargetEnv {
      wrapperMap = wrapperMap, compileCEnv = compileCEnv,
      revTypeEnv = revTypeEnv, tensorMaxRank = tensorMaxRank} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  sem generateMarshallingCode =
  | env ->
    let stmt1 = generateTensorIntervalStmts env in
    let stmt2 = generateIntervalSort env in
    let stmt3 = generateTopTensorConstruction env in
    let stmt4 = generateTensorCudaAlloc env in
    let stmt5 = generateOCamlToCudaWrapper env in
    let stmt6 = generateCudaWrapperCall env in
    let stmt7 = generateCudaToOCamlWrapper env in
    let stmt8 = generateTensorCudaDealloc env in
    join [stmt1, stmt2, stmt3, stmt4, stmt5, stmt6, stmt7, stmt8]

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode : Map Name AccelerateData -> Map Name Name
                         -> Int -> CompileCEnv -> CudaProg
  sem generateWrapperCode accelerated wrapperMap tensorMaxRank =
  | compileCEnv ->
    let env = generateInitWrapperEnv wrapperMap compileCEnv tensorMaxRank in
    let tensorTops = generateGlobalTensorTops compileCEnv in
    match generateWrapperCodeH env accelerated with (env, entryPointWrappers) in
    let entryPointTops =
      map
        (lam top : CTop. CuTTop {attrs = [CuAExternC ()], top = top})
        entryPointWrappers in
    CuPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"caml/alloc.h\"",
        "\"caml/bigarray.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\"",
        "\"cuda-utils.cuh\""
      ],
      tops = concat tensorTops entryPointTops}
end
