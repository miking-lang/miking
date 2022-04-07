include "cuda/ast.mc"
include "cuda/compile.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "pmexpr/wrapper.mc"

let _tensorStateOk = nameSym "STATE_OK"
let _tensorStateCpuInvalid = nameSym "STATE_CPU_INVALID"
let _tensorStateGpuInvalid = nameSym "STATE_GPU_INVALID"
let _tensorStateReturned = nameSym "STATE_RETURNED"
let _tensorStateNames =
  [ _tensorStateOk, _tensorStateCpuInvalid, _tensorStateGpuInvalid
  , _tensorStateReturned ]

let _tensorCountId = nameSym "tensor_count"
let _tensorStateData = nameSym "t_state"
let _stateEnumId = nameSym "tensor_state"

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
      compileCEnv : CompileCEnv}

  sem lookupTypeIdent (env : TargetWrapperEnv) =
  | TyRecord {labels = []} -> None ()
  | TyRecord t ->
    match env with CudaTargetEnv cenv in
    let fields : Option [(SID, Type)] =
      optionMapM
        (lam f : (SID, Type).
          match f with (key, ty) in
          match lookupTypeIdent env ty with Some ty then
            Some (key, ty)
          else None ())
        (mapBindings t.fields) in
    match fields with Some fieldsSeq then
      let fields = mapFromSeq cmpSID fieldsSeq in
      let ty = TyRecord {t with fields = fields} in
      optionMap
        (lam id. TyCon {ident = id, info = t.info})
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
      Some (TyCon {ident = id, info = infoTy ty})
    else None ()
  | ty & (TyVariant _) ->
    match env with CudaTargetEnv cenv in
    match mapLookup ty cenv.revTypeEnv with Some id then
      Some (TyCon {ident = id, info = infoTy ty})
    else None ()
  | ty -> Some ty

  sem getCudaType (env : TargetWrapperEnv) =
  | ty & (TyRecord {labels = labels}) ->
    match env with CudaTargetEnv cenv in
    if null labels then CTyVoid ()
    else match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      if any (nameEq id) cenv.compileCEnv.ptrTypes then
        CTyPtr {ty = CTyVar {id = id}}
      else CTyVar {id = id}
    else
      infoErrorExit
        (infoTy ty)
        "Reverse type lookup failed when generating CUDA wrapper code"
  | ty & (TySeq _ | TyTensor _ | TyVariant _) ->
    match env with CudaTargetEnv cenv in
    match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      if any (nameEq id) cenv.compileCEnv.ptrTypes then
        CTyPtr {ty = CTyVar {id = id}}
      else CTyVar {id = id}
    else
      infoErrorExit
        (infoTy ty)
        "Reverse type lookup failed when generating CUDA wrapper code"
  | ty ->
    match env with CudaTargetEnv cenv in
    compileType cenv.compileCEnv ty

  sem _generateCDataRepresentation (env : CWrapperEnv) =
  | ty -> _generateCudaDataRepresentation env ty

  sem _generateCudaDataRepresentation (env : CWrapperEnv) =
  | ty & (TySeq t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let elemTy = _unwrapType cenv.compileCEnv.typeEnv t.ty in
    CudaSeqRepr {
      ident = nameSym "cuda_seq_tmp",
      data = _generateCudaDataRepresentation env elemTy,
      elemTy = getCudaType env.targetEnv t.ty, ty = getCudaType env.targetEnv ty}
  | ty & (TyTensor t) ->
    CudaTensorRepr {
      ident = nameSym "cuda_tensor_tmp",
      data = _generateCudaDataRepresentation env t.ty,
      elemTy = getCudaType env.targetEnv t.ty, ty = getCudaType env.targetEnv ty}
  | ty & (TyRecord t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let fields : [CDataRepr] =
      map
        (lam label : SID.
          match mapLookup label t.fields with Some ty then
            let ty = _unwrapType cenv.compileCEnv.typeEnv ty in
            _generateCudaDataRepresentation env ty
          else infoErrorExit t.info "Inconsistent labels in record type")
        t.labels in
    CudaRecordRepr {
      ident = nameSym "cuda_rec_tmp", labels = t.labels, fields = fields,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyVariant t) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let constrs : Map Name (CType, CDataRepr) =
      mapMapWithKey
        (lam constrId : Name. lam constrTy : Type.
          let constrTy = _unwrapType cenv.compileCEnv.typeEnv constrTy in
          ( getCudaType env.targetEnv constrTy
          , _generateCudaDataRepresentation env constrTy ))
        t.constrs in
    CudaDataTypeRepr {
      ident = nameSym "cuda_adt_tmp", constrs = constrs,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyCon _) ->
    match env.targetEnv with CudaTargetEnv cenv in
    let ty = _unwrapType cenv.compileCEnv.typeEnv ty in
    match ty with TyCon _ then infoErrorExit (infoTy ty) "Could not unwrap type"
    else  _generateCudaDataRepresentation env ty
  | ty ->
    CudaBaseTypeRepr {
      ident = nameSym "cuda_tmp",
      ty = getCudaType env.targetEnv ty}
end

lang CudaTensorWrapper = CudaCWrapperBase
  sem generateGlobalTensorTops =
  | () ->
    let stateEnumTop = CuTTop {
      attrs = [],
      top = CTDef {
        ty = CTyEnum {id = Some _stateEnumId, mem = Some _tensorStateNames},
        id = None (), init = None ()}} in
    let stateEnumType = CTyEnum {id = Some _stateEnumId, mem = None ()} in
    let stateTopDecl = CuTTop {
      attrs = [CuAManaged ()],
      top = CTDef {
        ty = CTyPtr {ty = stateEnumType},
        id = Some _tensorStateData,
        init = None ()}} in
    [stateEnumTop, stateTopDecl]

  sem _generateTensorDataInitWrapperStmts
    : CWrapperEnv -> CExpr -> CDataRepr -> [CStmt]
  sem _generateTensorDataInitWrapperStmts env src =
  | CudaSeqRepr t ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let innerSrc = CEBinOp {
      op = COSubScript (),
      lhs = _accessMember t.ty src _seqKey,
      rhs = iter} in
    let innerInitStmts =
      _generateTensorDataInitWrapperStmts env innerSrc t.data in
    if null innerInitStmts then []
    else
      let iterInitStmt = CSDef {
        ty = CTyInt64 (), id = Some iterId,
        init = Some (CIExpr {expr = CEInt {i = 0}})} in
      let iterIncrementStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = iter,
        rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
      let lenExpr = _accessMember t.ty src _seqLenKey in
      let loopStmt = CSWhile {
        cond = CEBinOp {op = COLt (), lhs = iter, rhs = lenExpr},
        body = snoc innerInitStmts iterIncrementStmt} in
      [iterInitStmt, loopStmt]
  | CudaTensorRepr t ->
    let stateInitStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorStateData},
        rhs = _accessMember t.ty src _tensorIdKey},
      rhs = CEVar {id = _tensorStateOk}}} in
    [ stateInitStmt ]
  | CudaRecordRepr t ->
    foldl
      (lam acc. lam field : (SID, CDataRepr).
        match field with (key, fieldRepr) in
        let fieldId = nameNoSym (sidToString key) in
        let innerSrc = _accessMember t.ty src fieldId in
        concat acc (_generateTensorDataInitWrapperStmts env innerSrc fieldRepr))
      [] (zip t.labels t.fields)
  | CudaDataTypeRepr t ->
    let counter = ref 0 in
    mapFoldWithKey
      (lam acc. lam constrId. lam constrTyData.
        match constrTyData with (constrTy, constrData) in
        let constrExpr = _accessMember t.ty src constrId in
        let count = deref counter in
        (modref counter (addi count 1));
        let innerStmts =
          _generateTensorDataInitWrapperStmts env constrExpr constrData in
        if null innerStmts then acc
        else
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = _accessMember t.ty src _constrKey,
                rhs = CEInt {i = count}},
              thn = innerStmts,
              els = acc} ])
      [] t.constrs
  | CudaBaseTypeRepr _ -> []

  sem _generateCudaTensorDataWrapperArg : CWrapperEnv -> [CStmt] -> ArgData
                                       -> [CStmt]
  sem _generateCudaTensorDataWrapperArg env acc =
  | arg ->
    let arg : ArgData = arg in
    let src = CEVar {id = arg.gpuIdent} in
    concat acc (_generateTensorDataInitWrapperStmts env src arg.cData)

  sem _generateTensorDataAllocStmts : CWrapperEnv -> [CStmt]
  sem _generateTensorDataAllocStmts =
  | env ->
    let stateEnumType = CTyEnum {id = Some _stateEnumId, mem = None ()} in
    let allocTensorStateDataStmt =
      CSExpr {expr = CEApp {
        fun = _cudaMallocManaged,
        args = [
          CEUnOp {op = COAddrOf (), arg = CEVar {id = _tensorStateData}},
          CEBinOp {
            op = COMul (),
            lhs = CEVar {id = _tensorCountId},
            rhs = CESizeOfType {ty = stateEnumType}}]}} in
    [allocTensorStateDataStmt]

  sem generateCudaTensorDataWrapper : CWrapperEnv -> [CStmt]
  sem generateCudaTensorDataWrapper =
  | env ->
    let env : CWrapperEnv = env in
    concat
      (_generateTensorDataAllocStmts env)
      (foldl (_generateCudaTensorDataWrapperArg env) [] env.arguments)
end

lang OCamlToCudaWrapper = CudaCWrapperBase
  sem _tensorRankErrorStmt =
  | rankExpr ->
    let printErrorStmt = CSExpr {expr = CEApp {
      fun = _printf,
      args = [
        CEString {s = "Tensors with rank at most 3 are supported, found rank %ld\n"},
        rankExpr]}} in
    let exitErrorStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "exit",
      args = [CEInt {i = 1}]}} in
    CSIf {
      cond = CEBinOp {op = COGt (), lhs = rankExpr, rhs = CEInt {i = 3}},
      thn = [printErrorStmt, exitErrorStmt],
      els = []}

  sem _generateOCamlToCudaWrapperStmts : CWrapperEnv -> CExpr -> Name
                                      -> CDataRepr -> [CStmt]
  sem _generateOCamlToCudaWrapperStmts env src dstIdent =
  | CudaSeqRepr t ->
    let env : CWrapperEnv = env in
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
    [ seqDefStmt, setLenStmt, allocSeqStmt, iterDefStmt, dataCopyLoopStmt ]
  | CudaTensorRepr t ->
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv cenv in
    let bigarrayValId = _getIdentExn "Caml_ba_array_val" in
    let dst = CEVar {id = dstIdent} in
    let tensorDefStmt = CSDef {ty = t.ty, id = Some dstIdent, init = None ()} in
    let rankExpr = _accessMember t.ty dst _tensorRankKey in
    let setTensorRankStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = rankExpr,
      rhs = CEArrow {
        lhs = CEApp {fun = bigarrayValId, args = [src]},
        id = _bigarrayNumDimsKey}}} in

    -- NOTE(larshum, 2022-03-09): The current C representation of tensors
    -- supports at most 3 dimensions, so we verify that the provided tensor
    -- does not exceed this at runtime (as it is not known at compile-time).
    let rankErrorStmt = _tensorRankErrorStmt rankExpr in

    let setTensorOffsetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorOffsetKey,
      rhs = CEInt {i = 0}}} in
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
    
    let dimExpr = lam idx.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {
          lhs = CEApp {fun = bigarrayValId, args = [src]},
          id = _bigarrayDimKey},
        rhs = idx} in
    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let n = nameSym "n" in
    let sizeInitStmt = CSDef {
      ty = CTyInt64 (), id = Some n,
      init = Some (CIExpr {expr = CESizeOfType {ty = t.elemTy}})} in
    let setTensorDimStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = _accessMember t.ty dst _tensorDimsKey,
        rhs = CEVar {id = i}},
      rhs = dimExpr (CEVar {id = i})}} in
    let setMulSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = n},
      rhs = CEBinOp {
        op = COMul (),
        lhs = CEVar {id = n},
        rhs = dimExpr (CEVar {id = i})}}} in
    let incrementIterStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {op = COAdd (), lhs = CEVar {id = i}, rhs = CEInt {i = 1}}}} in
    let dimLoopBody = [setTensorDimStmt, setMulSizeStmt, incrementIterStmt] in
    let dimLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = _accessMember t.ty dst _tensorRankKey},
      body = dimLoopBody} in
    let setTensorSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorSizeKey,
      rhs = CEVar {id = n}}} in

    -- NOTE(larshum, 2022-04-04): If we are using unified memory, we allocate
    -- managed memory for the tensor and use that. Otherwise, we use the
    -- bigarray memory directly.
    let tempId = nameSym "t" in
    let emptyPtrDeclStmt = CSDef {
      ty = CTyPtr {ty = t.elemTy}, id = Some tempId, init = None ()} in
    let allocManagedStmt = CSExpr {expr = CEApp {
      fun = _cudaMallocManaged,
      args = [
        CEUnOp {op = COAddrOf (), arg = CEVar {id = tempId}},
        CEVar {id = n}]}} in
    let copyDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEVar {id = tempId},
        CEApp {fun = _getIdentExn "Caml_ba_data_val", args = [src]},
        CEVar {id = n},
        CEVar {id = _cudaMemcpyHostToDevice}]}} in
    let setTensorDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = _accessMember t.ty dst _tensorDataKey,
      rhs = CEVar {id = tempId}}} in

    [ tensorDefStmt, setTensorRankStmt, rankErrorStmt, setTensorOffsetStmt
    , setTensorIdStmt, incrementTensorCountStmt, iterInitStmt, sizeInitStmt
    , dimLoopStmt, setTensorSizeStmt, emptyPtrDeclStmt, allocManagedStmt
    , copyDataStmt , setTensorDataStmt ]
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
  | arg ->
    let arg : ArgData = arg in
    let src = CEVar {id = arg.mexprIdent} in
    concat acc (_generateOCamlToCudaWrapperStmts env src arg.gpuIdent arg.cData)

  sem generateOCamlToCudaWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let initTensorCountStmt = CSDef {
      ty = CTyInt64 (), id = Some _tensorCountId,
      init = Some (CIExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = _tensorCountId},
        rhs = CEInt {i = 0}}})} in
    cons
      initTensorCountStmt
      (foldl (_generateOCamlToCudaWrapperArg env) [] env.arguments)
end

lang CudaCallWrapper = CudaCWrapperBase
  sem generateCudaWrapperCall =
  | env ->
    let env : CWrapperEnv = env in
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
  sem _generateCudaToOCamlWrapperH (env : CWrapperEnv) (src : CExpr) (dst : CExpr) =
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
    let bigarrayKind =
      match t.elemTy with CTyInt _ | CTyInt64 _ then
        CEVar {id = _getIdentExn "CAML_BA_CAML_INT"}
      else match t.elemTy with CTyFloat _ | CTyDouble _ then
        CEVar {id = _getIdentExn "CAML_BA_FLOAT64"}
      else never in
    let bigarrayLayoutKind = CEBinOp {
      op = COBOr (),
      lhs = bigarrayKind,
      rhs = CEVar {id = _getIdentExn "CAML_BA_C_LAYOUT"}} in
    let rankExpr = _accessMember t.ty src _tensorRankKey in
    let dataExpr = _accessMember t.ty src _tensorDataKey in
    let dimsExpr = _accessMember t.ty src _tensorDimsKey in
    let allocTensorStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = dst,
      rhs = CEApp {
        fun = _getIdentExn "caml_ba_alloc",
        args = [bigarrayLayoutKind, rankExpr, dataExpr, dimsExpr]}}} in
    let setTensorStateReturnedStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = _tensorStateData},
        rhs = _accessMember t.ty src _tensorIdKey},
      rhs = CEVar {id = _tensorStateReturned}}} in
    [allocTensorStmt, setTensorStateReturnedStmt]
  | CudaRecordRepr t ->
    if null t.fields then []
    else
      let wrapField = lam idx : Int. lam field : CDataRepr.
        let labelId = nameNoSym (sidToString (get t.labels idx)) in
        let fieldSrcExpr = _accessMember t.ty src labelId in
        let tempId = nameSym "cuda_rec_tmp" in
        let temp = CEVar {id = tempId} in
        let fieldStmts = _generateCudaToOCamlWrapperH env fieldSrcExpr temp in
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

lang CudaDeallocWrapper = CudaCWrapperBase
  sem _generateDeallocArg : CWrapperEnv -> CExpr -> CExpr -> CDataRepr -> [CStmt]
  sem _generateDeallocArg env arg ocamlArg =
  | CudaSeqRepr t ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerArg = CEBinOp {
      op = COSubScript (),
      lhs = _accessMember t.ty arg _seqKey,
      rhs = iter} in
    let innerOcamlArg = CEApp {
      fun = _getIdentExn "Field", args = [ocamlArg, iter]} in
    let innerFreeStmts = _generateDeallocArg env innerArg innerOcamlArg t.data in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let lengthExpr = _accessMember t.ty arg _seqLenKey in
    let loopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = lengthExpr},
      body = snoc innerFreeStmts iterIncrementStmt} in
    let freeSeqDataStmt = CSExpr {expr = CEApp {
      fun = _cudaFree,
      args = [_accessMember t.ty arg _seqKey]}} in
    match t.ty with CTyPtr {ty = ty} then
      let freeSeqStmt = CSExpr {expr = CEApp {fun = _cudaFree, args = [arg]}} in
      [iterInitStmt, loopStmt, freeSeqDataStmt, freeSeqStmt]
    else [iterInitStmt, loopStmt, freeSeqDataStmt]
  | CudaTensorRepr t ->
    let env : CWrapperEnv = env in
    let tensorIdExpr = _accessMember t.ty arg _tensorIdKey in
    let accessIdx = lam ptrId.
      CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = ptrId},
        rhs = tensorIdExpr} in
    let copyBackTensorDataStmt = CSExpr {expr = CEApp {
      fun = _cudaMemcpy,
      args = [
        CEApp {fun = _getIdentExn "Caml_ba_data_val", args = [ocamlArg]},
        _accessMember t.ty arg _tensorDataKey,
        _accessMember t.ty arg _tensorSizeKey,
        CEVar {id = _cudaMemcpyDeviceToHost}]}} in
    let updatedCondExpr = CEBinOp {
      op = CONeq (),
      lhs = accessIdx _tensorStateData,
      rhs = CEVar {id = _tensorStateOk}} in
    let copyIfUpdatedStmt = CSIf {
      cond = updatedCondExpr,
      thn = [copyBackTensorDataStmt],
      els = []} in
    let freeDataStmt = CSExpr {expr = CEApp {
      fun = _cudaFree,
      args = [_accessMember t.ty arg _tensorDataKey]}} in
    let notReturnedCondExpr = CEBinOp {
      op = CONeq (),
      lhs = accessIdx _tensorStateData,
      rhs = CEVar {id = _tensorStateReturned}} in
    let freeIfNotReturnedStmt = CSIf {
      cond = notReturnedCondExpr,
      thn = [freeDataStmt],
      els = []} in
    [copyIfUpdatedStmt, freeIfNotReturnedStmt]
  | CudaRecordRepr t ->
    let fieldCounter = ref 0 in
    let generateDeallocField : [CStmt] -> (SID, CDataRepr) -> [CStmt] =
      lam acc. lam sidAndField.
      match sidAndField with (sid, field) in
      let innerArg = _accessMember t.ty arg (nameNoSym (sidToString sid)) in
      let fieldIdx = deref fieldCounter in
      (modref fieldCounter (addi fieldIdx 1));
      let innerOcamlArg = CEApp {
        fun = _getIdentExn "Field",
        args = [ocamlArg, CEInt {i = fieldIdx}]} in
      let innerFreeStmts = _generateDeallocArg env innerArg innerOcamlArg field in
      concat acc innerFreeStmts
    in
    let freeFieldStmts = foldl generateDeallocField [] (zip t.labels t.fields) in
    match t.ty with CTyPtr _ then
      let freeRecordStmt = CSExpr {expr = CEApp {fun = _free, args = [arg]}} in
      snoc freeFieldStmts freeRecordStmt
    else freeFieldStmts
  | CudaDataTypeRepr t ->
    let counter = ref 0 in
    let constructorFreeStmts =
      mapFoldWithKey
        (lam acc : [CStmt]. lam constrId : Name. lam v : (CType, CDataRepr).
          match v with (constrTy, constrData) in
          let constrIdx = deref counter in
          (modref counter (addi constrIdx 1));
          let innerArg = CEArrow {lhs = arg, id = constrId} in
          let innerFreeStmts = _generateDeallocArg env innerArg ocamlArg constrData in
          [ CSIf {
              cond = CEBinOp {
                op = COEq (),
                lhs = CEArrow {lhs = arg, id = _constrKey},
                rhs = CEInt {i = constrIdx}},
              thn = innerFreeStmts,
              els = acc} ])
        [] t.constrs in
    let freeVariantStmt = CSExpr {expr = CEApp {
      fun = _free, args = [arg]}} in
    snoc constructorFreeStmts freeVariantStmt

  | CudaBaseTypeRepr _ -> []
  sem generateCudaDeallocWrapper : CWrapperEnv -> [CStmt]
  sem generateCudaDeallocWrapper =
  | env ->
    let env : CWrapperEnv = env in

    -- Deallocate argument parameters
    let deallocStmts =
      join
        (map
          (lam arg : ArgData.
            let argExpr = CEVar {id = arg.gpuIdent} in
            let ocamlExpr = CEVar {id = arg.mexprIdent} in
            _generateDeallocArg env argExpr ocamlExpr arg.cData)
          env.arguments) in

    -- Free global tensor state data
    let freeTensorStateDataStmt = CSExpr {expr = CEApp {
      fun = _cudaFree, args = [CEVar {id = _tensorStateData}]}} in

    snoc deallocStmts freeTensorStateDataStmt
end

lang CudaCWrapper =
  CudaTensorWrapper + OCamlToCudaWrapper + CudaCallWrapper +
  CudaToOCamlWrapper + CudaDeallocWrapper + Cmp

  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv : Map Name Name -> CompileCEnv -> CWrapperEnv
  sem generateInitWrapperEnv wrapperMap =
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
    let stmt1 = generateOCamlToCudaWrapper env in
    let stmt2 = generateCudaTensorDataWrapper env in
    let stmt3 = generateCudaWrapperCall env in
    let stmt4 = generateCudaToOCamlWrapper env in
    let stmt5 = generateCudaDeallocWrapper env in
    join [stmt1, stmt2, stmt3, stmt4, stmt5]

  -- Defines the target-specific generation of wrapper code.
  sem generateWrapperCode : Map Name AccelerateData -> Map Name Name
                         -> CompileCEnv -> CudaProg
  sem generateWrapperCode accelerated wrapperMap =
  | compileCEnv ->
    let env = generateInitWrapperEnv wrapperMap compileCEnv in
    let tensorTops = generateGlobalTensorTops () in
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
        "\"caml/mlvalues.h\""
      ],
      tops = concat tensorTops entryPointTops}
end
