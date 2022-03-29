include "c/compile.mc"
include "cuda/ast.mc"
include "mexpr/ast.mc"
include "mexpr/cmp.mc"
include "pmexpr/wrapper.mc"

lang CudaCWrapperBase = PMExprCWrapper + CudaAst + MExprAst + MExprCCompile
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

      -- Identifier of a global variable used to give each tensor parameter a
      -- unique integer identifier.
      tensorCountId : Name}

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
  | ty -> Some ty

  sem getCudaType (env : TargetWrapperEnv) =
  | ty & (TyRecord {labels = labels}) ->
    if null labels then CTyVoid ()
    else match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      CTyVar {id = id}
    else
      match env with CudaTargetEnv cenv in
      infoErrorExit
        (infoTy ty)
        "Reverse type lookup failed when generating CUDA wrapper code"
  | ty & (TySeq _ | TyTensor _ | TyVariant _) ->
    match lookupTypeIdent env ty with Some (TyCon {ident = id}) then
      CTyVar {id = id}
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
    CudaSeqRepr {
      ident = nameSym "cuda_seq_tmp",
      data = _generateCudaDataRepresentation env t.ty,
      elemTy = getCudaType env.targetEnv t.ty, ty = getCudaType env.targetEnv ty}
  | ty & (TyTensor t) ->
    CudaTensorRepr {
      ident = nameSym "cuda_tensor_tmp",
      data = _generateCudaDataRepresentation env t.ty,
      elemTy = getCudaType env.targetEnv t.ty, ty = getCudaType env.targetEnv ty}
  | ty & (TyRecord t) ->
    let fields : [CDataRepr] =
      map
        (lam label : SID.
          match mapLookup label t.fields with Some ty then
            _generateCudaDataRepresentation env ty
          else infoErrorExit t.info "Inconsistent labels in record type")
        t.labels in
    CudaRecordRepr {
      ident = nameSym "cuda_rec_tmp", labels = t.labels, fields = fields,
      ty = getCudaType env.targetEnv ty}
  | ty & (TyCon {ident = ident}) ->
    -- TODO(larshum, 2022-03-29): This does not work for recursive data types.
    match env.targetEnv with CudaTargetEnv cenv in
    let typeEnv = cenv.compileCEnv.typeEnv in
    match assocSeqLookup {eq=nameEq} ident typeEnv with Some (TyVariant t) then
      let constrs : Map Name (CType, CDataRepr) =
        mapMapWithKey
          (lam constrId : Name. lam constrTy : Type.
            let constrTy =
              match constrTy with TyCon {ident = iident} then
                match assocSeqLookup {eq=nameEq} iident typeEnv with Some ty then
                  ty
                else
                  infoErrorExit (infoTy ty)
                    (join ["Could not unwrap constructor ", nameGetStr iident,
                           " of algebraic data type ", nameGetStr ident])
              else constrTy in
            ( getCudaType env.targetEnv constrTy
            , _generateCudaDataRepresentation env constrTy ))
          t.constrs in
      CudaDataTypeRepr {
        ident = nameSym "cuda_adt_tmp", constrs = constrs,
        ty = getCudaType env.targetEnv ty}
    else
      infoErrorExit
        (infoTy ty)
        (join ["Invalid algebraic data type ", nameGetStr ident])
  | ty ->
    CudaBaseTypeRepr {
      ident = nameSym "cuda_tmp",
      ty = getCudaType env.targetEnv ty}
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

  sem _generateOCamlToCudaWrapperStmts (env : CWrapperEnv) (src : CExpr)
                                       (dstIdent : Name) =
  | CudaSeqRepr t ->
    match env.targetEnv with CudaTargetEnv cenv in
    let seqDefStmt = CSDef {ty = t.ty, id = Some dstIdent, init = None ()} in
    let dst = CEVar {id = dstIdent} in
    let seqLenExpr = CEMember {lhs = dst, id = _seqLenKey} in
    let setLenStmt = CSExpr {expr = CEBinOp {
      op = COAssign (), lhs = seqLenExpr, rhs = _wosize src}} in
    let elemTy =
      match t.data with CudaDataTypeRepr _ then CTyPtr {ty = t.elemTy}
      else t.elemTy in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = _wosize src,
      rhs = CESizeOfType {ty = elemTy}} in
    let allocSeqStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = CEVar {id = dstIdent}, id = _seqKey},
      rhs = CECast {
        ty = CTyPtr {ty = elemTy},
        rhs = CEApp {fun = _getIdentExn "malloc", args = [sizeExpr]}}}} in

    let iterIdent = nameSym "i" in
    let iter = CEVar {id = iterIdent} in
    let iterDefStmt = CSDef {
      ty = CTyInt64 (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let fieldDstExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEMember {lhs = dst, id = _seqKey},
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
    match env.targetEnv with CudaTargetEnv cenv in
    let bigarrayValId = _getIdentExn "Caml_ba_array_val" in
    let dst = CEVar {id = dstIdent} in
    let tensorDefStmt = CSDef {ty = t.ty, id = Some dstIdent, init = None ()} in
    let rankExpr = CEMember {lhs = dst, id = _tensorRankKey} in
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
    let setTensorDimStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = dst, id = _tensorDimsKey},
        rhs = CEVar {id = i}},
      rhs = dimExpr (CEVar {id = i})}} in
    let incrementIterStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {op = COAdd (), lhs = CEVar {id = i}, rhs = CEInt {i = 1}}}} in
    let dimLoopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = CEMember {lhs = dst, id = _tensorRankKey}},
      body = [setTensorDimStmt, incrementIterStmt]} in

    let setTensorDataStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _tensorDataKey},
      rhs = CECast {
        ty = CTyPtr {ty = t.elemTy},
        rhs = CEApp {fun = _getIdentExn "Caml_ba_data_val", args = [src]}}}} in
    let setTensorOffsetStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _tensorOffsetKey},
      rhs = CEInt {i = 0}}} in
    let setTensorIdStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEMember {lhs = dst, id = _tensorIdKey},
      rhs = CEVar {id = cenv.tensorCountId}}} in
    let incrementTensorCountStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = cenv.tensorCountId},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = cenv.tensorCountId},
        rhs = CEInt {i = 1}}}} in
    [ tensorDefStmt, setTensorRankStmt, rankErrorStmt, iterInitStmt
    , dimLoopStmt, setTensorDataStmt, setTensorOffsetStmt , setTensorIdStmt
    , incrementTensorCountStmt ]
  | CudaRecordRepr t ->
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
        lhs = CEMember {lhs = CEVar {id = dstIdent}, id = labelId},
        rhs = CEVar {id = fieldDstIdent}}} in
      join [acc, innerStmts, [fieldUpdateStmt]]
    in
    let indexedFields = create (length t.fields) (lam i. (get t.fields i, i)) in
    let recordDeclStmt = CSDef {ty = t.ty, id = Some dstIdent, init = None ()} in
    cons
      recordDeclStmt
      (foldl generateMarshallingField [] indexedFields)
  | CudaDataTypeRepr t ->
    let sizeExpr = CESizeOfType {ty = CTyPtr {ty = t.ty}} in
    let tagValExpr = CEApp {fun = nameNoSym "Tag_val", args = [src]} in
    let unknownTagStmt = CSExpr {expr = CEApp {
      fun = _printf,
      args = [
        CEString {s = "Unknown constructor with tag %d\n"},
        tagValExpr]}} in
    let dst = CEVar {id = dstIdent} in
    let dstAllocStmt = CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some dstIdent,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = t.ty},
        rhs = CEApp {
          fun = _malloc,
          args = [CESizeOfType {ty = t.ty}]}}})} in
    let dst = CEVar {id = dstIdent} in
    -- NOTE(larshum, 2022-03-29): Use a counter to keep track of which
    -- constructor we are currently at.
    let counter = ref 0 in
    let constructorInitStmt = mapFoldWithKey
        (lam acc : CStmt. lam constrId : Name. lam v : (CType, CDataRepr).
          match v with (constrTy, constrData) in
          let setConstrStmt = CSExpr {expr = CEBinOp {
            op = COAssign (),
            lhs = CEArrow {lhs = dst, id = _constrKey},
            rhs = CEVar {id = constrId}}} in
          let innerId = nameSym "cuda_constr_inner_tmp" in
          let srcExpr =
            match constrData with CudaRecordRepr _ then src
            else CEApp {fun = _getIdentExn "Field", args = [src, CEInt {i = 0}]} in
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

  sem _generateOCamlToCudaWrapperArg (env : CWrapperEnv) (acc : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    let src = CEVar {id = arg.mexprIdent} in
    concat acc (_generateOCamlToCudaWrapperStmts env src arg.gpuIdent arg.cData)

  sem generateOCamlToCudaWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with CudaTargetEnv cenv in
    let defTensorCountStmt = CSDef {
      ty = CTyInt64 (), id = Some cenv.tensorCountId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    cons
      defTensorCountStmt
      (foldl (_generateOCamlToCudaWrapperArg env) [] env.arguments)
end

lang CudaCallWrapper = CudaCWrapperBase
  sem _generateDeallocArg (arg : CExpr) =
  | CudaSeqRepr t ->
    let iterId = nameSym "i" in
    let iter = CEVar {id = iterId} in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterId,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let innerArg = CEBinOp {
      op = COSubScript (),
      lhs = CEMember {lhs = arg, id = _seqKey},
      rhs = iter} in
    let innerFreeStmts = _generateDeallocArg innerArg t.data in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = iter,
      rhs = CEBinOp {op = COAdd (), lhs = iter, rhs = CEInt {i = 1}}}} in
    let lengthExpr = CEMember {lhs = arg, id = _seqLenKey} in
    let loopStmt = CSWhile {
      cond = CEBinOp {op = COLt (), lhs = iter, rhs = lengthExpr},
      body = snoc innerFreeStmts iterIncrementStmt} in
    let freeSeqStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free",
      args = [CEMember {lhs = arg, id = _seqKey}]}} in
    [ iterInitStmt, loopStmt, freeSeqStmt ]
  | CudaDataTypeRepr t ->
    [ CSExpr {expr = CEApp {fun = _getIdentExn "free", args = [arg]}} ]
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
        (lam arg : ArgData. CEVar {id = arg.gpuIdent})
        env.arguments in
    let cudaWrapperId =
      match mapLookup env.functionIdent cenv.wrapperMap with Some id then id
      else error "Internal compiler error: No function defined for wrapper map" in
    let callStmts =
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
    in

    -- Deallocate argument parameters
    let deallocStmts =
      join
        (map
          (lam arg : ArgData.
            let argExpr = CEVar {id = arg.gpuIdent} in
            _generateDeallocArg argExpr arg.cData)
          env.arguments) in

    concat callStmts deallocStmts
end

lang CudaToOCamlWrapper = CudaCWrapperBase
  sem _generateCudaToOCamlWrapperH (env : CWrapperEnv) (src : CExpr) (dst : CExpr) =
  | CudaSeqRepr t ->
    -- Directly write to the OCaml value... First we need to allocate memory
    let lengthExpr = CEMember {lhs = src, id = _seqLenKey} in
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
    let rankExpr = CEMember {lhs = src, id = _tensorRankKey} in
    let dataExpr = CEMember {lhs = src, id = _tensorDataKey} in
    let dimsExpr = CEMember {lhs = src, id = _tensorDimsKey} in
    [ CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = dst,
        rhs = CEApp {
          fun = _getIdentExn "caml_ba_alloc",
          args = [bigarrayLayoutKind, rankExpr, dataExpr, dimsExpr]}}} ]
  | CudaRecordRepr t ->
    if null t.fields then []
    else
      let wrapField = lam idx : Int. lam field : CDataRepr.
        let labelId = nameNoSym (sidToString (get t.labels idx)) in
        let fieldSrcExpr = CEMember {lhs = src, id = labelId} in
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

lang CudaCWrapper =
  OCamlToCudaWrapper + CudaCallWrapper + CudaToOCamlWrapper + Cmp

  -- Generates the initial wrapper environment
  sem generateInitWrapperEnv (wrapperMap : Map Name Name) =
  | compileCEnv ->
    let compileCEnv : CompileCEnv = compileCEnv in
    let tupleSwap = lam t : (a, b). match t with (x, y) in (y, x) in
    let revTypeEnv = mapFromSeq cmpType (map tupleSwap compileCEnv.typeEnv) in
    let targetEnv = CudaTargetEnv {
      wrapperMap = wrapperMap, compileCEnv = compileCEnv,
      revTypeEnv = revTypeEnv, tensorCountId = nameSym "tensor_count"} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  sem generateMarshallingCode =
  | env ->
    let stmt1 = generateOCamlToCudaWrapper env in
    let stmt2 = generateCudaWrapperCall env in
    let stmt3 = generateCudaToOCamlWrapper env in
    join [stmt1, stmt2, stmt3]

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
