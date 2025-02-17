include "map.mc"
include "string.mc"
include "c/ast.mc"
include "c/pprint.mc"
include "futhark/pprint.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/record.mc"
include "pmexpr/extract.mc"
include "pmexpr/wrapper.mc"

let getFutharkSeqTypeString : String -> Int -> String =
  lam futharkElementTypeString. lam numDims.
  join [futharkElementTypeString, "_", int2string numDims, "d"]

lang FutharkCWrapperBase = PMExprCWrapper + RecordTypeUtils
  -- Definition of the intermediate representation definitions for the Futhark
  -- backend. Note that nested sequences are treated as one 'FutharkSeqRepr',
  -- and that sequences can only contain base types.
  syn CDataRepr =
  | FutharkSeqRepr {ident : Name, data : CDataRepr, dimIdents : [Name],
                    sizeIdent : Name, elemTy : CType}
  | FutharkRecordRepr {fields : [CDataRepr]}
  | FutharkBaseTypeRepr {ident : Name, ty : CType}

  -- In the Futhark-specific environment, we store identifiers related to the
  -- Futhark context config and the context.
  syn TargetWrapperEnv =
  | FutharkTargetEnv {
      initContextIdent : Name, futharkContextConfigIdent : Name,
      futharkContextIdent : Name}

  sem getFutharkElementTypeString : CType -> String
  sem getFutharkElementTypeString =
  | CTyChar _ | CTyInt64 _ -> "i64"
  | CTyDouble _ -> "f64"
  | CTyPtr t -> getFutharkElementTypeString t.ty

  sem getSeqFutharkTypeString : CDataRepr -> String
  sem getSeqFutharkTypeString =
  | FutharkSeqRepr t ->
    let elemTyStr = getFutharkElementTypeString t.elemTy in
    let dims = length t.dimIdents in
    join [elemTyStr, "_", int2string dims, "d"]

  sem getFutharkCType : CDataRepr -> CType
  sem getFutharkCType =
  | t & (FutharkSeqRepr _) ->
    let seqTypeStr = getSeqFutharkTypeString t in
    let seqTypeIdent = _getIdentOrInitNew (concat "futhark_" seqTypeStr) in
    CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}}
  | FutharkRecordRepr t ->
    -- TODO(larshum, 2022-03-09): How do we figure out this type?
    error "Records have not been implemented for Futhark"
  | FutharkBaseTypeRepr t -> t.ty

  sem mexprToCType : Type -> CType
  sem mexprToCType =
  | TyInt _ -> CTyInt64 ()
  | TyFloat _ -> CTyDouble ()
  | TyBool _ -> CTyChar ()
  | TyChar _ -> CTyChar ()
  | ty ->
    let tystr = use MExprPrettyPrint in type2str ty in
    errorSingle [infoTy ty]
      (join ["Type ", tystr, " cannot be passed to accelerated expressions ",
             "using the functional backend."])

  sem _generateCDataRepresentation : CWrapperEnv -> Type -> CDataRepr
  sem _generateCDataRepresentation env =
  | TySeq ty ->
    recursive let findSequenceDimensions = lam n. lam ty.
      match ty with TySeq t then
        findSequenceDimensions (addi n 1) t.ty
      else (n, ty)
    in
    match findSequenceDimensions 0 (TySeq ty) with (dims, elemType) in
    if isBaseType elemType then
      let dimIdents = create dims (lam. nameSym "d") in
      FutharkSeqRepr {
        ident = nameSym "seq_tmp", data = _generateCDataRepresentation env ty.ty,
        dimIdents = dimIdents, sizeIdent = nameSym "n",
        elemTy = mexprToCType elemType}
    else
      let tystr = use MExprPrettyPrint in type2str (TySeq ty) in
      errorSingle [ty.info] (join ["Sequences of ", tystr, " are not supported in Futhark wrapper"])
  | TyTensor {info = info} ->
    errorSingle [info] "Tensors are not supported in Futhark wrapper"
  | (TyRecord t) & ty ->
    let labels = tyRecordOrderedLabels ty in
    let fields : [CDataRepr] =
      map
        (lam label : SID.
          match mapLookup label t.fields with Some ty then
            _generateCDataRepresentation env ty
          else
            errorSingle [t.info] "Inconsistent labels in record type")
        labels in
    FutharkRecordRepr {fields = fields}
  | ty -> FutharkBaseTypeRepr {ident = nameSym "c_tmp", ty = mexprToCType ty}
end

lang FutharkOCamlToCWrapper = FutharkCWrapperBase
  sem _computeSequenceDimensions : Name -> Int -> CDataRepr -> [CStmt]
  sem _computeSequenceDimensions srcIdent idx =
  | t & (FutharkSeqRepr {dimIdents = dimIdents, sizeIdent = sizeIdent}) ->
    let dimIdent = get dimIdents idx in
    let initDimStmt = CSDef {
      ty = CTyInt64 (), id = Some dimIdent,
      init = Some (CIExpr {expr = _wosize (CEVar {id = srcIdent})})} in
    let updateSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = sizeIdent},
      rhs = CEBinOp {
        op = COMul (),
        lhs = CEVar {id = sizeIdent},
        rhs = CEVar {id = dimIdent}}}} in
    let idx = addi idx 1 in
    if eqi idx (length dimIdents) then [initDimStmt, updateSizeStmt]
    else
      let innerSrcIdent = nameSym "t" in
      -- NOTE(larshum, 2022-03-09): We assume sequences are non-empty here.
      let innerSrcStmt = CSDef {
        ty = CTyVar {id = _getIdentExn "value"},
        id = Some innerSrcIdent,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEInt {i = 0}]}})} in
      let stmts = _computeSequenceDimensions innerSrcIdent idx t in
      concat [initDimStmt, updateSizeStmt, innerSrcStmt] stmts

  sem _generateForLoop : Name -> Name -> [CStmt] -> [CStmt]
  sem _generateForLoop iterIdent dimIdent =
  | bodyWithoutIterIncrement ->
    let iterDefStmt = CSDef {
      ty = CTyInt64 (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let iterIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = iterIdent},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = iterIdent},
        rhs = CEInt {i = 1}}}} in
    [ iterDefStmt
    , CSWhile {
        cond = CEBinOp {
          op = COLt (),
          lhs = CEVar {id = iterIdent},
          rhs = CEVar {id = dimIdent}},
        body = snoc bodyWithoutIterIncrement iterIncrementStmt} ]

  sem _allocateSequenceCDataH : CType -> Name -> Name -> [Name] -> [CStmt]
  sem _allocateSequenceCDataH elemTy srcIdent dstIdent =
  | [dimIdent] ++ dimIdents ->
    let iterIdent = nameSym "i" in
    let innerSrcIdent = nameSym "x" in
    let innerDstIdent = nameSym "y" in
    let valueTy = CTyVar {id = _getIdentExn "value"} in
    let innerSrcInitStmt = CSDef {
      ty = valueTy, id = Some innerSrcIdent,
      init = Some (CIExpr {expr = CEApp {
        fun = _getIdentExn "Field",
        args = [CEVar {id = srcIdent}, CEVar {id = iterIdent}]}})} in
    let offsetExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = iterIdent},
      rhs = _wosize (CEVar {id = innerSrcIdent})} in
    let innerCopyStmt = CSDef {
      ty = CTyPtr {ty = elemTy}, id = Some innerDstIdent,
      init = Some (CIExpr {expr = CEUnOp {
        op = COAddrOf (),
        arg = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = dstIdent},
          rhs = offsetExpr}}})} in
    let innerStmts = _allocateSequenceCDataH elemTy innerSrcIdent innerDstIdent dimIdents in
    let loopBodyStmts = concat [innerSrcInitStmt, innerCopyStmt] innerStmts in
    _generateForLoop iterIdent dimIdent loopBodyStmts
  | [dimIdent] ->
    let iterIdent = nameSym "i" in
    -- NOTE(larshum, 2022-03-09): We need to treat sequences of doubles
    -- specially, because an OCaml array of floats must be accessed via
    -- 'Double_field' rather than 'Field' as for other arrays.
    let fieldAccessExpr =
      match elemTy with CTyDouble _ then
        CEApp {
          fun = _getIdentExn "Double_field",
          args = [CEVar {id = srcIdent}, CEVar {id = iterIdent}]}
      else
        let fieldExpr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEVar {id = iterIdent}]} in
        CEApp {
          fun = ocamlToCConversionFunctionIdent elemTy,
          args = [fieldExpr]}
    in
    let fieldWriteStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = dstIdent},
        rhs = CEVar {id = iterIdent}},
      rhs = fieldAccessExpr}} in
    _generateForLoop iterIdent dimIdent [fieldWriteStmt]
  | [] -> []

  sem _allocateSequenceCData : Name -> CDataRepr -> [CStmt]
  sem _allocateSequenceCData srcIdent =
  | FutharkSeqRepr t ->
    let cType = CTyPtr {ty = t.elemTy} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = t.sizeIdent},
      rhs = CESizeOfType {ty = t.elemTy}} in
    let allocStmt = CSDef {
      ty = cType, id = Some t.ident,
      init = Some (CIExpr {expr = CECast {
        ty = cType,
        rhs = CEApp {
          fun = _getIdentExn "malloc",
          args = [sizeExpr]}}})} in
    cons
      allocStmt
      (_allocateSequenceCDataH t.elemTy srcIdent t.ident t.dimIdents)

  sem _generateOCamlToCWrapperStmts : Name -> CDataRepr -> [CStmt]
  sem _generateOCamlToCWrapperStmts srcIdent =
  | t & (FutharkSeqRepr {sizeIdent = sizeIdent}) ->
    let initSizeStmt = CSDef {
      ty = CTyInt64 (), id = Some sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    let dimStmts = _computeSequenceDimensions srcIdent 0 t in
    let allocStmts = _allocateSequenceCData srcIdent t in
    join [[initSizeStmt], dimStmts, allocStmts]
  | FutharkRecordRepr t ->
    let generateMarshallingField : [CStmt] -> (CDataRepr, Int) -> [CStmt] =
      lam acc. lam fieldIdx.
        match fieldIdx with (field, idx) in
        let valueType = CTyVar {id = _getIdentExn "value"} in
        let fieldId = nameSym "c_tmp" in
        let fieldValueStmt = CSDef {
          ty = valueType, id = Some fieldId,
          init = Some (CIExpr {expr = CEApp {
            fun = _getIdentExn "Field",
            args = [CEVar {id = srcIdent}, CEInt {i = idx}]}})} in
        let innerStmts = _generateOCamlToCWrapperStmts fieldId field in
        join [acc, [fieldValueStmt], innerStmts]
    in
    let indexedFields = create (length t.fields) (lam i. (get t.fields i, i)) in
    foldl generateMarshallingField [] indexedFields
  | FutharkBaseTypeRepr t ->
    let conversionFunctionId : Name = ocamlToCConversionFunctionIdent t.ty in
    let tmp = nameSym "c_tmp" in
    [ CSDef {ty = t.ty, id = Some tmp, init = None ()}
    , CSDef {
        ty = CTyPtr {ty = t.ty}, id = Some t.ident,
        init = Some (CIExpr {expr = CEUnOp {
          op = COAddrOf (),
          arg = CEVar {id = tmp}}})}
    , CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEUnOp {op = CODeref (), arg = CEVar {id = t.ident}},
        rhs = CEApp {
          fun = conversionFunctionId,
          args = [CEVar {id = srcIdent}]}}} ]

  sem _generateOCamlToCWrapperArg : [CStmt] -> ArgData -> [CStmt]
  sem _generateOCamlToCWrapperArg accStmts =
  | arg ->
    concat accStmts (_generateOCamlToCWrapperStmts arg.mexprIdent arg.cData)

  sem generateOCamlToCWrapper : CWrapperEnv -> [CStmt]
  sem generateOCamlToCWrapper =
  | env ->
    foldl _generateOCamlToCWrapperArg [] env.arguments
end

lang CToFutharkWrapper = FutharkCWrapperBase
  sem _generateCToFutharkWrapperArgH : Name -> ArgData -> CDataRepr -> [CStmt]
  sem _generateCToFutharkWrapperArgH ctxIdent arg =
  | FutharkSeqRepr t ->
    let futharkSeqTypeStr = getSeqFutharkTypeString (FutharkSeqRepr t) in
    let seqTypeIdent = _getIdentOrInitNew (concat "futhark_" futharkSeqTypeStr) in
    let seqNewIdent = _getIdentOrInitNew (concat "futhark_new_" futharkSeqTypeStr) in
    let allocStmt = CSDef {
      ty = CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}},
      id = Some arg.gpuIdent,
      init = Some (CIExpr {expr = CEApp {
        fun = seqNewIdent,
        args =
          concat
            [CEVar {id = ctxIdent}, CEVar {id = t.ident}]
            (map (lam id. CEVar {id = id}) t.dimIdents)}})} in
    let freeCTempStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free",
      args = [CEVar {id = t.ident}]}} in
    [allocStmt, freeCTempStmt]
  | FutharkRecordRepr t ->
    -- TODO(larshum, 2022-03-09): Implement support for passing records to
    -- Futhark.
    error "Record parameters have not been implemented for Futhark"
  | FutharkBaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some arg.gpuIdent,
      init = Some (CIExpr {expr = CEVar {id = t.ident}})}]

  sem _generateCToFutharkWrapperArg : Name -> [CStmt] -> ArgData -> [CStmt]
  sem _generateCToFutharkWrapperArg ctxIdent accStmts =
  | arg ->
    let stmts = _generateCToFutharkWrapperArgH ctxIdent arg arg.cData in
    concat accStmts stmts

  sem generateCToFutharkWrapper : CWrapperEnv -> [CStmt]
  sem generateCToFutharkWrapper =
  | env ->
    match env.targetEnv with FutharkTargetEnv fenv in
    let ctxIdent = fenv.futharkContextIdent in
    let initContextCall = CSExpr {expr = CEApp {
      fun = fenv.initContextIdent, args = []}} in
    cons
      initContextCall
      (foldl (_generateCToFutharkWrapperArg ctxIdent) [] env.arguments)
end

lang FutharkCallWrapper = FutharkCWrapperBase
  sem generateFutharkCall : CWrapperEnv -> [CStmt]
  sem generateFutharkCall =
  | env ->
    match env.targetEnv with FutharkTargetEnv fenv in
    let return : ArgData = env.return in
    let returnType = return.mexprType in

    -- Declare Futhark return value
    let futResultDeclStmt = CSDef {
      ty = getFutharkCType return.cData,
      id = Some return.gpuIdent, init = None ()} in
    -- TODO(larshum, 2021-09-03): This only works under the assumption that the
    -- function name (i.e. the string) is unique.
    let functionStr =
      match futPprintEnvGetStr pprintEnvEmpty env.functionIdent with (_, ident) in
      ident
    in
    let funcId = nameSym (concat "futhark_entry_" functionStr) in
    let returnCodeIdent = nameSym "v" in
    let returnCodeDeclStmt = CSDef {
      ty = CTyInt64 (), id = Some returnCodeIdent, init = None ()
    } in

    -- Call Futhark entry point and synchronize context afterwards
    let args =
      map
        (lam arg : ArgData.
          match arg.cData with FutharkBaseTypeRepr _ then
            CEUnOp {op = CODeref (), arg = CEVar {id = arg.gpuIdent}}
          else CEVar {id = arg.gpuIdent})
        env.arguments in
    let functionCallStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = funcId,
        args =
          concat
            [ CEVar {id = fenv.futharkContextIdent}
            , CEUnOp {op = COAddrOf (), arg = CEVar {id = return.gpuIdent}} ]
            args}}} in
    let contextSyncStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = _getIdentExn "futhark_context_sync",
        args = [CEVar {id = fenv.futharkContextIdent}]}}} in

    -- Handle Futhark errors by printing the error message and exiting
    let errorHandlingStmt = CSIf {
      cond = CEBinOp {
        op = CONeq (),
        lhs = CEVar {id = returnCodeIdent},
        rhs = CEInt {i = 0}},
      thn = [
        CSExpr {expr = CEApp {
          fun = _getIdentExn "printf",
          args = [
            CEString {s = "Runtime error in generated code: %s\n"},
            CEApp {
              fun = _getIdentExn "futhark_context_get_error",
              args = [CEVar {id = fenv.futharkContextIdent}]}]}},
        CSExpr {expr = CEApp {
          fun = _getIdentExn "exit",
          args = [CEVar {id = returnCodeIdent}]}}],
      els = []} in

    -- Deallocate the Futhark input values
    let deallocStmts =
      join
        (map
          (lam arg : ArgData.
            match arg.cData with FutharkSeqRepr t then
              let futTypeStr = getSeqFutharkTypeString (FutharkSeqRepr t) in
              let futFreeStr = concat "futhark_free_" futTypeStr in
              let deallocIdent = _getIdentOrInitNew futFreeStr in
              [CSExpr {expr = CEApp {
                fun = deallocIdent,
                args = [
                  CEVar {id = fenv.futharkContextIdent},
                  CEVar {id = arg.gpuIdent}]}}]
            else [])
          env.arguments)
    in

    concat
      [futResultDeclStmt, returnCodeDeclStmt, functionCallStmt,
       errorHandlingStmt, contextSyncStmt, errorHandlingStmt]
      deallocStmts
end

lang FutharkToCWrapper = FutharkCWrapperBase
  sem _generateFutharkToCWrapperH : Name -> Name -> CDataRepr -> [CStmt]
  sem _generateFutharkToCWrapperH ctxIdent srcIdent =
  | FutharkSeqRepr t ->
    -- Find dimensions of result value through the use of 'futhark_shape_*'
    let futReturnTypeString = getSeqFutharkTypeString (FutharkSeqRepr t) in
    let futharkShapeString = concat "futhark_shape_" futReturnTypeString in
    let futharkShapeIdent = _getIdentOrInitNew futharkShapeString in
    -- NOTE(larshum, 2022-03-09): We use casting to remove the const of the
    -- type because the C AST cannot express constant types.
    let dimIdent = nameSym "dim" in
    let dimsStmt = CSDef {
      ty = CTyPtr {ty = CTyInt64 ()},
      id = Some dimIdent,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = CTyInt64 ()},
        rhs = CEApp {
          fun = futharkShapeIdent,
          args = [
            CEVar {id = ctxIdent},
            CEVar {id = srcIdent}]}}})} in
    let dimInitStmts =
      mapi
        (lam i. lam ident.
          CSDef {
            ty = CTyInt64 (), id = Some ident,
            init = Some (CIExpr {expr = CEBinOp {
              op = COSubScript (),
              lhs = CEVar {id = dimIdent},
              rhs = CEInt {i = i}}})})
        t.dimIdents in
    let dimProdExpr =
      foldl
        (lam expr. lam id.
          CEBinOp {op = COMul (), lhs = expr, rhs = CEVar {id = id}})
        (CEVar {id = head t.dimIdents})
        (tail t.dimIdents) in
    let sizeInitStmt = CSDef {
      ty = CTyInt64 (), id = Some t.sizeIdent,
      init = Some (CIExpr {expr = dimProdExpr})} in

    -- Allocate C memory to contain results.
    let cType = CTyPtr {ty = t.elemTy} in
    let cAllocStmt = CSDef {
      ty = cType, id = Some t.ident,
      init = Some (CIExpr {expr = CECast {
        ty = cType,
        rhs = CEApp {
          fun = _getIdentExn "malloc",
          args = [CEBinOp {
            op = COMul (),
            lhs = CEVar {id = t.sizeIdent},
            rhs = CESizeOfType {ty = cType}}]}}})} in

    -- Copy from Futhark to C using the 'futhark_values_*' function.
    let futValuesString = concat "futhark_values_" futReturnTypeString in
    let futValuesIdent = _getIdentOrInitNew futValuesString in
    let copyFutharkToCStmt = CSExpr {expr = CEApp {
      fun = futValuesIdent,
      args = [
        CEVar {id = ctxIdent},
        CEVar {id = srcIdent},
        CEVar {id = t.ident}]}} in

    -- Free Futhark memory
    let futFreeString = concat "futhark_free_" futReturnTypeString in
    let futFreeIdent = _getIdentOrInitNew futFreeString in
    let freeFutharkStmt = CSExpr {expr = CEApp {
      fun = futFreeIdent,
      args = [CEVar {id = ctxIdent}, CEVar {id = srcIdent}]}} in

    join [
      [dimsStmt], dimInitStmts,
      [sizeInitStmt, cAllocStmt, copyFutharkToCStmt, freeFutharkStmt]]
  | FutharkRecordRepr t ->
    -- TODO(larshum, 2022-03-09): Implement support for returning records from
    -- Futhark.
    error "Record return values have not been implemented for Futhark"
  | FutharkBaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some t.ident,
      init = Some (CIExpr {expr = CEUnOp {
        op = COAddrOf (),
        arg = CEVar {id = srcIdent}}})}]

  sem generateFutharkToCWrapper : CWrapperEnv -> [CStmt]
  sem generateFutharkToCWrapper =
  | env ->
    match env.return with {gpuIdent = gpuIdent, cData = cData} in
    match env.targetEnv with FutharkTargetEnv fenv in
    let futCtx = fenv.futharkContextIdent in
    _generateFutharkToCWrapperH futCtx gpuIdent cData
end

lang FutharkCToOCamlWrapper = FutharkCWrapperBase
  sem _generateAllocOCamlLoop : Name -> Name -> Name -> CExpr -> [CStmt]
                             -> [CStmt]
  sem _generateAllocOCamlLoop iterIdent dstIdent dimIdent tag =
  | bodyStmts ->
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let dstAllocStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = _getIdentExn "caml_alloc",
        args = [CEVar {id = dimIdent}, tag]}}} in
    let iterIncrStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = iterIdent},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = iterIdent},
        rhs = CEInt {i = 1}}}} in
    let whileBody = snoc bodyStmts iterIncrStmt in
    let whileStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = iterIdent},
        rhs = CEVar {id = dimIdent}},
      body = whileBody} in
    [iterInitStmt, dstAllocStmt, whileStmt]

  sem _allocateSequenceOCamlDataH : CType -> Name -> Name -> Name -> [Name]
                                 -> [CStmt]
  sem _allocateSequenceOCamlDataH elemTy countIdent srcIdent dstIdent =
  | [dimIdent] ++ dimIdents ->
    let iterIdent = nameSym "i" in
    let innerDstIdent = nameSym "x" in
    let innerDstInitStmt = CSDef {
      ty = CTyVar {id = _getIdentExn "value"}, id = Some innerDstIdent,
      init = None ()} in
    let stmts = _allocateSequenceOCamlDataH elemTy countIdent srcIdent
                                            innerDstIdent dimIdents in
    let storeFieldStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "Store_field",
      args = [
        CEVar {id = dstIdent},
        CEVar {id = iterIdent},
        CEVar {id = innerDstIdent}]}} in
    let tagExpr = CEInt {i = 0} in
    let loopStmts = join [[innerDstInitStmt], stmts, [storeFieldStmt]] in
    _generateAllocOCamlLoop iterIdent dstIdent dimIdent tagExpr loopStmts
  | [dimIdent] ->
    let iterIdent = nameSym "i" in
    let valueExpr = CEBinOp {
      op = COSubScript (),
      lhs = CEVar {id = srcIdent},
      rhs = CEVar {id = countIdent}} in
    let fieldStoreExpr =
      match elemTy with CTyDouble _ then
        CEApp {
          fun = _getIdentExn "Store_double_field",
          args = [
            CEVar {id = dstIdent},
            CEVar {id = iterIdent},
            valueExpr]}
      else
        let cExprToValueExpr = CEApp {
          fun = cToOCamlConversionFunctionIdent elemTy,
          args = [valueExpr]} in
        CEApp {
          fun = _getIdentExn "Store_field",
          args = [
            CEVar {id = dstIdent},
            CEVar {id = iterIdent},
            cExprToValueExpr]}
    in
    let fieldStoreStmt = CSExpr {expr = fieldStoreExpr} in
    let countIncrementStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = countIdent},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = countIdent},
        rhs = CEInt {i = 1}}}} in
    let tagExpr =
      match elemTy with CTyDouble _ then
        CEVar {id = _getIdentExn "Double_array_tag"}
      else CEInt {i = 0} in
    let loopStmts = [fieldStoreStmt, countIncrementStmt] in
    _generateAllocOCamlLoop iterIdent dstIdent dimIdent tagExpr loopStmts
  | [] -> []

  sem _allocateSequenceOCamlData : Name -> Name -> CDataRepr -> [CStmt]
  sem _allocateSequenceOCamlData srcIdent dstIdent =
  | FutharkSeqRepr t ->
    let countIdent = nameSym "count" in
    let countDeclStmt = CSDef {
      ty = CTyInt64 (), id = Some countIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let freeStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free",
      args = [CEVar {id = srcIdent}]}} in
    let allocStmts = _allocateSequenceOCamlDataH t.elemTy countIdent srcIdent
                                                 dstIdent t.dimIdents in
    join [[countDeclStmt], allocStmts, [freeStmt]]

  sem _generateCToOCamlWrapperStmts : Name -> CDataRepr -> [CStmt]
  sem _generateCToOCamlWrapperStmts dstIdent =
  | t & (FutharkSeqRepr {ident = ident}) ->
    _allocateSequenceOCamlData ident dstIdent t
  | FutharkRecordRepr t ->
    if null t.fields then []
    else
      let wrapField : Int -> CDataRepr -> [CStmt] = lam idx. lam field.
        let tempDstIdent = nameSym "c_tmp" in
        let fieldStmts = _generateCToOCamlWrapperStmts tempDstIdent field in
        let storeStmt = CSExpr {expr = CEApp {
          fun = _getIdentExn "Store_field",
          args = [
            CEVar {id = dstIdent},
            CEInt {i = idx},
            CEVar {id = tempDstIdent}]}} in
        snoc fieldStmts storeStmt
      in
      let recordAllocStmt = CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = dstIdent},
        rhs = CEApp {
          fun = _getIdentExn "caml_alloc",
          args = [CEInt {i = length t.fields}, CEInt {i = 0}]}}} in
      let fieldStmts = join (mapi wrapField t.fields) in
      cons recordAllocStmt fieldStmts
  | FutharkBaseTypeRepr t ->
    let toOCamlStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = cToOCamlConversionFunctionIdent t.ty,
        args = [CEUnOp {op = CODeref (), arg = CEVar {id = t.ident}}]}}} in
    [toOCamlStmt]

  sem generateCToOCamlWrapper : CWrapperEnv -> [CStmt]
  sem generateCToOCamlWrapper =
  | env ->
    match env.return with {mexprIdent = mexprIdent, cData = cData} in
    _generateCToOCamlWrapperStmts mexprIdent cData
end

lang FutharkCWrapper =
  FutharkOCamlToCWrapper + CToFutharkWrapper + FutharkCallWrapper +
  FutharkToCWrapper + FutharkCToOCamlWrapper + CProgAst

  -- Generates global Futhark context config and context variables along with a
  -- function to initialize them if they have not already been initialized.
  -- This allows us to reuse the same context instead of constructing a new one
  -- for each call, which significantly reduces the overhead of accelerate
  -- calls.
  --
  -- NOTE(larshum, 2021-10-19): As we do not know when the last accelerate call
  -- happens, the context config and context are not freed. This should not be
  -- a problem because all values should be deallocated after each Futhark
  -- call.
  sem futharkContextInit : CWrapperEnv -> [CTop]
  sem futharkContextInit =
  | env ->
    match env.targetEnv with FutharkTargetEnv fenv in
    let ctxConfigStructId = _getIdentExn "futhark_context_config" in
    let ctxStructId = _getIdentExn "futhark_context" in
    let ctxConfigIdent = fenv.futharkContextConfigIdent in
    let ctxIdent = fenv.futharkContextIdent in
    let initBody = [
      CSIf {
        cond = CEBinOp {
          op = COEq (),
          lhs = CEVar {id = ctxConfigIdent},
          rhs = CEVar {id = _getIdentExn "NULL"}
        },
        thn = [
          CSExpr { expr = CEBinOp {
            op = COAssign (),
            lhs = CEVar {id = ctxConfigIdent},
            rhs = CEApp {
              fun = _getIdentExn "futhark_context_config_new", args = []}}},
          CSExpr { expr = CEBinOp {
            op = COAssign (),
            lhs = CEVar {id = ctxIdent},
            rhs = CEApp {
              fun = _getIdentExn "futhark_context_new",
              args = [CEVar {id = ctxConfigIdent}]}}}],
        els = []}] in
    [ CTDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxConfigStructId,
                                     mem = None ()}},
        id = Some ctxConfigIdent,
        init = None ()},
      CTDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxStructId, mem = None ()}},
        id = Some ctxIdent,
        init = None ()},
      CTFun {
        ret = CTyVoid (),
        id = fenv.initContextIdent,
        params = [],
        body = initBody} ]

  sem generateInitWrapperEnv =
  | _ ->
    let targetEnv = FutharkTargetEnv {
      initContextIdent = nameSym "initContext",
      futharkContextConfigIdent = nameSym "config",
      futharkContextIdent = nameSym "ctx"} in
    let env : CWrapperEnv = _emptyWrapperEnv () in
    {env with targetEnv = targetEnv}

  sem generateMarshallingCode =
  | env ->
    let stmt1 = generateOCamlToCWrapper env in
    let stmt2 = generateCToFutharkWrapper env in
    let stmt3 = generateFutharkCall env in
    let stmt4 = generateFutharkToCWrapper env in
    let stmt5 = generateCToOCamlWrapper env in
    join [stmt1, stmt2, stmt3, stmt4, stmt5]

  sem generateWrapperCode : Map Name AccelerateData -> CProg
  sem generateWrapperCode =
  | accelerated ->
    let env = generateInitWrapperEnv () in
    match generateWrapperCodeH env accelerated with (env, entryPointWrappers) in
    let contextInit = futharkContextInit env in
    -- NOTE(larshum, 2021-08-27): According to
    -- https://ocaml.org/manual/intfc.html CAML_NAME_SPACE should be defined
    -- before including caml headers, but the current C AST does not support
    -- this. It seems to be working without it, though.
    CPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"mexpr-futhark.h\"",
        "\"caml/alloc.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops = join [contextInit, entryPointWrappers]}
end

lang Test = FutharkCWrapper + CProgPrettyPrint + CPrettyPrint
end

mexpr

use Test in

let functionIdent = nameSym "f" in
let dataEntry : AccelerateData = {
  identifier = functionIdent,
  bytecodeWrapperId = nameSym "fbyte",
  params = [(nameSym "s", tyseq_ tyint_)],
  paramCopyStatus = [CopyBoth ()],
  returnType = tyseq_ tyint_,
  info = NoInfo ()
} in
let accelerated = mapFromSeq nameCmp [(functionIdent, dataEntry)] in

let wrapperCode = generateWrapperCode accelerated in
-- print (printCProg [] wrapperCode);
()
