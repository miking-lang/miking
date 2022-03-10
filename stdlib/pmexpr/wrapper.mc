include "c/ast.mc"
include "pmexpr/ast.mc"

let _bigarrayNumDimsKey = nameNoSym "num_dims"
let _bigarrayDimKey = nameNoSym "dim"

-- TODO(larshum, 2022-01-19): Figure out a way to make this set of names
-- extensible for the individual wrappers, instead of having to include all of
-- them here.
let cWrapperNamesRef = ref (None ())
let _genCWrapperNames = lam.
  let identifiers =
    ["malloc", "free", "printf", "exit", "value", "size_t",
    "Long_val", "Int_val", "Double_val", "Val_long", "Val_int",
    "caml_copy_double", "Wosize_val", "caml_alloc", "Field", "Store_field",
    "Double_field", "Store_double_field", "Double_array_tag", "CAMLlocal1",
    "CAMLreturn", "CAMLreturn0", "futhark_context_config",
    "futhark_context_config_new", "futhark_context", "futhark_context_new",
    "futhark_context_config_free", "futhark_context_free",
    "futhark_context_sync", "futhark_context_get_error", "NULL", "cudaMalloc",
    "cudaFree", "cudaMemcpy", "cudaDeviceSynchronize",
    "cudaMemcpyHostToDevice", "cudaMemcpyDeviceToHost", "Caml_ba_array_val",
    "Caml_ba_data_val", "caml_ba_alloc", "CAML_BA_CAML_INT", "CAML_BA_FLOAT64",
    "CAML_BA_C_LAYOUT"]
  in
  mapFromSeq
    cmpString
    (map (lam s. (s, nameNoSym s)) identifiers)
let getCWrapperNames = lam.
  match deref cWrapperNamesRef with Some names then names
  else
    let names = _genCWrapperNames () in
    modref cWrapperNamesRef (Some names);
    names
let updateCWrapperNames = lam newValue.
  modref cWrapperNamesRef (Some newValue)

-- Maps a string to a (hardcoded) unique name of the C function.
let _getIdentExn : String -> Name = lam str.
  match mapLookup str (getCWrapperNames ()) with Some id then id
  else error (concat "Undefined string " str)

let _getIdentOrInitNew : String -> Name = lam str.
  let strIdentMap = getCWrapperNames () in
  optionGetOrElse
    (lam.
      let id = nameSym str in
      updateCWrapperNames (mapInsert str id strIdentMap);
      id)
    (mapLookup str strIdentMap)


lang PMExprCWrapperBase = MExprAst + CAst
  -- Definition of the intermediate representation shapes in C. Note that
  -- nested sequences are treated as one 'SeqRepr', and that sequences and
  -- tensor cannot contain records in the current version.
  syn CDataRepr =
  | SeqRepr {dataIdent : Name, dimIdents : [Name], sizeIdent : Name, elemTy : CType}
  | TensorRepr {dataIdent : Name, rankIdent : Name, sizeIdent : Name,
                dimsIdent : Name, elemTy : CType}
  | RecordRepr {fields : [CDataRepr]}
  | BaseTypeRepr {ident : Name, ty : CType}

  type ArgData = {
    -- The identifier and type of the OCaml value representing the MExpr
    -- argument.
    mexprIdent : Name,
    mexprType : Type,

    -- The intermediate representation of the argument in C.
    cData : CDataRepr,

    -- The identifier of the argument in the GPU backend. We do not store an
    -- explicit type of the argument as the type is backend-specific.
    gpuIdent : Name
  }

  sem defaultArgData =
  | () ->
    { mexprIdent = nameNoSym "", mexprType = tyunknown_
    , cData = RecordRepr {fields = mapEmpty cmpSID}, gpuIdent = nameNoSym "" }

  syn TargetWrapperEnv =
  | EmptyTargetEnv ()

  type CWrapperEnv = {
    -- Identifiers and type of the arguments of the function. These are needed
    -- to keep track of identifiers (in OCaml, C and the GPU target) across
    -- multiple translation steps.
    arguments : [ArgData],

    -- Identifiers and type of the return value. Needed for the same reason as
    -- above.
    return : ArgData,

    -- The name of the GPU function that is being called.
    functionIdent : Name,

    -- Environment containing target-specific variables.
    targetEnv : TargetWrapperEnv}

  sem _emptyWrapperEnv =
  | () ->
    { arguments = [], return = defaultArgData (), functionIdent = nameNoSym ""
    , targetEnv = EmptyTargetEnv () }

  sem _wosize = 
  | id -> CEApp {fun = _getIdentExn "Wosize_val", args = [CEVar {id = id}]}

  sem isBaseType =
  | TyInt _ | TyFloat _ | TyBool _ | TyChar _ -> true
  | _ -> false

  sem mexprToCType =
  | TyInt _ -> CTyInt64 ()
  | TyFloat _ -> CTyDouble ()
  | TyBool _ -> CTyChar ()
  | TyChar _ -> CTyChar ()
  | ty ->
    let tystr = use MExprPrettyPrint in type2str ty in
    error (join ["Type ", tystr, " is not supported by C wrapper"])

  sem _generateCDataRepresentation =
  | TySeq ty ->
    recursive let findSequenceDimensions = lam n. lam ty.
      match ty with TySeq t then
        findSequenceDimensions (addi n 1) t.ty
      else (n, ty)
    in
    match findSequenceDimensions 0 (TySeq ty) with (dims, elemType) in
    if isBaseType elemType then
      let dimIdents = create dims (lam. nameSym "d") in
      SeqRepr {
        dataIdent = nameSym "c_tmp", dimIdents = dimIdents,
        sizeIdent = nameSym "n", elemTy = mexprToCType elemType}
    else
      let tystr = use MExprPrettyPrint in type2str ty in
      error (join ["Sequences of ", tystr, " are not supported by C wrapper"])
  | TyTensor {ty = elemType & (TyInt _ | TyFloat _)} ->
    TensorRepr {
      dataIdent = nameSym "c_tmp", rankIdent = nameSym "rank",
      sizeIdent = nameSym "n", dimsIdent = nameSym "dims",
      elemTy = mexprToCType elemType}
  | TyRecord t ->
    let fields : [CDataRepr] =
      map
        (lam label : SID.
          match mapLookup label t.fields with Some ty then
            _generateCDataRepresentation ty
          else error "Inconsistent labels in record type")
        t.labels in
    RecordRepr {fields = fields}
  | ty -> BaseTypeRepr {ident = nameSym "c_tmp", ty = mexprToCType ty}
end

lang PMExprOCamlToCWrapper = PMExprCWrapperBase
  sem ocamlToCConversionFunctionIdent =
  | CTyChar _ -> _getIdentExn "Int_val"
  | CTyInt64 _ -> _getIdentExn "Long_val"
  | CTyDouble _ -> _getIdentExn "Double_val"

  sem _computeSequenceDimensions (srcIdent : Name) (idx : Int) =
  | t & (SeqRepr {dimIdents = dimIdents, sizeIdent = sizeIdent}) ->
    let dimIdent = get dimIdents idx in
    let initDimStmt = CSDef {
      ty = CTyInt64 (), id = Some dimIdent,
      init = Some (CIExpr {expr = _wosize srcIdent})} in
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

  sem _generateForLoop (iterIdent : Name) (dimIdent : Name) =
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

  sem _allocateSequenceCDataH (elemTy : CType) (srcIdent : Name) (dstIdent : Name) =
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
      rhs = _wosize innerSrcIdent} in
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

  sem _allocateSequenceCData (srcIdent : Name) =
  | SeqRepr t ->
    let cType = CTyPtr {ty = t.elemTy} in
    let sizeExpr = CEBinOp {
      op = COMul (),
      lhs = CEVar {id = t.sizeIdent},
      rhs = CESizeOfType {ty = t.elemTy}} in
    let allocStmt = CSDef {
      ty = cType, id = Some t.dataIdent,
      init = Some (CIExpr {expr = CECast {
        ty = cType,
        rhs = CEApp {
          fun = _getIdentExn "malloc",
          args = [sizeExpr]}}})} in
    cons
      allocStmt
      (_allocateSequenceCDataH t.elemTy srcIdent t.dataIdent t.dimIdents)

  sem _computeTensorDimensions (srcIdent : Name) =
  | TensorRepr t ->
    let bigarrayValId = _getIdentExn "Caml_ba_array_val" in
    let dimExpr = lam idx.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {
          lhs = CEApp {
            fun = bigarrayValId,
            args = [CEVar {id = srcIdent}]},
          id = _bigarrayDimKey},
        rhs = idx} in
    let sizeInitStmt = CSDef {
      ty = CTyInt64 (), id = Some t.sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    let rankInitStmt = CSDef {
      ty = CTyInt64 (), id = Some t.rankIdent,
      init = Some (CIExpr {expr = CEArrow {
        lhs = CEApp {
          fun = bigarrayValId,
          args = [CEVar {id = srcIdent}]},
        id = _bigarrayNumDimsKey}})} in
    let dimsInitStmt = CSDef {
      ty = CTyArray {ty = CTyInt64 (), size = Some (CEVar {id = t.rankIdent})},
      id = Some t.dimsIdent, init = None ()} in
    let i = nameSym "i" in
    let iterInitStmt = CSDef {
      ty = CTyInt64 (), id = Some i,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    let mulSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = t.sizeIdent},
      rhs = CEBinOp {
        op = COMul (),
        lhs = CEVar {id = t.sizeIdent},
        rhs = dimExpr (CEVar {id = i})}}} in
    let setDimsStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = t.dimsIdent},
        rhs = CEVar {id = i}},
      rhs = dimExpr (CEVar {id = i})}} in
    let incrementIterStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = i},
      rhs = CEBinOp {op = COAdd (), lhs = CEVar {id = i}, rhs = CEInt {i = 1}}}} in
    let loopStmt = CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = i},
        rhs = CEVar {id = t.rankIdent}},
      body = [mulSizeStmt, setDimsStmt, incrementIterStmt]} in
    [sizeInitStmt, rankInitStmt, dimsInitStmt, iterInitStmt, loopStmt]

  sem _generateOCamlToCWrapperStmts (srcIdent : Name) =
  | t & (SeqRepr {sizeIdent = sizeIdent}) ->
    let initSizeStmt = CSDef {
      ty = CTyInt64 (), id = Some sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    let dimStmts = _computeSequenceDimensions srcIdent 0 t in
    let allocStmts = _allocateSequenceCData srcIdent t in
    join [[initSizeStmt], dimStmts, allocStmts]
  | TensorRepr t ->
    let dimsStmts = _computeTensorDimensions srcIdent (TensorRepr t) in
    let tensorDataTy = CTyPtr {ty = t.elemTy} in
    let declStmt = CSDef {
      ty = tensorDataTy, id = Some t.dataIdent,
      init = Some (CIExpr {expr = CECast {
        ty = tensorDataTy,
        rhs = CEApp {
          fun = _getIdentExn "Caml_ba_data_val",
          args = [CEVar {id = srcIdent}]}}})} in
    snoc dimsStmts declStmt
  | RecordRepr t ->
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
  | BaseTypeRepr t ->
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

  sem _generateOCamlToCWrapperArg (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    concat accStmts (_generateOCamlToCWrapperStmts arg.mexprIdent arg.cData)

  sem generateOCamlToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    foldl _generateOCamlToCWrapperArg [] env.arguments
end

lang PMExprCToOCamlWrapper = PMExprCWrapperBase
  sem cToOCamlConversionFunctionIdent =
  | CTyChar _ -> _getIdentExn "Val_int"
  | CTyInt64 _ -> _getIdentExn "Val_long"
  | CTyDouble _ -> _getIdentExn "caml_copy_double"

  sem _generateAllocOCamlLoop (iterIdent : Name) (dstIdent : Name)
                              (dimIdent : Name) (tag : CExpr) =
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

  sem _allocateSequenceOCamlDataH (elemTy : CType) (countIdent : Name)
                                  (srcIdent : Name) (dstIdent : Name) =
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

  sem _allocateSequenceOCamlData (srcIdent : Name) (dstIdent : Name) =
  | SeqRepr t ->
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

  sem _generateCToOCamlWrapperStmts (dstIdent : Name) =
  | t & (SeqRepr {dataIdent = dataIdent}) ->
    _allocateSequenceOCamlData dataIdent dstIdent t
  | TensorRepr t ->
    let bigarrayKind =
      match t.elemTy with CTyInt64 _ then
        CEVar {id = _getIdentExn "CAML_BA_CAML_INT"}
      else match t.elemTy with CTyDouble _ then
        CEVar {id = _getIdentExn "CAML_BA_FLOAT64"}
      else never in
    let bigarrayLayoutKind = CEBinOp {
      op = COBOr (),
      lhs = bigarrayKind,
      rhs = CEVar {id = _getIdentExn "CAML_BA_C_LAYOUT"}} in
    let tensorAllocStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = _getIdentExn "caml_ba_alloc",
        args = [
          bigarrayLayoutKind,
          CEVar {id = t.rankIdent},
          CEVar {id = t.dataIdent},
          CEVar {id = t.dimsIdent}]}}} in
    [tensorAllocStmt]
  | RecordRepr t ->
    if null t.fields then []
    else
      let wrapField = lam idx : Int. lam field : CDataRepr.
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
      let fieldStmts = mapi wrapField t.fields in
      cons recordAllocStmt fieldStmts
  | BaseTypeRepr t ->
    let toOCamlStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = cToOCamlConversionFunctionIdent t.ty,
        args = [CEUnOp {op = CODeref (), arg = CEVar {id = t.ident}}]}}} in
    [toOCamlStmt]

  sem generateCToOCamlWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    _generateCToOCamlWrapperStmts return.mexprIdent return.cData
end

-- Defines an extensible C wrapper generation language fragment. This fragment
-- can be extended to implement the target-specific parts of the wrapper, while
-- allowing reuse of the parts that all targets will have in common.
lang PMExprCWrapper =
  PMExprCWrapperBase + PMExprOCamlToCWrapper + PMExprCToOCamlWrapper

  sem _getCReturnType =
  | TyRecord {labels = []} -> CTyVoid ()
  | _ -> CTyVar {id = _getIdentExn "value"}

  -- Generates an additional wrapper function to be referenced from OCaml. This
  -- function is used when calling from bytecode (hence the name) and also when
  -- the function takes more than five parameters.
  sem generateBytecodeWrapper =
  | data ->
    let data : AccelerateData = data in
    let returnType = _getCReturnType data.returnType in
    let bytecodeStr = nameGetStr data.bytecodeWrapperId in
    let bytecodeFunctionName = nameSym bytecodeStr in
    let args = nameSym "args" in
    let argc = nameSym "argc" in
    let nargs = length data.params in
    let functionArgs =
      map
        (lam i. CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = args},
          rhs = CEInt {i = i}})
        (create nargs (lam i. i)) in
    let valueTy = CTyVar {id = _getIdentExn "value"} in
    CTFun {
      ret = returnType,
      id = bytecodeFunctionName,
      params = [(CTyPtr {ty = valueTy}, args), (CTyInt (), argc)],
      body = [CSRet {val = Some (CEApp {
        fun = data.identifier,
        args = functionArgs})}]}

  sem generateCAMLparamDeclarations =
  | args /- : [ArgData] -/ ->
    let genParamStmt : [ArgData] -> String -> CExpr = lam args. lam funStr.
      let nargsStr = int2string (length args) in
      let camlParamIdent = _getIdentOrInitNew (concat funStr nargsStr) in
      CSExpr {expr = CEApp {
        fun = camlParamIdent,
        args = map (lam arg : ArgData. CEVar {id = arg.mexprIdent}) args}} in
    let nargs = length args in
    let fstArgs = subsequence args 0 5 in
    let fstDeclStmt = genParamStmt fstArgs "CAMLparam" in
    if gti nargs 5 then
      recursive let generateExtraParamDecl = lam args.
        let nargs = length args in
        let declStmt = genParamStmt (subsequence args 0 5) "CAMLxparam" in
        if gti nargs 5 then
          cons
            declStmt
            (generateExtraParamDecl (subsequence args 5 (length args)))
        else [declStmt] in
      let remainingArgs = subsequence args 5 (length args) in
      cons fstDeclStmt (generateExtraParamDecl remainingArgs)
    else [fstDeclStmt]

  -- Defines the generation of marshalling code between OCaml and the GPU
  -- backend, including conversion between C and calls to functions defined by
  -- the GPU backend. As this generation depends on the GPU backend, it is left
  -- empty here.
  sem generateMarshallingCode =

  -- Generates the main function of the wrapper code. This is the function that
  -- manages the marshalling between OCaml and the target GPU language.
  sem generateWrapperFunctionCode (env : CWrapperEnv) =
  | data ->
    let data : AccelerateData = data in
    let toArgData = lam arg : (Name, Type).
      let default : ArgData = defaultArgData () in
      {{{{default with mexprIdent = arg.0}
                  with mexprType = arg.1}
                  with cData = _generateCDataRepresentation arg.1}
                  with gpuIdent = nameSym "gpu_tmp"} in
    let bytecodeWrapper = generateBytecodeWrapper data in
    let returnIdent = nameSym "out" in
    let returnArg = (returnIdent, data.returnType) in
    let env = {{{env with arguments = map toArgData data.params}
                     with return = toArgData returnArg}
                     with functionIdent = data.identifier} in
    let camlParamStmts = generateCAMLparamDeclarations env.arguments in
    let stmts = generateMarshallingCode env in
    let value = _getIdentExn "value" in
    let stmts =
      match data.returnType with TyRecord {labels = []} then
        let camlReturnStmt = CSExpr {expr = CEVar {
          id = _getIdentExn "CAMLreturn0"
        }} in
        join [camlParamStmts, stmts, [camlReturnStmt]]
      else
        let camlLocalStmt = CSExpr {expr = CEApp {
          fun = _getIdentExn "CAMLlocal1",
          args = [CEVar {id = returnIdent}]}} in
        let camlReturnStmt = CSExpr {expr = CEApp {
          fun = _getIdentExn "CAMLreturn",
          args = [CEVar {id = returnIdent}]}} in
        join [camlParamStmts, [camlLocalStmt], stmts, [camlReturnStmt]] in
    let withValueType = lam arg : (Name, Info, Type).
      (CTyVar {id = value}, arg.0) in
    [ CTFun {
        ret = _getCReturnType data.returnType,
        id = data.identifier,
        params = map withValueType data.params,
        body = stmts}
    , bytecodeWrapper ]

  sem generateWrapperCodeH (env : CWrapperEnv) =
  | accelerated /- Map Name AccelerateData -/ ->
    let entryPointWrappers =
      map (generateWrapperFunctionCode env) (mapValues accelerated) in
    (env, join entryPointWrappers)
end
