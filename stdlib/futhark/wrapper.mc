include "map.mc"
include "string.mc"
include "c/ast.mc"
include "c/pprint.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"

let cWrapperNamesRef = ref (None ())
let _genCWrapperNames = lam.
  let identifiers =
    ["malloc", "free", "printf", "exit", "value", "size_t", "int64_t",
    "Long_val", "Bool_val", "Double_val", "Val_long", "Val_bool",
    "caml_copy_double", "Wosize_val", "caml_alloc", "Field", "Store_field",
    "Double_field", "Store_double_field", "Double_array_tag", "CAMLlocal1",
    "CAMLreturn", "futhark_context_config", "futhark_context_config_new",
    "futhark_context", "futhark_context_new", "futhark_context_config_free",
    "futhark_context_free", "futhark_context_sync",
    "futhark_context_get_error"]
  in
  mapFromSeq
    cmpString
    (map (lam s. (s, nameSym s)) identifiers)
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

type ArgData = {
  -- The identifier and the MExpr type of the argument.
  ident : Name,
  ty : Type,

  -- The identifiers of the C variable(s) containing values used to represent
  -- this variable. This is a sequence because the fields of records and tuples
  -- are placed in one array each.
  cTempVars : [(Name, CType)],

  -- The identifier of the Futhark variable. Unlike the C temporaries, the
  -- Futhark value is always represented using one variable, as multiple C
  -- arrays are translated into one Futhark array using helper functions.
  futIdent : Name,

  -- Identifiers of variables containing the dimensions of the array, starting
  -- with the outermost dimension. This sequence is empty if the type of the
  -- argument is not a sequence.
  dimIdents : [Name],

  -- The identifier of a variable containing the full size of the array.
  sizeIdent : Name
}

let defaultArgData = use MExprAst in {
  ident = nameNoSym "", ty = TyUnknown {info = NoInfo ()}, cTempVars = [],
  futIdent = nameNoSym "", dimIdents = [], sizeIdent = nameNoSym ""
}

type CWrapperEnv = {
  -- Identifiers and type of the arguments of the function. These are needed
  -- to keep track of identifiers (in OCaml, C and Futhark) across multiple
  -- translation steps.
  arguments : [ArgData],

  -- Identifiers and type of the return value. Needed for the same reason as
  -- above.
  return : ArgData,

  -- The name of the Futhark function that is being called.
  functionIdent : Name,

  -- The Futhark context config and context variable identifiers.
  futharkContextConfigIdent : Name,
  futharkContextIdent : Name
}

let emptyWrapperEnv = {
  arguments = [], return = [], keywordIdentMap = mapEmpty cmpString,
  functionIdent = nameNoSym "", futharkContextConfigIdent = nameNoSym "",
  futharkContextIdent = nameNoSym ""
}

let getMExprSeqFutharkTypeString : Type -> String = use MExprAst in
  lam ty.
  recursive let work = lam dim. lam ty.
    match ty with TySeq {ty = innerTy} then
      work (addi dim 1) innerTy
    else match ty with TyInt _ | TyChar _ then
      (dim, "i64")
    else match ty with TyFloat _ then
      (dim, "f64")
    else never
  in
  match work 0 ty with (dim, elemTyStr) then
    if eqi dim 0 then
      elemTyStr
    else
      join [elemTyStr, "_", int2string dim, "d"]
  else never

let getFutharkSeqTypeString : String -> Int -> String =
  lam futharkElementTypeString. lam numDims.
  join [futharkElementTypeString, "_", int2string numDims, "d"]

recursive let getDimensionsOfType : Type -> Int = use MExprAst in
  lam ty.
  match ty with TySeq {ty = innerTy} then
    addi 1 (getDimensionsOfType innerTy)
  else 0
end

lang CWrapperBase = MExprAst + CAst
  sem _wosize =
  | id ->
      CEApp {fun = _getIdentExn "Wosize_val", args = [CEVar {id = id}]}

  sem getFutharkCType =
  | TyInt _ | TyChar _ -> CTyVar {id = _getIdentExn "int64_t"}
  | TyFloat _ -> CTyDouble ()
  | ty & (TySeq _) ->
    let seqTypeStr = getMExprSeqFutharkTypeString ty in
    let seqTypeIdent = _getIdentOrInitNew (concat "futhark_" seqTypeStr) in
    CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}}


  sem getFutharkElementTypeString =
  | ty & (CTyVar {id = id}) ->
    if nameEq id (_getIdentExn "int64_t") then
      "i64"
    else error "Unsupported C type"
  | CTyDouble _ -> "f64"
  | CTyPtr t -> getFutharkElementTypeString t.ty

  -- Converts a given MExpr type to a sequence containing the C type or types
  -- used to represent it in the C wrapper. Records and tuples are represented
  -- by multiple types, one for each field.
  sem mexprToCTypes =
  | TyInt _ | TyChar _ -> [CTyVar {id = _getIdentExn "int64_t"}]
  | TyFloat _ -> [CTyDouble {}]
  | TySeq {ty = elemTy & !(TySeq _)} ->
    map (lam ty. CTyPtr {ty = ty}) (mexprToCTypes elemTy)
  | TySeq t -> mexprToCTypes t.ty
  | TyRecord _ -> error "Records cannot be translated to C yet"
end

lang OCamlToCWrapper = CWrapperBase
  sem _generateOCamlToCSequenceWrapper (srcIdent : Name) (dimIdent : Name)
                                       (iterIdent : Name) =
  | whileBody /- : [CStmt] -/ ->
    let iterDefStmt = CSDef {
      ty = CTyInt (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})} in
    [ iterDefStmt
    , CSWhile {
        cond = CEBinOp {
          op = COLt (), lhs = CEVar {id = iterIdent},
          rhs = CEVar {id = dimIdent}},
        body = whileBody} ]

  sem _generateOCamlToCWrapperInner (srcIdent : Name) (cvars : [(Name, CType)])
                                    (dimIdents : [Name]) =
  | TyInt _ | TyChar _ ->
    let cvar : (Name, Type) = head cvars in
    let cIdent = cvar.0 in
    [CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEUnOp {op = CODeref (), arg = CEVar {id = cIdent}},
      rhs = CEApp {fun = _getIdentExn "Long_val",
                   args = [CEVar {id = srcIdent}]}}}]
  | TyFloat _ ->
    let cvar : (Name, Type) = head cvars in
    let cIdent = cvar.0 in
    [CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEUnOp {op = CODeref (), arg = CEVar {id = cIdent}},
      rhs = CEApp {fun = _getIdentExn "Double_val",
                   args = [CEVar {id = srcIdent}]}}}]
  | TySeq {ty = TyFloat _} ->
    let cvar : (Name, CType) = head cvars in
    let cIdent = cvar.0 in
    let dimIdent = head dimIdents in
    let iterIdent = nameSym "i" in
    let whileBody = [
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = cIdent}, rhs = CEVar {id = iterIdent}},
        rhs = CEApp {fun = _getIdentExn "Double_field",
                     args = [CEVar {id = srcIdent}, CEVar {id = iterIdent}]}}},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = iterIdent},
        rhs = CEBinOp {
          op = COAdd (),
          lhs = CEVar {id = iterIdent},
          rhs = CEInt {i = 1}}}}
    ] in
    _generateOCamlToCSequenceWrapper srcIdent dimIdent iterIdent whileBody
  | TySeq {ty = innerTy} ->
    let iterIdent = nameSym "i" in
    let innerSrcIdent = nameSym "x" in
    let innerCvars = map (lam p : (Name, CType). (nameSym "y", p.1)) cvars in
    let innerCopyStmts =
      map
        (lam entry : ((Name, CType), (Name, CType)).
          let cvar = entry.0 in
          let innerCvar = entry.1 in
          let elemTy = cvar.1 in
          let offset =
            match innerTy with TySeq _ then
              CEBinOp {
                op = COMul (),
                lhs = CEVar {id = iterIdent},
                rhs = _wosize innerSrcIdent}
            else CEVar {id = iterIdent}
          in
          CSDef {
            ty = elemTy, id = Some innerCvar.0,
            init = Some (CIExpr {expr = CEUnOp {
              op = COAddrOf (),
              arg = CEBinOp {
                op = COSubScript (),
                lhs = CEVar {id = cvar.0},
                rhs = offset}}})})
        (zip cvars innerCvars)
    in
    let value = _getIdentExn "value" in
    let field = _getIdentExn "Field" in
    match dimIdents with [dimIdent] ++ remainingDimIdents then
      let whileBody = join [
        [CSDef {
          ty = CTyVar {id = value}, id = Some innerSrcIdent,
          init = Some (CIExpr {expr = CEApp {
            fun = field,
            args = [CEVar {id = srcIdent}, CEVar {id = iterIdent}]}})}],
        innerCopyStmts,
        _generateOCamlToCWrapperInner innerSrcIdent innerCvars
                                      remainingDimIdents innerTy,
        [CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEVar {id = iterIdent},
          rhs = CEBinOp {
            op = COAdd (), lhs = CEVar {id = iterIdent},
            rhs = CEInt {i = 1}}}}]
      ] in
      _generateOCamlToCSequenceWrapper srcIdent dimIdent iterIdent whileBody
    else never

  sem _generateOCamlToCAlloc (arg : ArgData) =
  | ty ->
    let cIdent = nameSym "c_tmp" in
    match ty with CTyPtr {ty = elementType} then
      let allocStmt = CSDef {
        ty = ty, id = Some cIdent,
        init = Some (CIExpr {expr = CECast {
          ty = ty,
          rhs = CEApp {
            fun = _getIdentExn "malloc",
            args = [CEBinOp {
              op = COMul (),
              lhs = CEVar {id = arg.sizeIdent},
              rhs = CESizeOfType {ty = elementType}}]}}})
      } in
      let arg = {arg with cTempVars = snoc arg.cTempVars (cIdent, ty)} in
      (arg, [allocStmt])
    else
      let cPtrIdent = nameSym "c_tmp_ptr" in
      let allocStmts = [
        CSDef {ty = ty, id = Some cIdent, init = None ()},
        CSDef {
          ty = CTyPtr {ty = ty}, id = Some cPtrIdent,
          init = Some (CIExpr {expr = CEUnOp {
            op = COAddrOf (),
            arg = CEVar {id = cIdent}}})}
      ] in
      let arg = {arg with cTempVars = snoc arg.cTempVars (cPtrIdent, ty)} in
      (arg, allocStmts)

  sem _computeDimensionsH (arg : ArgData) (srcIdent : Name) =
  | TySeq {ty = innerTy} ->
    let dimIdent = nameSym "d" in
    let arg = {arg with dimIdents = snoc arg.dimIdents dimIdent} in
    let initDimStmt = CSDef {
      ty = CTyInt (), id = Some dimIdent,
      init = Some (CIExpr {expr = _wosize srcIdent})} in
    let updateSizeStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = arg.sizeIdent},
      rhs = CEBinOp {
        op = COMul (),
        lhs = CEVar {id = arg.sizeIdent},
        rhs = CEVar {id = dimIdent}}}} in
    match innerTy with TySeq _ then
      let innerSrcIdent = nameSym "t" in
      let innerSrcStmt = CSDef {
        ty = CTyVar {id = _getIdentExn "value"},
        id = Some innerSrcIdent,
        -- NOTE(larshum, 2021-09-01): Crashes at runtime if a multi-dimensional
        -- sequence is empty.
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEInt {i = 0}]}})} in
      match _computeDimensionsH arg innerSrcIdent innerTy with (arg, stmts) then
        (arg, concat [initDimStmt, updateSizeStmt, innerSrcStmt] stmts)
      else never
    else (arg, [initDimStmt, updateSizeStmt])
  | ty -> (arg, [])

  sem _computeDimensions =
  | arg ->
    let arg : ArgData = arg in
    let arg = {arg with sizeIdent = nameSym "n"} in
    let initStmt = CSDef {
      ty = CTyInt (), id = Some arg.sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    match _computeDimensionsH arg arg.ident arg.ty with (arg, stmts) then
      (arg, cons initStmt stmts)
    else never

  sem _generateOCamlToCWrapperArg (accStmts : [CStmt]) =
  | arg /- : ArgData -/ ->
    match _computeDimensions arg with (arg, dimStmts) then
      let arg : ArgData = arg in
      let cTypes = mexprToCTypes arg.ty in
      match mapAccumL _generateOCamlToCAlloc arg cTypes with (arg, allocStmts) then
        let arg : ArgData = arg in
        let copyStmts =
          _generateOCamlToCWrapperInner
            arg.ident arg.cTempVars arg.dimIdents arg.ty
        in
        (join [accStmts, dimStmts, join allocStmts, copyStmts], arg)
      else never
    else never

  sem generateOCamlToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match mapAccumL _generateOCamlToCWrapperArg [] env.arguments
    with (stmts, args) then
      ({env with arguments = args}, stmts)
    else never
end

lang CToFutharkWrapper = CWrapperBase
  sem _generateCToFutharkWrapperInner (ctxIdent : Name) (arg : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head arg.cTempVars in
    ({arg with futIdent = cvar.0}, [])
  | TySeq _ ->
    let cvars = arg.cTempVars in
    -- TODO(larshum, 2021-09-01): Add support for records by passing all cvars
    -- to a Futhark helper function which produces records of appropriate type.
    -- For now, we assume there is a one-to-one mapping between the OCaml and
    -- the C identifiers (i.e. non record/tuple types).
    let cvar : (Name, CType) = head cvars in
    let futharkElemTypeStr = getFutharkElementTypeString cvar.1 in
    let numDims = length arg.dimIdents in
    let futharkSeqTypeStr = getFutharkSeqTypeString futharkElemTypeStr numDims in
    let seqTypeIdent = _getIdentOrInitNew (concat "futhark_" futharkSeqTypeStr) in
    let seqNewIdent = _getIdentOrInitNew (concat "futhark_new_" futharkSeqTypeStr) in
    let futIdent = nameSym "fut_tmp" in
    let allocStmt = CSDef {
      ty = CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}},
      id = Some futIdent,
      init = Some (CIExpr {expr = CEApp {
        fun = seqNewIdent,
        args =
          concat
            [CEVar {id = ctxIdent}, CEVar {id = cvar.0}]
            (map (lam id. CEVar {id = id}) arg.dimIdents)}})}
    in
    let freeCTempStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free", args = [CEVar {id = cvar.0}]}}
    in
    let arg = {arg with futIdent = futIdent} in
    (arg, [allocStmt, freeCTempStmt])

  sem _generateCToFutharkWrapperArg (ctxIdent : Name) (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    match _generateCToFutharkWrapperInner ctxIdent arg arg.ty
    with (arg, stmts) then
      (concat accStmts stmts, arg)
    else never

  sem generateCToFutharkWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let ctxConfigIdent = nameSym "cfg" in
    let ctxIdent = nameSym "ctx" in
    let env = {{env with futharkContextConfigIdent = ctxConfigIdent}
                    with futharkContextIdent = ctxIdent} in
    let ctxConfigStructId = _getIdentExn "futhark_context_config" in
    let ctxStructId = _getIdentExn "futhark_context" in
    let configInitStmts = [
      CSDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxConfigStructId,
                                     mem = None ()}},
        id = Some ctxConfigIdent,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "futhark_context_config_new", args = []}})},
      CSDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxStructId, mem = None ()}},
        id = Some ctxIdent,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "futhark_context_new",
          args = [CEVar {id = ctxConfigIdent}]}})}
    ] in
    match mapAccumL (_generateCToFutharkWrapperArg ctxIdent) [] env.arguments
    with (futharkCopyStmts, args) then
      ({env with arguments = args}, join [configInitStmts, futharkCopyStmts])
    else never
end

lang FutharkCallWrapper = CWrapperBase
  sem generateFutharkCall =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    let returnType = return.ty in

    -- Declare Futhark return value
    let futReturnCType = getFutharkCType returnType in
    let futResultIdent = nameSym "fut_ret" in
    let futResultDeclStmt = CSDef {
      ty = futReturnCType,
      id = Some futResultIdent,
      init = None ()
    } in
    -- TODO(larshum, 2021-09-03): This only works under the assumption that the
    -- function name (i.e. the string) is unique.
    let functionStr = escapeFutharkVarString (nameGetStr env.functionIdent) in
    let funcId = nameSym (concat "futhark_entry_" functionStr) in
    let returnCodeIdent = nameSym "v" in
    let returnCodeDeclStmt = CSDef {
      ty = CTyInt (), id = Some returnCodeIdent, init = None ()
    } in

    -- Call Futhark entry point and synchronize context afterwards
    let args =
      map
        (lam arg : ArgData.
          match arg.ty with TySeq _ then
            CEVar {id = arg.futIdent}
          else
            CEUnOp {op = CODeref (), arg = CEVar {id = arg.futIdent}})
        env.arguments
    in
    let functionCallStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = funcId,
        args =
          concat
            [ CEVar {id = env.futharkContextIdent}
            , CEUnOp {op = COAddrOf (), arg = CEVar {id = futResultIdent}} ]
            args}
    }} in
    let contextSyncStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = _getIdentExn "futhark_context_sync",
        args = [CEVar {id = env.futharkContextIdent}]}
    }} in

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
              args = [CEVar {id = env.futharkContextIdent}]}]}},
        CSExpr {expr = CEApp {
          fun = _getIdentExn "exit",
          args = [CEVar {id = returnCodeIdent}]}}],
      els = []
    } in

    -- Deallocate the Futhark input values
    let deallocStmts =
      join
        (map
          (lam arg : ArgData.
            match arg.ty with TySeq _ then
              let futTypeStr = getMExprSeqFutharkTypeString arg.ty in
              let futFreeStr = concat "futhark_free_" futTypeStr in
              let deallocIdent = _getIdentOrInitNew futFreeStr in
              [CSExpr {expr = CEApp {
                fun = deallocIdent,
                args = [
                  CEVar {id = env.futharkContextIdent},
                  CEVar {id = arg.futIdent}]}}]
            else [])
          env.arguments)
    in

    let return = {return with futIdent = futResultIdent} in
    let stmts =
      concat
        [futResultDeclStmt, returnCodeDeclStmt, functionCallStmt,
         errorHandlingStmt, contextSyncStmt, errorHandlingStmt]
        deallocStmts
    in
    ({env with return = return}, stmts)
end

lang FutharkToCWrapper = CWrapperBase
  sem _generateFutharkToCWrapperInner (ctxIdent : Name) (return : ArgData) =
  | ty & (TyInt _ | TyChar _ | TyFloat _) ->
    let ctype = head (mexprToCTypes ty) in
    let cIdent = return.futIdent in
    let return = {return with cTempVars = [(cIdent, ctype)]} in
    (return, [])
  | ty & (TySeq _) ->
    let ctype = head (mexprToCTypes ty) in
    let cIdent = nameSym "c_tmp" in
    
    -- Find dimensions of result value through 'futhark_shape_*'
    let futReturnTypeString = getMExprSeqFutharkTypeString ty in
    let futharkShapeString = join ["futhark_shape_", futReturnTypeString] in
    let futharkShapeIdent = nameSym futharkShapeString in
    let dimIdent = nameSym "dim" in
    -- NOTE(larshum, 2021-09-02): We cast away the const because the current C
    -- AST implementation does not support const types.
    let dimsStmt = CSDef {
      ty = CTyPtr {ty = CTyVar {id = _getIdentExn "int64_t"}},
      id = Some dimIdent,
      init = Some (CIExpr {expr = CECast {
        ty = CTyPtr {ty = CTyVar {id = _getIdentExn "int64_t"}},
        rhs = CEApp {
          fun = futharkShapeIdent,
          args = [
            CEVar {id = ctxIdent},
            CEVar {id = return.futIdent}]}}})
    } in
    let ndims = getDimensionsOfType ty in
    let dimIdents = create ndims (lam. nameSym "d") in
    let dimInitStmts =
      mapi
        (lam i. lam ident.
          CSDef {
            ty = CTyInt (), id = Some ident,
            init = Some (CIExpr {expr = CEBinOp {
              op = COSubScript (),
              lhs = CEVar {id = dimIdent},
              rhs = CEInt {i = i}}})})
        dimIdents
    in
    let dimProdExpr =
      foldl
        (lam expr. lam id.
          CEBinOp {op = COMul (), lhs = expr, rhs = CEVar {id = id}})
        (CEVar {id = head dimIdents})
        (tail dimIdents)
    in
    let sizeIdent = nameSym "n" in
    let sizeInitStmt = CSDef {
      ty = CTyInt (), id = Some sizeIdent,
      init = Some (CIExpr {expr = dimProdExpr})
    } in

    -- Preallocate C memory using the size found in previous step
    let preallocStmt = CSDef {
      ty = ctype,
      id = Some cIdent,
      init = Some (CIExpr {expr = CECast {
        ty = ctype,
        rhs = CEApp {
          fun = _getIdentExn "malloc",
          args = [CEBinOp {
            op = COMul (),
            lhs = CEVar {id = sizeIdent},
            rhs = CESizeOfType {ty = ctype}}]}}})
    } in

    -- Copy from Futhark to C using 'futhark_values_*' function
    let futValuesString = join ["futhark_values_", futReturnTypeString] in
    let futValuesIdent = _getIdentOrInitNew futValuesString in
    let copyFutharkToCStmt = CSExpr {expr = CEApp {
      fun = futValuesIdent,
      args = [
        CEVar {id = ctxIdent},
        CEVar {id = return.futIdent},
        CEVar {id = cIdent}]
    }} in

    -- Free Futhark memory
    let futFreeString = join ["futhark_free_", futReturnTypeString] in
    let futFreeIdent = _getIdentOrInitNew futFreeString in
    let freeFutharkStmt = CSExpr {expr = CEApp {
      fun = futFreeIdent,
      args = [CEVar {id = ctxIdent}, CEVar {id = return.futIdent}]
    }} in

    let return = {{{return with cTempVars = [(cIdent, ctype)]}
                           with dimIdents = dimIdents}
                           with sizeIdent = sizeIdent}
    in
    (return, join [[dimsStmt], dimInitStmts, [sizeInitStmt, preallocStmt,
                   copyFutharkToCStmt, freeFutharkStmt]])

  sem generateFutharkToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let freeContextStmts = [
      CSExpr {expr = CEApp {
        fun = _getIdentExn "futhark_context_free",
        args = [CEVar {id = env.futharkContextIdent}]}},
      CSExpr {expr = CEApp {
        fun = _getIdentExn "futhark_context_config_free",
        args = [CEVar {id = env.futharkContextConfigIdent}]}}
    ] in
    let futCtx = env.futharkContextIdent in
    match _generateFutharkToCWrapperInner futCtx env.return env.return.ty
    with (return, copyStmts) then
      ({env with return = return}, concat copyStmts freeContextStmts)
    else never
end

lang CToOCamlWrapper = CWrapperBase
  sem _generateCToOCamlSequenceWrapper (iterIdent : Name) (dstIdent : Name)
                                       (dimIdent : Name) (tag : CExpr) =
  | whileBody /- : [CStmt] -/ ->
    let incrementIterStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = iterIdent},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = iterIdent},
        rhs = CEInt {i = 1}}
    }} in
    let whileBody = snoc whileBody incrementIterStmt in
    [ CSDef {
        ty = CTyInt (), id = Some iterIdent,
        init = Some (CIExpr {expr = CEInt {i = 0}})}
    , CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEVar {id = dstIdent},
        rhs = CEApp {
          fun = _getIdentExn "caml_alloc",
          args = [CEVar {id = dimIdent}, tag]}}}
    , CSWhile {
        cond = CEBinOp {
          op = COLt (),
          lhs = CEVar {id = iterIdent},
          rhs = CEVar {id = dimIdent}},
        body = whileBody} ]

  sem _incrementCounter =
  | countIdent /- : Name -/ ->
    CSExpr {expr = CEBinOp {
      op = COAssign(),
      lhs = CEVar {id = countIdent},
      rhs = CEBinOp {
        op = COAdd (),
        lhs = CEVar {id = countIdent},
        rhs = CEInt {i = 1}}}}

  sem _generateCToOCamlWrapperInner (countIdent : Name)
                                    (cvars : [(Name, CType)])
                                    (dstIdent : Name)
                                    (dimIdents : [Name]) =
  | TyInt _ | TyChar _ ->
    let cvar : (Name, CType) = head cvars in
    [CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = _getIdentExn "Val_long",
        args = [CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = cvar.0},
          rhs = CEVar {id = countIdent}}]}}},
    _incrementCounter countIdent]
  | TyFloat _ ->
    let cvar : (Name, CType) = head cvars in
    [CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = _getIdentExn "caml_copy_double",
        args = [CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = cvar.0},
          rhs = CEVar {id = countIdent}}]}}},
    _incrementCounter countIdent]
  | TySeq {ty = TyFloat _} ->
    let cvar : (Name, CType) = head cvars in
    let iterIdent = nameSym "i" in
    let whileBody = [
      CSExpr {expr = CEApp {
        fun = _getIdentExn "Store_double_field",
        args = [
          CEVar {id = dstIdent},
          CEVar {id = iterIdent},
          CEBinOp {
            op = COSubScript (),
            lhs = CEVar {id = cvar.0},
            rhs = CEVar {id = countIdent}}]}},
      _incrementCounter countIdent
    ] in
    let tag = CEVar {id = _getIdentExn "Double_array_tag"} in
    let dimIdent = head dimIdents in
    _generateCToOCamlSequenceWrapper iterIdent dstIdent dimIdent tag whileBody
  | TySeq {ty = innerTy} ->
    let iterIdent = nameSym "i" in
    let innerDstIdent = nameSym "x" in
    let whileBody = join [
      [CSDef {
        ty = CTyVar {id = _getIdentExn "value"},
        id = Some innerDstIdent, init = None ()}],
      _generateCToOCamlWrapperInner countIdent cvars innerDstIdent
                                    (tail dimIdents) innerTy,
      [CSExpr {expr = CEApp {
        fun = _getIdentExn "Store_field",
        args = [
          CEVar {id = dstIdent},
          CEVar {id = iterIdent},
          CEVar {id = innerDstIdent}]}}]
    ] in
    let tag = CEInt {i = 0} in
    let dimIdent = head dimIdents in
    _generateCToOCamlSequenceWrapper iterIdent dstIdent dimIdent tag whileBody

  sem generateCToOCamlWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    let cvars = return.cTempVars in
    let dimIdents = return.dimIdents in
    let countIdent = nameSym "count" in
    let countDeclStmt = CSDef {
      ty = CTyInt (), id = Some countIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})
    } in
    let freeCvars =
      map
        (lam cvar : (Name, CType).
          CSExpr {expr = CEApp {
            fun = _getIdentExn "free",
            args = [CEVar {id = cvar.0}]}})
        cvars
    in
    let stmts = join [
      [countDeclStmt],
      _generateCToOCamlWrapperInner countIdent cvars return.ident
                                    dimIdents return.ty,
      freeCvars
    ] in
    (return, stmts)
end

lang FutharkCWrapper =
  OCamlToCWrapper + CToFutharkWrapper + FutharkCallWrapper +
  FutharkToCWrapper + CToOCamlWrapper + CProgAst

  sem generateCAMLparamDeclarations =
  | args /- : [ArgData] -/ ->
    let genParamStmt : [ArgData] -> String -> CExpr = lam args. lam funStr.
      let nargsStr = int2string (length args) in
      let camlParamIdent = _getIdentOrInitNew (concat funStr nargsStr) in
      CSExpr {expr = CEApp {
        fun = camlParamIdent,
        args = map (lam arg : ArgData. CEVar {id = arg.ident}) args}}
    in
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
        else [declStmt]
      in
      let remainingArgs = subsequence args 5 (length args) in
      cons fstDeclStmt (generateExtraParamDecl remainingArgs)
    else [fstDeclStmt]

  sem generateBytecodeWrapper (functionName : Name) =
  | nargs /- : Int -/ ->
    let valueTy = CTyVar {id = _getIdentExn "value"} in
    let bytecodeStr = concat (nameGetStr functionName) "_bytecode" in
    let bytecodeFunctionName = nameNoSym bytecodeStr in
    let args = nameSym "args" in
    let argc = nameSym "argc" in
    let functionArgs =
      map
        (lam i. CEBinOp {
          op = COSubScript (),
          lhs = CEVar {id = args},
          rhs = CEInt {i = i}})
        (create nargs (lam i. i))
    in
    CTFun {
      ret = valueTy,
      id = bytecodeFunctionName,
      params = [(CTyPtr {ty = valueTy}, args), (CTyInt (), argc)],
      body = [CSExpr {expr = CEApp {
        fun = functionName,
        args = functionArgs
      }}]
    }

  sem generateWrapperFunctionCode (functionName : Name) (returnType : Type) =
  | args /- : [(Name, Type)] -/ ->
    let toArgData = lam arg : (Name, Type).
      {{defaultArgData with ident = arg.0}
                       with ty = arg.1}
    in
    let bytecodeWrapper = generateBytecodeWrapper functionName (length args) in
    let returnIdent = nameSym "out" in
    let returnArg = (returnIdent, returnType) in
    let env = {{{emptyWrapperEnv with arguments = map toArgData args}
                                 with return = toArgData returnArg}
                                 with functionIdent = functionName}
    in
    let camlParamStmts = generateCAMLparamDeclarations env.arguments in
    let camlLocalStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "CAMLlocal1",
      args = [CEVar {id = returnIdent}]
    }} in
    let camlReturnStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "CAMLreturn",
      args = [CEVar {id = returnIdent}]
    }} in
    match generateOCamlToCWrapper env with (env, stmt1) then
      match generateCToFutharkWrapper env with (env, stmt2) then
        match generateFutharkCall env with (env, stmt3) then
          match generateFutharkToCWrapper env with (env, stmt4) then
            match generateCToOCamlWrapper env with (env, stmt5) then
              let value = _getIdentExn "value" in
              let withValueType = lam arg : (Name, Type).
                (CTyVar {id = value}, arg.0)
              in
              [ CTFun {
                  ret = CTyVar {id = value},
                  id = functionName,
                  params = map withValueType args,
                  body = join [camlParamStmts, [camlLocalStmt], stmt1, stmt2,
                               stmt3, stmt4, stmt5, [camlReturnStmt]]},
                bytecodeWrapper ]
            else never
          else never
        else never
      else never
    else never

  sem _getArgumentAndReturnTypes (acc : [Type]) =
  | TyArrow {from = from, to = to} ->
    _getArgumentAndReturnTypes (snoc acc from) to
  | ty -> (acc, ty)

  sem generateWrapperCode =
  | accelerated /- Map Name Type -/ ->
    let entryPointWrappers =
      map
        (lam entry : (Name, Type).
          match _getArgumentAndReturnTypes [] entry.1 with (argTypes, retType) then
            let identWithType = lam ty. (nameSym "a", ty) in
            let args : [(Name, Type)] = map identWithType argTypes in
            generateWrapperFunctionCode entry.0 retType args
          else never)
        (mapBindings accelerated)
    in
    -- NOTE(larshum, 2021-08-27): According to
    -- https://ocaml.org/manual/intfc.html CAML_NAME_SPACE should be defined
    -- before including caml headers, but the current C AST does not support
    -- this. It seems to be working without it, though.
    CPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"gpu.h\"",
        "\"caml/alloc.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops = join entryPointWrappers
    }
end

lang Test = FutharkCWrapper + CProgPrettyPrint + CPrettyPrint

mexpr

use Test in

let functionIdent = nameSym "f" in
let returnType = tyseq_ (tyseq_ (tyseq_ tyint_)) in
let args = [
  (nameSym "a", tyseq_ (tyseq_ (tyseq_ tyfloat_)))
] in

let wrapperCode = generateWrapperCode functionIdent returnType args in
()
-- print (printCProg [] wrapperCode)
