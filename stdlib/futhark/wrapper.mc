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
    "Long_val", "Bool_val", "Double_val", "Val_long", "Val_bool", "Val_double",
    "Wosize_val", "caml_alloc", "Field", "Store_field", "Double_field",
    "Store_double_field", "Double_array_tag", "futhark_context_config",
    "futhark_context_config_new", "futhark_context", "futhark_context_config",
    "futhark_context_sync", "futhark_context_get_error"]
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
  ident = nameNoSym "", ty = TyUnknown {info = NoInfo ()}, cTempIdents = [],
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

  -- The Futhark context config and context variable identifiers.
  futharkContextConfigIdent : Name,
  futharkContextIdent : Name
}

let emptyWrapperEnv = {
  arguments = [], return = [], keywordIdentMap = mapEmpty cmpString,
  futharkContextConfigIdent = nameNoSym "", futharkContextIdent = nameNoSym ""
}

let getFutharkTypeString : Type -> String = use MExprAst in
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

lang CWrapperBase = MExprAst + CAst + MExprPrettyPrint
  sem _wosize =
  | id ->
      CEApp {fun = _getIdentExn "Wosize_val", args = [CEVar {id = id}]}

  sem getFutharkElementTypeString =
  | ty & (CTyVar {id = id}) ->
    if nameEq id (_getIdentExn "int64_t") then
      "i64"
    else error (join ["Unsupported C type: ", type2str ty])
  | CTyDouble _ -> "f64"
  | CTyPtr t -> getFutharkElementTypeString t.ty
  | ty -> error (join ["Cannot generate Futhark type string from C type ", type2str ty])

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
  | ty -> error (join ["Translation of type ", type2str ty, " to C is not supported"])
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
    let cvar = head cvars in
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
    let initExpr =
      match ty with CTyPtr {ty = elemTy} then
        Some (CIExpr {expr = CECast {
          ty = ty,
          rhs = CEApp {
            fun = _getIdentExn "malloc",
            args = [CEBinOp {
              op = COMul (),
              lhs = CEVar {id = arg.sizeIdent},
              rhs = CESizeOfType {ty = elemTy}}]}}})
      else None ()
    in
    let stmt = CSDef {ty = ty, id = Some cIdent, init = initExpr} in
    let arg = {arg with cTempVars = snoc arg.cTempVars (cIdent, ty)} in
    (arg, stmt)

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
        -- NOTE(larshum, 2021-09-01): Assumes we never get empty nested
        -- sequences, or this would crash at runtime.
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEInt {i = 0}]}})} in
      match _computeDimensionsH arg innerSrcIdent innerTy with (arg, stmts) then
        (arg, concat [initDimStmt, updateSizeStmt, innerSrcStmt] stmts)
      else never
    else (arg, [initDimStmt, updateSizeStmt])
  | ty -> []

  sem _computeDimensions (env : CWrapperEnv) =
  | arg ->
    let arg : ArgData = arg in
    let arg = {arg with sizeIdent = nameSym "n"} in
    let initStmt = CSDef {
      ty = CTyInt (), id = Some arg.sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    _computeDimensionsH arg arg.ident arg.ty

  sem _generateOCamlToCWrapperArg =
  | arg ->
    let arg : ArgData = arg in
    match _computeDimensions arg with (arg, dimStmts) then
      let cTypes = mexprToCTypes arg.ty in
      match mapAccumL _generateOCamlToCAlloc arg cTypes with (arg, allocStmts) then
        let copyStmts =
          _generateOCamlToCWrapperInner
            arg.ident arg.cTempVars arg.dimIdents arg.ty
        in
        (arg, join [dimStmts, allocStmts, copyStmts])
      else never
    else never

  sem generateOCamlToCWrapper =
  | env ->
    match mapAccumL _generateOCamlToCWrapperArg env.arguments
    with (args, stmts) then
      ({env with arguments = args}, join stmts)
    else never
end

lang CToFutharkWrapper = CWrapperBase
  sem _generateCToFutharkWrapperInner (ctxIdent : Name) (arg : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head arg.cTempVars in
    let futIdent = nameSym "fut_tmp" in
    let stmt = CSDef {
      ty = cvar.1, id = Some futIdent,
      init = Some (CIExpr {expr = CEVar {id = cvar.0}})}
    in
    let arg = {arg with futIdent = futIdent} in
    (arg, [stmt])
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
    let seqTypeIdent = concat "futhark_" futharkSeqTypeStr in
    let seqNewIdent = concat "futhark_new_" futharkSeqTypeStr in
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

  sem _generateCToFutharkWrapperArg (ctxIdent : Name) =
  | arg ->
    let arg : ArgData = arg in
    _generateCToFutharkWrapperInner ctxIdent arg.cTempVars arg.dimIdents arg.ty

  sem generateCToFutharkWrapper =
  | env ->
    let env : CWrapperEnv = env in
    let ctxConfigIdent = nameSym "cfg" in
    let ctxIdent = nameSym "ctx" in
    let env = {{env with futharkContextConfigIdent = ctxConfigIdent}
                    with futharkContextIdent = ctxIdent} in
    let configInitStmts = [
      CSDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxConfigIdent, mem = None ()}},
        id = Some ctxConfigIdent,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "futhark_context_config_new", args = []}})},
      CSDef {
        ty = CTyPtr {ty = CTyStruct {id = Some ctxIdent, mem = None ()}},
        id = Some ctxIdent,
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "futhark_context_new",
          args = [CEVar {id = ctxConfigIdent}]}})}
    ] in
    match mapAccumL (_generateCToFutharkWrapperArg ctxIdent) env.arguments
    with (args, futharkCopyStmts) then
      ({env with arguments = args}, join [configInitStmts, futharkCopyStmts])
    else never
end

lang FutharkCallWrapper = CWrapperBase
  sem generateFutharkCall =
  | env ->
    let env : CWrapperEnv = env in
    let return = env.return in
    let functionId = return.ident in
    let returnType = return.ty in

    -- Declare Futhark return value
    let futReturnTypeString = getFutharkTypeString returnType in
    let futReturnTypeIdent = _getIdentOrInitNew futReturnTypeString in
    let futResultIdent = nameSym "fut_ret" in
    let futResultDeclStmt = CSDef {
      ty = CTyVar {id = futReturnTypeIdent},
      id = Some futResultIdent,
      init = None ()
    } in
    let funcId = nameSym (concat "futhark_entry_" (nameGetStr functionId)) in
    let returnCodeIdent = nameSym "v" in
    let returnCodeDeclStmt = CSDef {
      ty = CTyInt (), id = Some returnCodeIdent, init = None ()
    } in

    -- Call Futhark entry point
    let functionCallStmt = CSExpr {expr = CEBinOp (),
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = funcId,
        args =
          concat
            [ CEVar {id = env.futharkContextIdent}
            , CEUnOp {op = COAddrOf (), arg = CEVar {id = futResultIdent}} ]
            (map (lam arg : ArgData. CEVar {id = arg.futIdent}) env.arguments)}
    } in

    -- Handle Futhark errors by printing the error message and exiting
    let errorHandlingStmt = CSIf {
      cond = CEBinOp {
        op = CONeq (),
        lhs = CEVar {ident = returnCodeIdent},
        rhs = CEInt {i = 0}},
      thn = [
        CSExpr {expr = CEApp {
          fun = _getIdentExn "printf",
          args = [
            CEString {s = "Runtime error in generated code: %s\\n"},
            CEApp {
              fun = _getIdentExn "futhark_context_get_error",
              args = [CEVar {id = env.futharkContextIdent}]}]}},
        CSExpr {expr = CEApp {
          fun = _getIdentExn "exit",
          args = [CEVar {id = returnCodeIdent}]}}],
      els = []
    } in
    let contextSyncStmt = CSDef {
      ty = CTyInt (), id = Some returnCodeIdent,
      init = Some (CIExpr {expr = CEApp {
        fun = _getIdentExn "futhark_context_sync",
        args = [CEVar {id = env.futharkContextIdent}]}})
    } in

    -- Deallocate the Futhark input values
    let deallocStmts =
      join
        (map
          (lam arg : ArgData.
            match arg.ty with TySeq _ then
              let futTypeStr = getFutharkTypeString arg.ty in
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
    let cIdent = nameSym "c_tmp" in
    let return = {return with cTempVars = [(cIdent, ctype)]} in
    ( return
    , [CSDef {
        ty = ctype, id = Some cIdent,
        init = Some (CIExpr {expr = CEVar {id = return.futIdent}})}] )
  | ty & (TySeq _) ->
    let ctype = head (mexprToCTypes ty) in
    let cIdent = nameSym "c_tmp" in
    
    -- Find dimensions of result value through 'futhark_shape_*'
    let futReturnTypeString = getFutharkTypeString ty in
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
    let sizeIdent = nameSym "n" in
    let sizeDeclStmt = CSDef {
      ty = CTyInt (), id = Some sizeIdent, init = CEInt {i = 1}
    } in
    let ndims = getDimensionsOfType ty in
    let dimIdents = create ndims (lam. nameSym "d") in
    let dimInitStmts =
      mapi
        (lam i. lam ident.
          CSDef {
            ty = CTyInt (), id = Some ident,
            init = CEBinOp {
              op = COSubScript (),
              lhs = CEVar {id = dimIdent},
              rhs = CEInt {i = i}}})
        dimIdents
    in
    let dimProdStmts =
      foldl
        (lam expr. lam id.
          CEBinOp {op = COMul (), lhs = expr, rhs = CEVar {id = id}})
        (CEVar {id = head dimIdents})
        (tail dimIdents)
    in

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
    (return, join [[dimsStmt], dimInitStmts, dimProdStmts,
                   [preallocStmt, copyFutharkToCStmt, freeFutharkStmt]])

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
  sem _generateCToOCamlSequenceWrapper (iterIdent : Name) (dimIdent : Name)
                                       (dimIndex : Int) (dstIdent : Name)
                                       (tag : CExpr) =
  | whileBody /- : [CStmt] -/ ->
    let lenIdent = nameSym "n" in
    [CSDef {
      ty = CTyInt (), id = Some iterIdent,
      init = Some (CIExpr {expr = CEInt {i = 0}})},
    CSDef {
      ty = CTyInt (), id = Some lenIdent,
      init = Some (CIExpr {expr = CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = dimIdent},
        rhs = CEInt {i = dimIndex}}})},
    CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = dstIdent},
      rhs = CEApp {
        fun = _getIdentExn "caml_alloc",
        args = [CEVar {id = lenIdent}, tag]}}},
    CSWhile {
      cond = CEBinOp {
        op = COLt (),
        lhs = CEVar {id = iterIdent},
        rhs = CEVar {id = lenIdent}},
      body =
        snoc
          whileBody
          (CSExpr {expr = CEBinOp {
            op = COAssign (),
            lhs = CEVar {id = iterIdent},
            rhs = CEBinOp {
              op = COAdd (),
              lhs = CEVar {id = iterIdent},
              rhs = CEInt {i = 1}}}})}]

  sem _generateCToOCamlWrapperInner (returns : [(CType, Name)])
                                    (dstIdent : Name) (dimIdent : Name)
                                    (dimIndex : Int) =
  | TyInt _ | TyChar _ ->
    let return : (CType, Name) = head returns in
    let returnIdent = return.1 in
    []
    -- [_assignConvertedTerm dstIdent "Val_long" returnIdent]
  | TyFloat _ ->
    let return : (CType, Name) = head returns in
    let returnIdent = return.1 in
    []
    --[_assignConvertedTerm dstIdent "caml_copy_double" returnIdent]
  | TySeq {ty = TyFloat _} ->
    let return : (CType, Name) = head returns in
    let returnIdent = return.1 in
    let iterIdent = nameSym "i" in
    let whileBody = [
      CSExpr {expr = CEApp {
        fun = _getIdentExn "Store_double_field",
        args = [
          CEVar {id = dstIdent},
          CEVar {id = iterIdent},
          CEBinOp {
            op = COSubScript (),
            lhs = CEVar {id = returnIdent},
            rhs = CEVar {id = iterIdent}}]}}] in
    let tag = CEVar {id = _getIdentExn "Double_array_tag"} in
    _generateCToOCamlSequenceWrapper iterIdent dimIdent dimIndex dstIdent tag
                                     whileBody
  | TySeq {ty = innerTy} ->
    let iterIdent = nameSym "i" in
    let innerReturns = map (lam ret : (CType, Name). (ret.0, nameSym "r")) returns in
    let innerReturnAssignments =
      map
        (lam entry : ((CType, Name), (CType, Name)).
          let ctype = (entry.0).0 in
          let returnId = (entry.0).1 in
          let innerReturnId = (entry.1).1 in
          CSDef {
            ty = CTyPtr {ty = ctype}, id = Some innerReturnId,
            init = Some (CIExpr {expr = CEUnOp {
              op = COAddrOf (),
              arg = CEBinOp {
                op = COSubScript (),
                lhs = CEVar {id = returnId},
                rhs = CEVar {id = iterIdent}}}})})
        (zip returns innerReturns) in
    let innerDstIdent = nameSym "x" in
    let whileBody = join [
      innerReturnAssignments,
      [CSDef {
        ty = CTyVar {id = _getIdentExn "value"},
        id = Some innerDstIdent, init = None ()}],
      _generateCToOCamlWrapperInner innerReturns innerDstIdent dimIdent
                                    (addi dimIndex 1) innerTy,
      [CSExpr {expr = CEApp {
        fun = _getIdentExn "Store_field",
        args = [
          CEVar {id = dstIdent},
          CEVar {id = iterIdent},
          CEVar {id = innerDstIdent}]}}]
    ] in
    let tag = CEInt {i = 0} in
    _generateCToOCamlSequenceWrapper iterIdent dimIdent dimIndex dstIdent tag
                                     whileBody

  sem _generateCToOCamlWrapper (returns : [(CType, Name)]) (dstIdent : Name)
                               (dimIdent : Name) =
  | ty ->
    _generateCToOCamlWrapperInner returns dstIdent dimIdent 0 ty
end

lang FutharkCWrapper = OCamlToCWrapper + CToFutharkWrapper +
                       FutharkToCWrapper + CToOCamlWrapper + CProgAst
  sem generateWrapperFunctionCode (function : (Name, Type)) =
  | args /- : [(Name, Type)] -/ ->
    let toArgData = lam arg : (Name, Type).
      {{defaultArgData with ident = arg.0}
                       with ty = arg.1}
    in
    let env = {{emptyWrapperEnv with arguments = map toArgData args}
                                with return = toArgData function} in
    match generateOCamlToCWrapper env with (env, stmt1) then
      match generateCToFutharkWrapper env with (env, stmt2) then
        match generateFutharkToCWrapper env with (env, stmt3) then
          match mapAccumL (_generateCToOCamlWrapper env) args with (env, stmt4) then
            let value = _getIdentExn "value" in
            let withValueType = lam arg : (Name, Type).
              (arg.0, CTyVar {id = value})
            in
            CTFun {
              ret = CTyVar {id = value},
              id = function.0,
              params = map withValueType args,
              body = join [stmt1, stmt2, stmt3, stmt4]}
          else never
        else never
      else never
    else never

  sem generateWrapperCode (function : (Name, Type)) =
  | args /- : [(Name, Type)] -/ ->
    -- NOTE(larshum, 2021-08-27): According to
    -- https://ocaml.org/manual/intfc.html CAML_NAME_SPACE should be defined
    -- before including caml headers, but the current C AST does not support
    -- this. It seems to be working without it, though.
    CPProg {
      includes = [
        "<stddef.h>",
        "<stdlib.h>",
        "<stdio.h>",
        "\"program.h\"",
        "\"caml/alloc.h\"",
        "\"caml/memory.h\"",
        "\"caml/mlvalues.h\""
      ],
      tops = generateWrapperFunctionCode function args
    }
end

lang Test = OCamlToCWrapper + CToFutharkWrapper + FutharkToCWrapper + CToOCamlWrapper + CPrettyPrint

mexpr

use Test in

let srcIdent = nameSym "src" in
let dstIdents = [nameSym "dst"] in
let elemTy = tyfloat_ in
let ocamlArgTy = tyseq_ (tyseq_ elemTy) in
let cType = head (mexprToCTypes elemTy) in
--print (printCStmts 0 pprintEnvEmpty
--  (generateOCamlToCWrapper srcIdent ocamlArgTy)).1;

print "\n\n";

let dim1 = nameSym "dim1" in
let dim2 = nameSym "dim2" in
--print (printCStmts 0 pprintEnvEmpty
--  (_generateCToFutharkWrapper cType [srcIdent] [dim1, dim2] ocamlArgTy)).1;

print "\n\n";

let returns = [(CTyDouble (), nameSym "dst")] in
let ctxConfigIdent = nameSym "config" in
let ctxIdent = nameSym "ctx" in
let dimIdents = [dim1, dim2] in
let dstIdent = nameSym "ret" in
--print (printCStmts 0 pprintEnvEmpty
--  (_generateFutharkToCWrapper ctxConfigIdent ctxIdent dimIdents (head returns) ocamlArgTy)).1;

print "\n\n";

let dstIdent = nameSym "out" in
let dimIdent = nameSym "dim" in
print (printCStmts 0 pprintEnvEmpty
  (_generateCToOCamlWrapper returns dstIdent dimIdent ocamlArgTy)).1

