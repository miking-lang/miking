include "map.mc"
include "string.mc"
include "c/ast.mc"
include "c/pprint.mc"
include "futhark/pprint.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "pmexpr/extract.mc"
include "pmexpr/wrapper.mc"

let getFutharkSeqTypeString : String -> Int -> String =
  lam futharkElementTypeString. lam numDims.
  join [futharkElementTypeString, "_", int2string numDims, "d"]

lang FutharkCWrapperBase = PMExprCWrapper
  -- In the Futhark-specific environment, we store identifiers related to the
  -- Futhark context config and the context.
  syn TargetWrapperEnv =
  | FutharkTargetEnv {
      initContextIdent : Name, futharkContextConfigIdent : Name,
      futharkContextIdent : Name}

  sem getFutharkElementTypeString =
  | CTyChar _ | CTyInt64 _ -> "i64"
  | CTyDouble _ -> "f64"
  | CTyPtr t -> getFutharkElementTypeString t.ty

  sem getSeqFutharkTypeString =
  | SeqRepr t ->
    let elemTyStr = getFutharkElementTypeString t.elemTy in
    let dims = length t.dimIdents in
    join [elemTyStr, "_", int2string dims, "d"]

  sem getFutharkCType =
  | t & (SeqRepr _) ->
    let seqTypeStr = getSeqFutharkTypeString t in
    let seqTypeIdent = _getIdentOrInitNew seqTypeStr in
    CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}}
  | TensorRepr t -> error "Tensors are not supported in Futhark"
  | RecordRepr t ->
    -- TODO(larshum, 2022-03-09): How do we figure out this type?
    error "Records have not been implemented for Futhark"
  | BaseTypeRepr t -> t.ty
end

lang CToFutharkWrapper = FutharkCWrapperBase
  sem _generateCToFutharkWrapperArgH (ctxIdent : Name) (arg : ArgData) =
  | SeqRepr t ->
    let futharkSeqTypeStr = getSeqFutharkTypeString (SeqRepr t) in
    let seqTypeIdent = _getIdentOrInitNew (concat "futhark_" futharkSeqTypeStr) in
    let seqNewIdent = _getIdentOrInitNew (concat "futhark_new_" futharkSeqTypeStr) in
    let allocStmt = CSDef {
      ty = CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}},
      id = Some arg.gpuIdent,
      init = Some (CIExpr {expr = CEApp {
        fun = seqNewIdent,
        args =
          concat
            [CEVar {id = ctxIdent}, CEVar {id = t.dataIdent}]
            (map (lam id. CEVar {id = id}) t.dimIdents)}})} in
    let freeCTempStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "free",
      args = [CEVar {id = t.dataIdent}]}} in
    [allocStmt, freeCTempStmt]
  | TensorRepr t -> error "Tensors are not supported in Futhark"
  | RecordRepr t ->
    -- TODO(larshum, 2022-03-09): Implement support for passing records to
    -- Futhark.
    error "Record parameters have not been implemented for Futhark"
  | BaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some arg.gpuIdent,
      init = Some (CIExpr {expr = CEVar {id = t.ident}})}]

  sem _generateCToFutharkWrapperArg (ctxIdent : Name) (accStmts : [CStmt]) =
  | arg ->
    let arg : ArgData = arg in
    let stmts = _generateCToFutharkWrapperArgH ctxIdent arg arg.cData in
    concat accStmts stmts

  sem generateCToFutharkWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with FutharkTargetEnv fenv in
    let ctxIdent = fenv.futharkContextIdent in
    let initContextCall = CSExpr {expr = CEApp {
      fun = fenv.initContextIdent, args = []}} in
    cons
      initContextCall
      (foldl (_generateCToFutharkWrapperArg ctxIdent) [] env.arguments)
end

lang FutharkCallWrapper = FutharkCWrapperBase + FutharkIdentifierPrettyPrint
  sem generateFutharkCall =
  | env ->
    let env : CWrapperEnv = env in
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
      match pprintVarName pprintEnvEmpty env.functionIdent with (_, ident) then
        ident
      else never
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
          match arg.cData with BaseTypeRepr _ then
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
            match arg.cData with SeqRepr t then
              let futTypeStr = getSeqFutharkTypeString (SeqRepr t) in
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
  sem _generateFutharkToCWrapperH (ctxIdent : Name) (srcIdent : Name) =
  | SeqRepr t ->
    -- Find dimensions of result value through the use of 'futhark_shape_*'
    let futReturnTypeString = getSeqFutharkTypeString (SeqRepr t) in
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
      ty = cType, id = Some t.dataIdent,
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
        CEVar {id = t.dataIdent}]}} in

    -- Free Futhark memory
    let futFreeString = concat "futhark_free_" futReturnTypeString in
    let futFreeIdent = _getIdentOrInitNew futFreeString in
    let freeFutharkStmt = CSExpr {expr = CEApp {
      fun = futFreeIdent,
      args = [CEVar {id = ctxIdent}, CEVar {id = srcIdent}]}} in

    join [
      [dimsStmt], dimInitStmts,
      [sizeInitStmt, cAllocStmt, copyFutharkToCStmt, freeFutharkStmt]]
  | TensorRepr t -> error "Tensors are not supported in Futhark"
  | RecordRepr t ->
    -- TODO(larshum, 2022-03-09): Implement support for returning records from
    -- Futhark.
    error "Record return values have not been implemented for Futhark"
  | BaseTypeRepr t ->
    [CSDef {
      ty = CTyPtr {ty = t.ty}, id = Some t.ident,
      init = Some (CIExpr {expr = CEUnOp {
        op = COAddrOf (),
        arg = CEVar {id = srcIdent}}})}]

  sem generateFutharkToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with FutharkTargetEnv fenv in
    let futCtx = fenv.futharkContextIdent in
    let return = env.return in
    _generateFutharkToCWrapperH futCtx return.gpuIdent return.cData
end

lang FutharkCWrapper =
  CToFutharkWrapper + FutharkCallWrapper + FutharkToCWrapper + CProgAst

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
  sem futharkContextInit =
  | env /- : CWrapperEnv -> [CTop] -/ ->
    let env : CWrapperEnv = env in
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
        "\"gpu.h\"",
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
let dataEntry : AcceleratedData = {
  identifier = functionIdent,
  bytecodeWrapperId = nameSym "fbyte",
  params = [(nameSym "s", tyseq_ tyint_)],
  returnType = tyseq_ tyint_,
  info = NoInfo ()
} in
let accelerated = mapFromSeq nameCmp [(functionIdent, dataEntry)] in

let wrapperCode = generateWrapperCode accelerated in
-- print (printCProg [] wrapperCode);
()
