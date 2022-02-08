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

let getMExprSeqFutharkTypeString : Type -> String = use MExprAst in
  lam ty.
  recursive let work = lam dim. lam typ.
    match typ with TySeq {ty = innerTy} then
      work (addi dim 1) innerTy
    else match typ with TyInt _ | TyChar _ then
      (dim, "i64")
    else match typ with TyFloat _ then
      (dim, "f64")
    else
      let tyStr = use MExprPrettyPrint in type2str typ in
      infoErrorExit (infoTy typ) (join ["Cannot accelerate sequences with ",
                                        "elements of type ", tyStr])
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

lang FutharkCWrapperBase = PMExprCWrapper
  -- In the Futhark-specific environment, we store identifiers related to the
  -- Futhark context config and the context.
  syn TargetWrapperEnv =
  | FutharkTargetEnv {
      initContextIdent : Name, futharkContextConfigIdent : Name,
      futharkContextIdent : Name}

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
    else
      let tyStr = use CPrettyPrint in printCType "" pprintEnvEmpty ty in
      infoErrorExit (infoTy ty) (join ["Terms of type '", tyStr,
                                       "' cannot be accelerated"])
  | CTyDouble _ -> "f64"
  | CTyPtr t -> getFutharkElementTypeString t.ty
end

lang CToFutharkWrapper = FutharkCWrapperBase
  sem _generateCToFutharkWrapperInner (ctxIdent : Name) (arg : ArgData) =
  | TyInt _ | TyChar _ | TyFloat _ ->
    let cvar : (Name, CType) = head arg.cTempVars in
    ({arg with gpuIdent = cvar.0}, [])
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
    let gpuIdent = nameSym "fut_tmp" in
    let allocStmt = CSDef {
      ty = CTyPtr {ty = CTyStruct {id = Some seqTypeIdent, mem = None ()}},
      id = Some gpuIdent,
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
    let arg = {arg with gpuIdent = gpuIdent} in
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
    match env.targetEnv with FutharkTargetEnv targetEnv in
    let ctxIdent = targetEnv.futharkContextIdent in
    let initContextCall =
      CSExpr {expr = CEApp { fun = targetEnv.initContextIdent, args = []}}
    in
    match mapAccumL (_generateCToFutharkWrapperArg ctxIdent) [] env.arguments
    with (futharkCopyStmts, args) then
      ({env with arguments = args}, cons initContextCall futharkCopyStmts)
    else never
end

lang FutharkCallWrapper = FutharkCWrapperBase + FutharkIdentifierPrettyPrint
  sem generateFutharkCall =
  | env ->
    let env : CWrapperEnv = env in
    match env.targetEnv with FutharkTargetEnv targetEnv in
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
    let functionStr =
      match pprintVarName pprintEnvEmpty env.functionIdent with (_, ident) then
        ident
      else never
    in
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
            CEVar {id = arg.gpuIdent}
          else
            CEUnOp {op = CODeref (), arg = CEVar {id = arg.gpuIdent}})
        env.arguments
    in
    let functionCallStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = funcId,
        args =
          concat
            [ CEVar {id = targetEnv.futharkContextIdent}
            , CEUnOp {op = COAddrOf (), arg = CEVar {id = futResultIdent}} ]
            args}
    }} in
    let contextSyncStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEVar {id = returnCodeIdent},
      rhs = CEApp {
        fun = _getIdentExn "futhark_context_sync",
        args = [CEVar {id = targetEnv.futharkContextIdent}]}
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
              args = [CEVar {id = targetEnv.futharkContextIdent}]}]}},
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
                  CEVar {id = targetEnv.futharkContextIdent},
                  CEVar {id = arg.gpuIdent}]}}]
            else [])
          env.arguments)
    in

    let return = {return with gpuIdent = futResultIdent} in
    let stmts =
      concat
        [futResultDeclStmt, returnCodeDeclStmt, functionCallStmt,
         errorHandlingStmt, contextSyncStmt, errorHandlingStmt]
        deallocStmts
    in
    ({env with return = return}, stmts)
end

lang FutharkToCWrapper = FutharkCWrapperBase
  sem _generateFutharkToCWrapperInner (ctxIdent : Name) (return : ArgData) =
  | ty & (TyInt _ | TyChar _ | TyFloat _) ->
    let ctype = head (mexprToCTypes ty) in
    let cIdent = return.gpuIdent in
    let return = {return with cTempVars = [(cIdent, ctype)]} in
    (return, [])
  | ty & (TySeq _) ->
    let ctype = head (mexprToCTypes ty) in
    let cIdent = nameSym "c_tmp" in
    
    -- Find dimensions of result value through 'futhark_shape_*'
    let futReturnTypeString = getMExprSeqFutharkTypeString ty in
    let futharkShapeString = concat "futhark_shape_" futReturnTypeString in
    let futharkShapeIdent = _getIdentOrInitNew futharkShapeString in
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
            CEVar {id = return.gpuIdent}]}}})
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
        CEVar {id = return.gpuIdent},
        CEVar {id = cIdent}]
    }} in

    -- Free Futhark memory
    let futFreeString = join ["futhark_free_", futReturnTypeString] in
    let futFreeIdent = _getIdentOrInitNew futFreeString in
    let freeFutharkStmt = CSExpr {expr = CEApp {
      fun = futFreeIdent,
      args = [CEVar {id = ctxIdent}, CEVar {id = return.gpuIdent}]
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
    match env.targetEnv with FutharkTargetEnv targetEnv in
    let futCtx = targetEnv.futharkContextIdent in
    match _generateFutharkToCWrapperInner futCtx env.return env.return.ty
    with (return, copyStmts) then
      ({env with return = return}, copyStmts)
    else never
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
    match env.targetEnv with FutharkTargetEnv targetEnv in
    let ctxConfigStructId = _getIdentExn "futhark_context_config" in
    let ctxStructId = _getIdentExn "futhark_context" in
    let ctxConfigIdent = targetEnv.futharkContextConfigIdent in
    let ctxIdent = targetEnv.futharkContextIdent in
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
        id = targetEnv.initContextIdent,
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
    match generateOCamlToCWrapper env with (env, stmt1) in
    match generateCToFutharkWrapper env with (env, stmt2) in
    match generateFutharkCall env with (env, stmt3) in
    match generateFutharkToCWrapper env with (env, stmt4) in
    match generateCToOCamlWrapper env with (env, stmt5) in
    (env, join [stmt1, stmt2, stmt3, stmt4, stmt5])

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
