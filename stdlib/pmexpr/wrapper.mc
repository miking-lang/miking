include "c/ast.mc"
include "pmexpr/ast.mc"

-- TODO(larshum, 2022-01-19): Figure out a way to make this set of names
-- extensible for the individual wrappers, instead of having to include all of
-- them here.
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
    "futhark_context_get_error", "NULL",
    "cudaMalloc", "cudaFree", "cudaMemcpy", "cudaDeviceSynchronize",
    "cudaMemcpyHostToDevice", "cudaMemcpyDeviceToHost"]
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

type ArgData = {
  -- The identifier and the MExpr type of the argument.
  ident : Name,
  ty : Type,

  -- The identifiers of the C variable(s) containing values used to represent
  -- this variable. This is a sequence because the fields of records and tuples
  -- are placed in one array each.
  cTempVars : [(Name, CType)],

  -- The identifier of the GPU variable.
  gpuIdent : Name,

  -- Identifiers of variables containing the dimensions of the array, starting
  -- with the outermost dimension. This sequence is empty if the type of the
  -- argument is not a sequence.
  dimIdents : [Name],

  -- The identifier of a variable containing the full size of the array.
  sizeIdent : Name
}

let defaultArgData = use MExprAst in {
  ident = nameNoSym "", ty = TyUnknown {info = NoInfo ()}, cTempVars = [],
  gpuIdent = nameNoSym "", dimIdents = [], sizeIdent = nameNoSym ""}

let emptyWrapperEnv = {
  arguments = [], return = defaultArgData,
  keywordIdentMap = mapEmpty cmpString, functionIdent = nameNoSym ""}

recursive let getDimensionsOfType : Type -> Int = use MExprAst in
  lam ty.
  match ty with TySeq {ty = innerTy} then
    addi 1 (getDimensionsOfType innerTy)
  else 0
end

lang PMExprCWrapperBase = MExprAst + CAst
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
    { arguments = [], return = defaultArgData
    , keywordIdentMap = mapEmpty cmpString, functionIdent = nameNoSym ""
    , targetEnv = EmptyTargetEnv () }

  sem _wosize = 
  | id -> CEApp {fun = _getIdentExn "Wosize_val", args = [CEVar {id = id}]}

  -- Converts a given MExpr type to a sequence containing the C type or types
  -- used to represent it in the C wrapper.
  sem mexprToCTypes =
  | TyInt _ | TyChar _ -> [CTyVar {id = _getIdentExn "int64_t"}]
  | TyFloat _ -> [CTyDouble {}]
  | TySeq {ty = elemTy & !(TySeq _)} ->
    map (lam ty. CTyPtr {ty = ty}) (mexprToCTypes elemTy)
  | TySeq t -> mexprToCTypes t.ty
  | TyRecord t ->
    infoErrorExit t.info (join ["Records cannot be a free variable in, or ",
                                "returned from, an accelerated term"])
  | t ->
    let tyStr = use MExprPrettyPrint in type2str t in
    infoErrorExit (infoTy t) (join ["Terms of type '", tyStr,
                                     "' cannot be accelerated"])
end

lang PMExprOCamlToCWrapper = PMExprCWrapperBase
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
    match dimIdents with [dimIdent] ++ remainingDimIdents in
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
        -- NOTE(larshum, 2022-01-18): If a multi-dimensional sequence happens
        -- to be empty, this will result in a runtime error.
        init = Some (CIExpr {expr = CEApp {
          fun = _getIdentExn "Field",
          args = [CEVar {id = srcIdent}, CEInt {i = 0}]}})} in
      match _computeDimensionsH arg innerSrcIdent innerTy with (arg, stmts) in
      (arg, concat [initDimStmt, updateSizeStmt, innerSrcStmt] stmts)
    else (arg, [initDimStmt, updateSizeStmt])
  | _ -> (arg, [])

  sem _computeDimensions =
  | arg ->
    let arg : ArgData = arg in
    let arg = {arg with sizeIdent = nameSym "n"} in
    let initStmt = CSDef {
      ty = CTyInt (), id = Some arg.sizeIdent,
      init = Some (CIExpr {expr = CEInt {i = 1}})} in
    match _computeDimensionsH arg arg.ident arg.ty with (arg, stmts) in
    (arg, cons initStmt stmts)

  sem _generateOCamlToCWrapperArg (accStmts : [CStmt]) =
  | arg ->
    match _computeDimensions arg with (arg, dimStmts) in
    let arg : ArgData = arg in
    let cTypes = mexprToCTypes arg.ty in
    match mapAccumL _generateOCamlToCAlloc arg cTypes with (arg, allocStmts) in
    let arg : ArgData = arg in
    let copyStmts =
      _generateOCamlToCWrapperInner
        arg.ident arg.cTempVars arg.dimIdents arg.ty in
    (join [accStmts, dimStmts, join allocStmts, copyStmts], arg)

  sem generateOCamlToCWrapper =
  | env ->
    let env : CWrapperEnv = env in
    match mapAccumL _generateOCamlToCWrapperArg [] env.arguments with (stmts, args) in
    ({env with arguments = args}, stmts)
end

lang PMExprCToOCamlWrapper = PMExprCWrapperBase
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
    let stmts =
      match return.ty with TyInt _ | TyChar _ | TyFloat _ then
        let cvar : (Name, CType) = head cvars in
        let returnPtrIdent = nameSym "ret_ptr" in
        let returnPtrStmt = CSDef {
          ty = CTyPtr {ty = cvar.1}, id = Some returnPtrIdent,
          init = Some (CIExpr {expr = CEUnOp {
            op = COAddrOf (),
            arg = CEVar {id = cvar.0}
          }})
        } in
        let cvars = [(returnPtrIdent, CTyPtr {ty = cvar.1})] in
        join [
          [countDeclStmt, returnPtrStmt],
          _generateCToOCamlWrapperInner countIdent cvars return.ident
                                        dimIdents return.ty]
      else
        let freeCvars =
          join (
            map
              (lam cvar : (Name, CType).
                match cvar.1 with CTyPtr _ then
                  [CSExpr {expr = CEApp {
                    fun = _getIdentExn "free",
                    args = [CEVar {id = cvar.0}]}}]
                else [])
              cvars)
        in
        join [
          [countDeclStmt],
          _generateCToOCamlWrapperInner countIdent cvars return.ident
                                        dimIdents return.ty,
          freeCvars]
    in
    (return, stmts)
end

-- Defines an extensible C wrapper generation language fragment. This fragment
-- can be extended to implement the target-specific parts of the wrapper, while
-- allowing reuse of the parts that all targets will have in common.
lang PMExprCWrapper =
  PMExprCWrapperBase + PMExprOCamlToCWrapper + PMExprCToOCamlWrapper

  -- Generates an additional wrapper function to be referenced from OCaml. This
  -- function is used when calling from bytecode (hence the name) and also when
  -- the function takes more than five parameters.
  sem generateBytecodeWrapper =
  | data ->
    let data : AccelerateData = data in
    let valueTy = CTyVar {id = _getIdentExn "value"} in
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
    CTFun {
      ret = valueTy,
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
        args = map (lam arg : ArgData. CEVar {id = arg.ident}) args}} in
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

  sem generateMarshallingCode =

  -- Generates the main function of the wrapper code. This is the function that
  -- manages the marshalling between OCaml and the target GPU language.
  sem generateWrapperFunctionCode (env : CWrapperEnv) =
  | data ->
    let data : AccelerateData = data in
    let toArgData = lam arg : (Name, Type).
      {{defaultArgData with ident = arg.0}
                       with ty = arg.1} in
    let bytecodeWrapper = generateBytecodeWrapper data in
    let returnIdent = nameSym "out" in
    let returnArg = (returnIdent, data.returnType) in
    let env = {{{env with arguments = map toArgData data.params}
                     with return = toArgData returnArg}
                     with functionIdent = data.identifier} in
    let camlParamStmts = generateCAMLparamDeclarations env.arguments in
    let camlLocalStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "CAMLlocal1",
      args = [CEVar {id = returnIdent}]}} in
    let camlReturnStmt = CSExpr {expr = CEApp {
      fun = _getIdentExn "CAMLreturn",
      args = [CEVar {id = returnIdent}]}} in
    match generateMarshallingCode env with (env, stmts) in
    let value = _getIdentExn "value" in
    let withValueType = lam arg : (Name, Info, Type).
      (CTyVar {id = value}, arg.0) in
    [ CTFun {
        ret = CTyVar {id = value},
        id = data.identifier,
        params = map withValueType data.params,
        body = join [camlParamStmts, [camlLocalStmt], stmts, [camlReturnStmt]]}
    , bytecodeWrapper ]

  sem generateWrapperCodeH (env : CWrapperEnv) =
  | accelerated /- Map Name AccelerateData -/ ->
    let entryPointWrappers =
      map (generateWrapperFunctionCode env) (mapValues accelerated) in
    (env, join entryPointWrappers)
end
