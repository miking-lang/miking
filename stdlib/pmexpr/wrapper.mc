include "c/ast.mc"
include "pmexpr/ast.mc"
include "pmexpr/extract.mc"

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
    "CAML_BA_C_LAYOUT", "qsort"]
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

-- Defines an extensible C wrapper generation language fragment. This fragment
-- can be extended to implement the target-specific parts of the wrapper, while
-- allowing reuse of the parts that all targets will have in common.
lang PMExprCWrapper = MExprAst + CAst + PMExprExtractAccelerate
  -- Defines a representation of a certain data type, with the specifics
  -- defined per backend.
  syn CDataRepr =
  | PlaceholderRepr ()

  type ArgData = {
    -- The identifier and type of the OCaml value representing the MExpr
    -- argument.
    mexprIdent : Name,
    mexprType : Type,

    -- A status used to determine whether copying a parameter can be omitted,
    -- when copying between OCaml and the accelerate backend. Currently only
    -- used for tensors in the CUDA backend.
    copyStatus : CopyStatus,

    -- The intermediate representation of the argument in C.
    cData : CDataRepr,

    -- The identifier of the argument in the GPU backend. We do not store an
    -- explicit type of the argument as the type is backend-specific.
    gpuIdent : Name
  }

  sem defaultArgData : () -> ArgData
  sem defaultArgData =
  | () ->
    { mexprIdent = nameNoSym "", mexprType = tyunknown_
    , copyStatus = CopyBoth () , cData = PlaceholderRepr ()
    , gpuIdent = nameNoSym "" }

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

  sem _emptyWrapperEnv : () -> CWrapperEnv
  sem _emptyWrapperEnv =
  | () ->
    { arguments = [], return = defaultArgData (), functionIdent = nameNoSym ""
    , targetEnv = EmptyTargetEnv () }

  sem _wosize : CExpr -> CExpr
  sem _wosize = 
  | e -> CEApp {fun = _getIdentExn "Wosize_val", args = [e]}

  sem isBaseType : Type -> Bool
  sem isBaseType =
  | TyInt _ | TyFloat _ | TyBool _ | TyChar _ -> true
  | _ -> false

  -- This implementation is backend-specific
  sem _generateCDataRepresentation : CWrapperEnv -> Type -> CDataRepr

  sem ocamlToCConversionFunctionIdent : CType -> Name
  sem ocamlToCConversionFunctionIdent =
  | CTyChar _ | CTyInt _ -> _getIdentExn "Int_val"
  | CTyInt64 _ -> _getIdentExn "Long_val"
  | CTyFloat _ | CTyDouble _ -> _getIdentExn "Double_val"

  sem cToOCamlConversionFunctionIdent : CType -> Name
  sem cToOCamlConversionFunctionIdent =
  | CTyChar _ | CTyInt _ -> _getIdentExn "Val_int"
  | CTyInt64 _ -> _getIdentExn "Val_long"
  | CTyFloat _ | CTyDouble _ -> _getIdentExn "caml_copy_double"

  sem _getCReturnType : Type -> CType
  sem _getCReturnType =
  | TyRecord t ->
    if mapIsEmpty t.fields then
      CTyVoid ()
    else
      CTyVar {id = _getIdentExn "value"}
  | _ -> CTyVar {id = _getIdentExn "value"}

  -- Generates an additional wrapper function to be referenced from OCaml. This
  -- function is used when calling from bytecode (hence the name) and also when
  -- the function takes more than five parameters.
  sem generateBytecodeWrapper : AccelerateData -> CTop
  sem generateBytecodeWrapper =
  | data ->
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

  sem generateCAMLParamDeclarations : [ArgData] -> [CStmt]
  sem generateCAMLParamDeclarations =
  | args ->
    let genParamStmt : [ArgData] -> String -> CStmt = lam args. lam funStr.
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
  -- the GPU backend. As this generation depends on the GPU backend, it is only
  -- declared here.
  sem generateMarshallingCode : CWrapperEnv -> [CStmt]

  -- Generates the main function of the wrapper code. This is the function that
  -- manages the marshalling between OCaml and the target GPU language.
  sem generateWrapperFunctionCode : CWrapperEnv -> AccelerateData -> [CTop]
  sem generateWrapperFunctionCode env =
  | data ->
    let toArgData = lam x : (CopyStatus, (Name, Type)).
      match x with (status, (id, ty)) in
      let default : ArgData = defaultArgData () in
      {{{{{default with mexprIdent = id}
                   with mexprType = ty}
                   with copyStatus = status}
                   with cData = _generateCDataRepresentation env ty}
                   with gpuIdent = nameSym "gpu_tmp"} in
    let bytecodeWrapper = generateBytecodeWrapper data in
    let returnIdent = nameSym "out" in
    let returnArg = (returnIdent, data.returnType) in
    let arguments = map toArgData (zip data.paramCopyStatus data.params) in
    let env = {{{env with arguments = arguments}
                     with return = toArgData (CopyBoth (), returnArg)}
                     with functionIdent = data.identifier} in
    let camlParamStmts = generateCAMLParamDeclarations env.arguments in
    let stmts = generateMarshallingCode env in
    let value = _getIdentExn "value" in
    let stmts =
      let returnTypeIsEmptyRecord =
        match data.returnType with TyRecord t then mapIsEmpty t.fields
        else false
      in
      if returnTypeIsEmptyRecord then
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
    let withValueType = lam arg : (Name, Type).
      (CTyVar {id = value}, arg.0) in
    [ CTFun {
        ret = _getCReturnType data.returnType,
        id = data.identifier,
        params = map withValueType data.params,
        body = stmts}
    , bytecodeWrapper ]

  sem generateWrapperCodeH : CWrapperEnv -> Map Name AccelerateData
                          -> (CWrapperEnv, [CTop])
  sem generateWrapperCodeH env =
  | accelerated ->
    let entryPointWrappers =
      map (generateWrapperFunctionCode env) (mapValues accelerated) in
    (env, join entryPointWrappers)
end
