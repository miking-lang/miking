-- Compiles a subset of MExpr programs to C.
-- * Anonymous functions are not supported, except when bound to variables at
-- top-level.
-- * Top-level MExpr variables (including functions) are compiled to global C
-- data.
-- * There is no garbage collection.
-- * Any top-level code besides functions and data declarations are returned as
-- a list of C statements. Usually, these statements should be
-- put in a C `main` function or similar.
--


include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"
include "mexpr/symbolize.mc"
include "mexpr/type-check.mc"
include "mexpr/remove-ascription.mc"
include "mexpr/type-lift.mc"
include "mexpr/record.mc"
include "mexpr/builtin.mc"
include "mexpr/boot-parser.mc"

include "name.mc"
include "map.mc"
include "set.mc"

include "ast.mc"
include "pprint.mc"

-- Externals (these should be automatically parsed eventually)
include "ext/math-ext.ext-c.mc"

----------------------
-- HELPER FUNCTIONS --
----------------------

-- Check for unit type
let _isUnitTy = use RecordTypeAst in lam ty.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields
  else false

-- Unwrap type variables until something useful falls out
recursive let _unwrapType =
  use MExprAst in
  lam tyEnv: AssocSeq Name Type. lam ty: Type.
    match unwrapType ty with TyCon { ident = ident } then
      match assocSeqLookup { eq = nameEq } ident tyEnv with Some ty then
        _unwrapType tyEnv ty
      else errorSingle [infoTy ty] "TyCon not defined in environment"
    else ty
end

-- Look up the name of a type variable corresponding to a given concrete type
let _lookupTypeName = use MExprAst in
  lam tyEnv : AssocSeq Name Type. lam ty : Type.
  let eqType = lam ty1. lam ty2.
    use MExprCmp in eqi (cmpType ty1 ty2) 0
  in
  recursive let work : Option Name -> Type -> Name = lam id. lam ty.
    match ty with TyCon {ident = ident} then ident
    else match assocSeqReverseLookup {eq = eqType} ty tyEnv with Some id then
      id
    else errorSingle [infoTy ty] "Type not found in type environment"
  in
  work (None ()) ty

-- C assignment shorthand
let _assign: use CAst in CExpr -> CExpr -> CExpr = use CAst in
  lam lhs. lam rhs.
    CEBinOp { op = COAssign {}, lhs = lhs, rhs = rhs }


----------------------------------------
-- COMPILER DEFINITIONS AND EXTERNALS --
----------------------------------------

-- Collect all maps of externals. Should be done automatically at some point,
-- but for now these files must be manually included and added to this map.
let externalsMap: ExtMap = foldl1 mapUnion [
  mathExtMap
]

-- Retrieve names used for externals. Used for making sure these names are printed without modification during C code generation.
let externalNames: [Name] =
  map nameNoSym
    (mapFoldWithKey (lam acc. lam. lam v: ExtInfo. cons v.ident acc)
       [] externalsMap)

-- Collect all includes for C externals.
let externalIncludes: [String] =
  setToSeq
    (mapFoldWithKey (lam acc. lam. lam v: ExtInfo. setInsert v.header acc)
       (setEmpty cmpString) externalsMap)

-- Customizable set of includes
let cIncludes = concat [
  "<stdint.h>",
  "<stdio.h>"
] externalIncludes

-- Names used in the compiler for intrinsics
let _printf = nameSym "printf"
let _exit = nameSym "exit"
let _cartesianToLinearIndex = nameSym "cartesian_to_linear_index"
let _tensorShape = nameSym "tensor_shape"

-- C names that must be pretty printed using their exact string
let cCompilerNames: [Name] = concat [
  _printf
] externalNames

-- Various names used when defining C structs
let _constrKey = nameNoSym "constr"
let _seqKey = nameNoSym "seq"
let _seqLenKey = nameNoSym "len"
let _tensorIdKey = nameNoSym "id"
let _tensorDataKey = nameNoSym "data"
let _tensorDimsKey = nameNoSym "dims"
let _tensorRankKey = nameNoSym "rank"
let _tensorSizeKey = nameNoSym "size"


-- TODO(dlunde,2022-04-29): A bug in the MLang transformation currently
-- prevents this fragment from being put in MExprCCompileBase
type CompileCOptions = {
  -- Controls the maximum rank of tensors in the C code.
  tensorMaxRank : Int,

  -- Controls whether 32-bit integers should be used. If this is false (which
  -- is the default setting), the compiler will use 64-bit integers.
  use32BitInts : Bool,

  -- Controls whether 32-bit floating-point numbers should be used. If this
  -- is false (which is the default setting), the compiler will use 64-bit
  -- floats.
  use32BitFloats : Bool
}

lang MExprCCompileBase = MExprAst + CAst

  --------------------------
  -- COMPILER ENVIRONMENT --
  --------------------------

  sem defaultCompileCOptions =
  | _ -> {tensorMaxRank = 3, use32BitInts = false, use32BitFloats = false}

  type CompileCEnv = {

    -- C Compiler options
    options : CompileCOptions,

    -- Type names accessed through pointers
    ptrTypes: [Name],

    -- The initial type environment produced by type lifting
    typeEnv: [(Name,Type)],

    -- Map from MExpr external names to their C counterparts
    externals: Map Name ExtInfo,

    -- Accumulator for allocations in functions
    allocs: [CStmt]
  }

  -- Empty environment
  sem compileCEnvEmpty =
  | compileOptions ->
    let compileOptions : CompileCOptions = compileOptions in
    { options = compileOptions, ptrTypes = [], typeEnv = []
    , externals = mapEmpty nameCmp, allocs = [] }

  -- Compilation of constant types
  sem getCIntType =
  | env ->
    let env : CompileCEnv = env in
    let opts : CompileCOptions = env.options in
    if opts.use32BitInts then CTyInt32 () else CTyInt64 ()

  sem getCFloatType =
  | env ->
    let env : CompileCEnv = env in
    let opts : CompileCOptions = env.options in
    if opts.use32BitFloats then CTyFloat () else CTyDouble ()

  sem getCBoolType =
  | env -> CTyChar ()

  sem getCCharType =
  | env -> CTyChar ()

end

-- Generation of tensor function for computing the linear index given a
-- sequence of integers representing a cartesian index, and the dimensions of
-- the tensor.
lang MExprTensorCCompile = MExprCCompileBase
  sem usesTensorTypes : [(Name, Type)] -> Bool
  sem usesTensorTypes =
  | typeEnv ->
    let isTensorType = lam ty.
      match ty with TyTensor _ then true else false
    in
    let isSeqIntType = lam ty.
      match ty with TySeq {ty = TyInt _} then true else false
    in
    if any (lam entry. isTensorType entry.1) typeEnv then
      any (lam entry. isSeqIntType entry.1) typeEnv
    else false

  sem _genIndexErrorStmts (rank : Name) =
  | nindices ->
    let errorStr = join [
      "Accessed tensor of rank %ld using ", int2string nindices, " indices\n"] in
    [ CSExpr {expr = CEApp {
        fun = _printf,
        args = [CEString {s = errorStr}, CEVar {id = rank}]}}
    , CSRet {val = Some (CEInt {i = negi 1})} ]

  -- TODO(larshum, 2022-03-21): Lots of code duplication here. This code could
  -- probably be generated in a more reusable way.
  sem specializedCartesianToLinearDef (dims : Name) (rank : Name) (id : Name) =
  | 0 ->
    CTFun {
      ret = CTyInt64 (), id = id,
      params = [
        (CTyArray {ty = CTyInt64 (), size = Some (CEInt {i = 3})}, dims),
        (CTyInt64 (), rank)],
      body = [CSRet {val = Some (CEInt {i = 0})}]}
  | nindices ->
    let indexIds = create nindices (lam. nameSym "i") in
    let indexParams = map (lam id : Name. (CTyInt64 (), id)) indexIds in
    let params =
      concat
        [ (CTyArray {ty = CTyInt64 (), size = Some (CEInt {i = 3})}, dims)
        , (CTyInt64 (), rank)]
        indexParams in
    let rankEqExpr = lam n : Int.
      CEBinOp {
        op = COEq (),
        lhs = CEVar {id = rank},
        rhs = CEInt {i = n}} in
    let dimsExpr = lam n : Int.
      CEBinOp {
        op = COSubScript (),
        lhs = CEVar {id = dims},
        rhs = CEInt {i = n}} in
    let mulExpr = lam lhs : CExpr. lam rhs : CExpr.
      CEBinOp {op = COMul (), lhs = lhs, rhs = rhs} in
    let addExpr = lam lhs : CExpr. lam rhs : CExpr.
      CEBinOp {op = COAdd (), lhs = lhs, rhs = rhs} in
    let retStmt = lam expr : CExpr. CSRet {val = Some expr} in
    let stmt =
      match nindices with 1 then
        let i0 = CEVar {id = get indexIds 0} in
        CSIf {
          cond = rankEqExpr 3,
          thn = [retStmt (mulExpr (mulExpr (dimsExpr 2) (dimsExpr 1)) i0)],
          els = [
            CSIf {
              cond = rankEqExpr 2,
              thn = [retStmt (mulExpr (dimsExpr 1) i0)],
              els = [retStmt i0]}]}
      else match nindices with 2 then
        let i0 = CEVar {id = get indexIds 0} in
        let i1 = CEVar {id = get indexIds 1} in
        CSIf {
          cond = rankEqExpr 3,
          thn = [
            retStmt
              (addExpr
                (mulExpr (mulExpr (dimsExpr 2) (dimsExpr 1)) i0)
                (mulExpr (dimsExpr 2) i1))],
          els = [
            CSIf {
              cond = rankEqExpr 2,
              thn = [
                retStmt
                  (addExpr (mulExpr (dimsExpr 1) i0) i1)],
              els = _genIndexErrorStmts rank nindices}]}
      else match nindices with 3 then
        let i0 = CEVar {id = get indexIds 0} in
        let i1 = CEVar {id = get indexIds 1} in
        let i2 = CEVar {id = get indexIds 2} in
        CSIf {
          cond = rankEqExpr 3,
          thn = [
            retStmt
              (addExpr
                (addExpr
                  (mulExpr (mulExpr (dimsExpr 2) (dimsExpr 1)) i0)
                  (mulExpr (dimsExpr 2) i1))
                i2)],
          els = _genIndexErrorStmts rank nindices}
      else
        error
          (join ["Cannot generate specialized index for ", int2string nindices,
                 " indices"]) in
    CTFun {ret = CTyInt64 (), id = id, params = params, body = [stmt]}

  sem cartesianToLinearIndexDef =
  | env ->
    let env : CompileCEnv = env in
    let intSeqType = TySeq {ty = TyInt {info = NoInfo ()}, info = NoInfo ()} in
    let cidxName = _lookupTypeName env.typeEnv intSeqType in
    let cidxType = CTyVar {id = cidxName} in
    let dims = nameSym "dims" in
    let rank = nameSym "rank" in
    let cidx = nameSym "cartesian_idx" in

    -- NOTE(larshum, 2022-03-21): For efficiency reasons, we generate
    -- specialized functions for a given number of index arguments. Currently,
    -- as the maximum rank is set to 3, we generate functions for 0, 1, 2, and
    -- 3 indices.
    let nspecialized = 4 in
    let specializedIds =
      create 4
        (lam i.
          nameSym
            (concat
              (nameGetStr _cartesianToLinearIndex)
              (int2string i))) in
    let specializedTops =
      create 4
        (lam i.
          let id = get specializedIds i in
          specializedCartesianToLinearDef dims rank id i) in

    let params = [
      (CTyArray {ty = CTyInt64 (), size = Some (CEInt {i = 3})}, dims),
      (CTyInt64 (), rank), (cidxType, cidx)] in
    let cidxElemExpr = lam n.
      CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = CEVar {id = cidx}, id = _seqKey},
        rhs = CEInt {i = n}} in
    let cidxLenExpr = CEMember {lhs = CEVar {id = cidx}, id = _seqLenKey} in
    let equalIntExpr = lam n : Int.
      CEBinOp {op = COEq (), lhs = cidxLenExpr, rhs = CEInt {i = n}} in
    let callSpecializedCToL = lam n : Int.
      let args =
        concat
          [CEVar {id = dims}, CEVar {id = rank}]
          (create n (lam i. cidxElemExpr i)) in
      CEApp {fun = get specializedIds n, args = args} in
    let stmts = [
      CSIf {
        cond = equalIntExpr 1,
        thn = [CSRet {val = Some (callSpecializedCToL 1)}],
        els = [
          CSIf {
            cond = equalIntExpr 2,
            thn = [CSRet {val = Some (callSpecializedCToL 2)}],
            els = [
              CSIf {
                cond = equalIntExpr 3,
                thn = [CSRet {val = Some (callSpecializedCToL 3)}],
                els = [CSRet {val = Some (callSpecializedCToL 0)}]}]}]}] in
    snoc
      specializedTops
      (CTFun {
        ret = CTyInt64 (), id = _cartesianToLinearIndex,
        params = params, body = stmts})

  sem tensorShapeDef =
  | env ->
    let env : CompileCEnv = env in
    let intType = getCIntType env in
    let mexprSeqType = TySeq {ty = TyInt {info = NoInfo ()}, info = NoInfo ()} in
    let seqName = _lookupTypeName env.typeEnv mexprSeqType in
    let seqType = CTyVar {id = seqName} in
    let dimsType = CTyArray {ty = CTyInt64 (), size = Some (CEInt {i = 3})} in
    let dimsId = nameSym "dims" in
    let rankId = nameSym "rank" in
    let seqId = nameSym "s" in
    let params = [(dimsType, dimsId), (CTyInt64 (), rankId)] in
    let stmts = [
      CSDef {ty = seqType, id = Some seqId, init = None ()},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = seqId}, id = _seqKey},
        rhs = CEVar {id = dimsId}}},
      CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = CEMember {lhs = CEVar {id = seqId}, id = _seqLenKey},
        rhs = CEVar {id = rankId}}},
      CSRet {val = Some (CEVar {id = seqId})}
    ] in
    CTFun {ret = seqType, id = _tensorShape, params = params, body = stmts}

  -- Computes the linear index given expressions representing the tensor and
  -- the sequence containing the cartesian coordinates.
  sem tensorComputeLinearIndex (tensor : CExpr) =
  | cartesianIndex ->
    let tensorDims = CEMember {lhs = tensor, id = _tensorDimsKey} in
    let tensorRank = CEMember {lhs = tensor, id = _tensorRankKey} in
    CEApp {
      fun = _cartesianToLinearIndex,
      args = [tensorDims, tensorRank, cartesianIndex]}

  sem tensorShapeCall =
  | tensor /- CExpr -/ ->
    let tensorDims = CEMember {lhs = tensor, id = _tensorDimsKey} in
    let tensorRank = CEMember {lhs = tensor, id = _tensorRankKey} in
    CEApp {fun = _tensorShape, args = [tensorDims, tensorRank]}
end

----------------------------------
-- MEXPR -> C COMPILER FRAGMENT --
----------------------------------

lang MExprCCompile = MExprCCompileBase + MExprTensorCCompile + RecordTypeUtils

  -- Used in compileStmt and compileStmts for deciding what action to take in
  -- tail position
  syn Result =
  | RIdent Name
  | RReturn ()
  | RNone ()

  -- Function that is called when allocation of data is needed. Must be implemented by a concrete C compiler.
  sem alloc (name: Name) =
  -- Intentionally left blank

  -- Function that is called to free allocated data. Should be implemented by a concrete C compiler. NOTE(dlunde,2021-09-30): Currently unused
  sem free =
  -- Intentionally left blank

  -- Entry point
  sem compile (typeEnv: [(Name,Type)]) (compileOptions : CompileCOptions) =
  | prog ->

    -- Find all type names which translates to C structs
    let ptrTypes: [Name] = foldr (lam t: (Name,Type). lam acc.
      if isPtrType acc t.1 then snoc acc t.0 else acc
    ) [] typeEnv in

    -- Construct a map from MCore external names to C names
    let externals: Map Name ExtInfo = collectExternals (mapEmpty nameCmp) prog in

    -- Set up initial environment
    let env = {{{ let e : CompileCEnv = compileCEnvEmpty compileOptions in e
      with ptrTypes = ptrTypes }
      with typeEnv = typeEnv }
      with externals = externals }
    in

    -- Compute type declarations
    let decls: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyDecls acc t.0 t.1
    ) [] typeEnv in

    -- Compute type definitions
    let defs: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyDefs env acc t.0 t.1
    ) [] typeEnv in

    -- Compute type definitions that must occur after the above definitions
    let postDefs: [CTop] = foldl (lam acc. lam t: (Name,Type).
      genTyPostDefs env acc t.0 t.1
    ) [] typeEnv in

    -- Run compiler
    match compileTops env [] [] prog with (tops, inits) in

    -- Generate functions for computing linear index for tensors, if the
    -- provided AST uses tensors and sequences of integers.
    let tops =
      if usesTensorTypes typeEnv then
        concat (snoc (cartesianToLinearIndexDef env) (tensorShapeDef env)) tops
      else tops
    in

    -- Compute return type
    let retTy: CType = compileType env (tyTm prog) in

    -- Return final compiler environment, types, top-level definitions,
    -- initialization code (e.g., to put in a main function), and the return
    -- type
    (env, join [decls, defs, postDefs], tops, inits, retTy)

  -----------------------
  -- COLLECT EXTERNALS --
  -----------------------

  sem collectExternals (acc: Map Name ExtInfo) =
  | TmExt t ->
    let str = nameGetStr t.ident in
    match mapLookup str externalsMap with Some e then
      let e: ExtInfo = e in -- TODO(dlunde,2021-10-25): Remove with more complete type system?
      let acc = mapInsert t.ident e acc in
      sfold_Expr_Expr collectExternals acc t.inexpr
    else errorSingle [t.info] "Unsupported external"
  | expr -> sfold_Expr_Expr collectExternals acc expr

  -------------
  -- TYPES --
  -------------

  sem isPtrType (acc: [Name]) =
  -- Variants are always accessed through pointer (could potentially be
  -- optimized in the same way as records)
  | TyVariant _ -> true
  -- Sequences and tensors are handled specially, and are not accessed directly
  -- through pointers
  | TySeq _ -> false
  | TyTensor _ -> false
  -- Records are only accessed through pointer if they contain pointer types.
  -- This allows for returning small records from functions, but may be
  -- expensive for very large records if it's not handled by the underlying
  -- C/C++ compiler.
  | TyRecord { fields = fields } ->
    let r = mapFoldlOption (lam. lam. lam ty.
      if isPtrType acc ty then None () else Some ()
    ) () fields in
    match r with None _ then true else false
  | TyCon { ident = ident } -> any (nameEq ident) acc
  | _ -> false

  -- Generate declarations for all variant types (required because of recursion).
  sem genTyDecls (acc: [CTop]) (name: Name) =
  | TyVariant _ ->
    let decl = CTTyDef {
      ty = CTyStruct { id = Some name, mem = None () },
      id = name
    } in
    cons decl acc
  | _ -> acc

  -- Generate type definitions.
  sem genTyDefs (env: CompileCEnv) (acc: [CTop]) (name: Name) =
  | TyVariant _ -> acc -- These are handled by genTyPostDefs instead
  | (TyRecord { fields = fields }) & ty ->
    let labels = tyRecordOrderedLabels ty in
    let fieldsLs: [(CType,Option Name)] =
      foldl (lam acc. lam k.
        let ty = mapFindExn k fields in
        let ty = compileType env ty in
        snoc acc (ty, Some (nameNoSym (sidToString k)))) [] labels in
    let def = CTTyDef {
      ty = CTyStruct { id = Some name, mem = Some fieldsLs },
      id = name
    } in
    cons def acc
  | TySeq { ty = ty } ->
    let ty = compileType env ty in
    let fields = [
      (CTyPtr { ty = ty }, Some _seqKey),
      (getCIntType env, Some _seqLenKey)
    ] in
    let def = CTTyDef {
      ty = CTyStruct { id = Some name, mem = Some fields },
      id = name
    } in
    cons def acc
  | TyTensor { ty = ty } ->
    let ty = compileType env ty in
    let dimsType = TySeq {ty = TyInt {info = NoInfo ()}, info = NoInfo ()} in
    let maxRank = env.options.tensorMaxRank in
    let fields = [
      (CTyInt64 (), Some _tensorIdKey),
      (CTyPtr { ty = ty }, Some _tensorDataKey),
      (CTyArray { ty = CTyInt64 (), size = Some (CEInt {i = maxRank}) }, Some _tensorDimsKey),
      (CTyInt64 (), Some _tensorRankKey),
      (CTyInt64 (), Some _tensorSizeKey)
    ] in
    let def = CTTyDef {
      ty = CTyStruct { id = Some name, mem = Some fields },
      id = name
    } in
    cons def acc
  | ty ->
    let def = CTTyDef { ty = compileType env ty, id = name } in
    cons def acc

  -- Generate variant definitions.
  sem genTyPostDefs
    (env: CompileCEnv) (acc: [CTop]) (name: Name) =
  | TyVariant { constrs = constrs } ->
      let constrLs: [(Name, CType)] =
        mapFoldWithKey (lam acc. lam name. lam ty.
          let ty = compileType env ty in
            snoc acc (name, ty)) [] constrs in
      let nameEnum = nameSym "constrs" in
      let enum = CTDef {
        ty = CTyEnum {
          id = Some nameEnum,
          mem = Some (map (lam t: (Name, CType). t.0) constrLs)
        },
        id = None (), init = None ()
      } in
      let def = CTTyDef {
        ty = CTyStruct {
          id = Some name,
          mem = Some [
            (CTyEnum { id = Some nameEnum, mem = None () }, Some _constrKey),
            (CTyUnion {
               id = None (),
               mem = Some (map
                 (lam t: (Name,CType). (t.1, Some t.0)) constrLs)
             }, None ())
          ] },
        id = name
      }
      in
      concat [enum,def] acc
  | _ -> acc

  sem compileType (env: CompileCEnv) =
  | TyInt _ -> getCIntType env
  | TyFloat _ -> getCFloatType env
  | TyBool _ -> getCBoolType env
  | TyChar _ -> getCCharType env

  | TyCon { ident = ident } & ty ->
    -- Pointer types
    if any (nameEq ident) env.ptrTypes then
      CTyPtr { ty = CTyVar { id = ident } }
    -- Non-pointer types
    else CTyVar { id = ident }

  | TyUnknown _ & ty -> errorSingle [infoTy ty] "Unknown type in compileType"

  | TyRecord { fields = fields } & ty ->
    if mapIsEmpty fields then CTyVoid {}
    else
      errorSingle [infoTy ty]
        "TyRecord should not occur in compileType. Did you run type lift?"

  | TyVariant _ & ty ->
    errorSingle [infoTy ty]
      "TyVariant should not occur in compileType. Did you run type lift?"

  | TySeq { ty = TyChar _ } -> CTyPtr { ty = CTyChar {} }

  | TySeq _ & ty ->
    errorSingle [infoTy ty]
      "TySeq should not occur in compileType. Did you run type lift?"

  | TyTensor _ & ty ->
    errorSingle [infoTy ty]
      "TyTensor should not occur in compileType. Did you run type lift?"

  | TyApp _ & ty -> errorSingle [infoTy ty] "Type not currently supported"
  | TyArrow _ & ty ->
    errorSingle [infoTy ty] "TyArrow currently not supported"
    -- recursive let params = lam acc. lam ty.
    --   match ty with TyArrow { from = from, to = to } then
    --     params (snoc acc from) to
    --   else (acc, ty)
    -- in
    -- match params [] ty with (params, ret) then
    --   match mapAccumL compileType params with (env, params) then
    --     match compileType ret with (env, ret) then
    --       (env, CTyFun { ret = ret, params = params })
    --     else never
    --   else never
    -- else never

  | TyAlias t -> compileType env t.display

  | ty -> errorSingle [infoTy ty] "Unsupported type in compileType"


  -----------------------
  -- COMPILE FUNCTIONS --
  -----------------------

  -- Translate a sequence of lambdas to a C function. Takes an explicit type as
  -- argument, because the lambdas do not explicitly give the return type,
  -- which is required in C.
  sem compileFun (env: CompileCEnv) (id: Name) (ty: Type) =
  | TmLam _ & fun ->
    recursive let detachParams: [Name] -> Expr -> ([Name], Expr) =
      lam acc. lam rest.
        match rest with
        TmLam { ty = ty, ident = ident, body = rest } then
          match ty with TyArrow { from = fromTy } then
            if _isUnitTy fromTy then detachParams acc rest
            else detachParams (snoc acc ident) rest
          else
            errorSingle [infoTy ty] "Incorrect type in compileFun"
        else (acc, rest)
    in
    recursive let funTypes: [Type] -> Type -> ([Type], Type) =
      lam acc. lam rest.
        match rest with TyArrow { from = from, to = rest } then
          if _isUnitTy from then funTypes acc rest
          else funTypes (snoc acc from) rest
        else (acc, rest)
    in
    match detachParams [] fun with (params, body) then
      match funTypes [] ty with (paramTypes, retType) then
        if neqi (length params) (length paramTypes) then
          errorSingle [infoTy ty] "Number of parameters in compileFun does not match."
        else
          match map (compileType env) paramTypes with paramTypes then
            let params = zipWith (lam t. lam id. (t, id)) paramTypes params in
            match (compileType env) retType with ret then
              let benv = { env with allocs = [] } in
              match compileStmts benv (RReturn ()) [] body with (benv, body) then
                let benv: CompileCEnv = benv in
                let body = concat benv.allocs body in
                -- Restore previous allocs
                let env = { benv with allocs = env.allocs } in
                (env, CTFun { ret = ret, id = id, params = params, body = body })
              else never
            else never
          else never
      else never
    else never

  | t -> errorSingle [infoTm t] "Non-lambda supplied to compileFun"


  -----------------
  -- ALLOCATIONS --
  -----------------

  -- Compiles allocation/definition and initialization of composite data types.
  -- The name of the allocation can either be given or generated.
  sem compileAlloc (env: CompileCEnv) (name: Option Name) =

  | TmConApp { ident = constrIdent, body = body, ty = ty } & t ->
    let n = match name with Some name then name else nameSym "alloc" in
    let def = alloc n (compileType env ty) in
    let init = [
      -- Set constructor tag
      CSExpr {
        expr = _assign (CEArrow { lhs = CEVar { id = n }, id = _constrKey })
          (CEVar { id = constrIdent })
      },
      -- Set data
      CSExpr {
        expr = _assign (CEArrow { lhs = CEVar { id = n }, id = constrIdent })
          (compileExpr env body)
      }
    ] in
    (env, def, init, n)

  | TmRecord _ & t ->
    errorSingle [infoTm t]
      "Unhandled case for TmRecord in compileAlloc (should be impossible)."
  | TmRecord { ty = TyRecord _, bindings = bindings } & t ->
    -- If the type is TyRecord, it follows from type lifting that this must be
    -- an empty record.
    -- TODO(dlunde,2021-10-07): Handle this how?
    errorSingle [infoTm t] "Empty bindings in TmRecord in compileAlloc"
  | TmRecord { ty = TyCon { ident = ident } & ty, bindings = bindings } & t ->
    let orderedLabels = recordOrderedLabels (mapKeys bindings) in
    let n = match name with Some name then name else nameSym "alloc" in
    let cTy = compileType env ty in
    if any (nameEq ident) env.ptrTypes then
      let def = alloc n cTy in
      let init = map (lam sid.
        let expr = mapFindExn sid bindings in
        CSExpr {
          expr = _assign
            (CEArrow {
              lhs = CEVar { id = n }, id = nameNoSym (sidToString sid)
            })
            (compileExpr env expr)
        }
      ) orderedLabels in
      (env, def, init, n)
    else
      let def = [{ ty = cTy, id = Some n, init = None ()}] in
      let init = map (lam sid.
        let expr = mapFindExn sid bindings in
        CSExpr {
          expr = _assign
            (CEMember {
              lhs = CEVar { id = n }, id = nameNoSym (sidToString sid)
            })
            (compileExpr env expr)
        }
      ) orderedLabels in
      (env, def, init, n)

  | TmSeq {tms = tms, ty = ty} & t ->
    let uTy = _unwrapType (env.typeEnv) ty in
    let n = match name with Some name then name else nameSym "alloc" in
    let len = length tms in

    -- Special handling of strings
    match uTy with TySeq { ty = TyChar _ & iTy } then
      let toChar = lam expr.
        match expr with TmConst { val = CChar { val = val } } then Some val
        else None ()
      in
      match optionMapM toChar tms with Some str then
        let str = CEString { s = str } in
        let def = [
          {
            ty = compileType env ty,
            id = Some n,
            init = Some (CIExpr { expr = str })
          }] in
        (env, def, [], n)
      else
        errorSingle [infoTm t] "Non-literal strings currently unsupported."
        -- let iTy = CTyArray {
        --   ty = compileType env iTy,
        --   size = Some (CEInt { i = addi 1 len })
        -- } in

    -- General sequences
    else match uTy with TySeq { ty = iTy } then
      -- Define the array
      let iTy = CTyArray {
        ty = compileType env iTy,
        size = Some (CEInt { i = len })
      } in
      let arrayName = nameSym "seqAlloc" in
      let def = alloc arrayName iTy in
      -- Initialize the array
      let init = mapi (lam i. lam t.
        CSExpr {
          expr = _assign
            (CEBinOp {
              op = COSubScript {},
              lhs = CEVar { id = arrayName },
              rhs = CEInt { i = i }
            })
            (compileExpr env t)
        }
      ) tms in
      -- Define and initialize the sequence struct
      let def = snoc def
        { ty = compileType env ty, id = Some n, init = None () } in
      let initSeq = [
        -- Set ptr
        CSExpr {
          expr = _assign (CEMember { lhs = CEVar { id = n }, id = _seqKey })
            (CEVar { id = arrayName })
        },
        -- Set len
        CSExpr {
          expr = _assign (CEMember { lhs = CEVar { id = n }, id = _seqLenKey })
            (CEInt { i = len })
        }
      ] in
      (env, def, concat init initSeq, n)


    else errorSingle [infoTm t] "TmSeq type inconsistency"


  ---------------
  -- TOP-LEVEL --
  ---------------

  sem compileTops (env: CompileCEnv) (accTop: [CTop]) (accInit: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->

    -- Functions
    match body with TmLam _ then
      match compileFun env ident tyBody body with (env, fun) then
        compileTops env (snoc accTop fun) accInit inexpr
      else never

    -- Optimize direct allocations
    else match body with TmConApp _ | TmRecord _ | TmSeq _ then
      match compileAlloc env (Some ident) body with (env, def, init, n) then
        let accTop = concat accTop (map (lam d. CTDef d) def) in
        let accInit = concat accInit init in
        compileTops env accTop accInit inexpr
      else never

    -- Other lets
    else
      let iu = _isUnitTy tyBody in
      let def =
        if iu then []
        else
          let ty = compileType env tyBody in
          [CTDef { ty = ty, id = Some ident, init = None () }]
      in
      let lres = if iu then RNone () else RIdent ident in
      match compileStmt env lres body with (env, stmts) then
        let accTop = concat accTop def in
        let accInit = concat accInit stmts in
        compileTops env accTop accInit inexpr
      else never

  | TmRecLets { bindings = bindings, inexpr = inexpr } ->
    let f = lam env. lam binding: RecLetBinding.
      match binding with { ident = ident, tyBody = tyBody, body = body } then
        compileFun env ident tyBody body
      else never
    in
    let g = lam fun.
      match fun with CTFun { ret = ret, id = id, params = params, body = body }
      then
        let params = map (lam t: (CType,Name). t.0) params in
        CTDef { ty = CTyFun { ret = ret, params = params }, id = Some id,
                init = None () }
      else never
    in
    match mapAccumL f env bindings with (env, funs) then
      let decls = if leqi (length funs) 1 then [] else map g funs in
      compileTops env (join [accTop, decls, funs]) accInit inexpr
    else never

  -- Ignore externals (handled elsewhere)
  | TmExt { inexpr = inexpr } -> compileTops env accTop accInit inexpr

  -- Set up initialization code (for use, e.g., in a main function)
  | rest ->
    match compileStmts env (RReturn ()) accInit rest with (env, accInit) then
      let env: CompileCEnv = env in
      (accTop, concat env.allocs accInit)
    else never

  ----------------------
  -- COMPILE PATTERNS --
  ----------------------

  sem compilePat (env: CompileCEnv) (conds: [CExpr]) (defs: [CStmt])
    (target: CExpr) (ty: Type) =

  | PatNamed { ident = PName ident } ->
    let def = CSDef {
      ty = compileType env ty,
      id = Some ident,
      init = Some (CIExpr { expr = target })
    } in
    ( conds, snoc defs def )

  | PatNamed { ident = PWildcard _ } -> (conds, defs)

  | PatBool { val = val } ->
    ( snoc conds (CEBinOp {
        op = COEq {},
        lhs = target,
        rhs = let val = match val with true then 1 else 0 in CEInt { i = val }
      }),
      defs )

  | PatRecord { bindings = bindings } & pat ->
    match env with { typeEnv = typeEnv } then
      let f = lam acc. lam sid. lam subpat.
        match acc with (conds, defs) then
          match _unwrapType typeEnv ty with TyRecord { fields = fields } then
            match mapLookup sid fields with Some fTy then
              let label = sidToString sid in
              let expr = match unwrapType ty with TyCon { ident = ident } then
                  if any (nameEq ident) env.ptrTypes then
                    CEArrow { lhs = target, id = nameNoSym label }
                  else
                    CEMember { lhs = target, id = nameNoSym label }
                else errorSingle [infoPat pat] "Impossible scenario"
              in
              compilePat env conds defs expr fTy subpat
            else errorSingle [infoPat pat] "Label does not match between PatRecord and TyRecord"
          else errorSingle [infoPat pat] "Type not TyCon for PatRecord in compilePat"
        else never
      in
      mapFoldWithKey f (conds, defs) bindings
    else never

  | PatCon { ident = ident, subpat = subpat } & pat ->
    match env with { typeEnv = typeEnv } then
      match _unwrapType typeEnv ty with TyVariant { constrs = constrs } then
        match mapLookup ident constrs with Some ty then
          let cond = CEBinOp {
            op = COEq {},
            lhs = CEArrow { lhs = target, id = _constrKey },
            rhs = CEVar { id = ident }
          } in
          let expr = CEArrow { lhs = target, id = ident } in
          compilePat env (snoc conds cond)
            defs expr ty subpat
        else errorSingle [infoPat pat] "Invalid constructor in compilePat"
      else errorSingle [infoPat pat] "Not a TyVariant for PatCon in compilePat"
    else never
  | pat -> errorSingle [infoPat pat] "Pattern not supported"


  ----------------
  -- STATEMENTS --
  ----------------

  -- Compile a single C statement, and take action according to res.
  sem compileStmt (env: CompileCEnv) (res: Result) =

  -- TmMatch: Compile to if-statement
  | TmMatch { target = target, pat = pat, thn = thn, els = els } & t ->

    let ctarget = compileExpr env target in

    -- Compile branches
    match compileStmts env res [] thn with (env, thn) then
      match compileStmts env res [] els with (env, els) then

        -- Generate conditions corresponding to pat, and add pattern bindings
        -- to start of thn
        match compilePat env [] [] ctarget (tyTm target) pat
        with (conds, defs) then

          let thn = concat defs thn in

          let stmts =
            if null conds then thn
            else
              -- Compute joint condition
              let cond = foldr1 (lam cond. lam acc.
                  CEBinOp { op = COAnd {}, lhs = cond, rhs = acc }
                ) conds in
              [CSIf { cond = cond, thn = thn, els = els }]
          in

          (env, stmts)

        else never
      else never
    else never

  | TmSeq { tms = tms } & t ->
    match res with RIdent id then
      match compileAlloc env (None ()) t with (env, def, init, n) then
        let env: CompileCEnv = env in
        let def = map (lam d. CSDef d) def in
        let env = { env with allocs = concat def env.allocs } in
        (env, join [
          init,
          [CSExpr { expr = _assign (CEVar { id = id }) (CEVar { id = n }) }]
        ])
      else never
    else match res with RReturn _ then
      errorSingle [infoTm t] "Returning TmSeq is not allowed"
    else
      errorSingle [infoTm t] "Type error, should have been caught previously"

  -- TODO(dlunde,2021-10-07): Lots of code duplication here ...
  | TmConApp { ident = constrIdent, body = body, ty = ty } & t ->
    match res with RIdent id then
      match compileAlloc env (None ()) t with (env, def, init, n) then
        let def = map (lam d. CSDef d) def in
        let env: CompileCEnv = env in
        let env = { env with allocs = concat def env.allocs } in
        (env, join [
          init,
          [CSExpr { expr = _assign (CEVar { id = id }) (CEVar { id = n }) }]
        ])
      else never
    else match res with RReturn _ then
      errorSingle [infoTm t] "Returning TmConApp is not allowed"
    else
      errorSingle [infoTm t] "Type error, should have been caught previously"

  -- TODO(dlunde,2021-10-07): ... and here
  | TmRecord { ty = ty, bindings = bindings } & t ->
    if mapIsEmpty bindings then
      match res with RNone _ | RReturn _ then (env, [CSNop {}])
      else errorSingle [infoTm t] "Binding of unit type is not allowed"
    else
      match res with RIdent id then
        match compileAlloc env (None ()) t with (env, def, init, n) in
        let env: CompileCEnv = env in
        let def = map (lam d. CSDef d) def in
        let env = { env with allocs = concat def env.allocs } in
        (env, join [
          init,
          [CSExpr { expr = _assign (CEVar { id = id }) (CEVar { id = n })}]
        ])
      else match res with RReturn _ then
        if isPtrType env.ptrTypes ty then
          errorSingle [infoTm t] "Returning TmRecord containing pointers is not allowed"
        else
          match compileAlloc env (None ()) t with (env, def, init, n) in
          let env : CompileCEnv = env in
          let def = map (lam d. CSDef d) def in
          let env = {env with allocs = concat def env.allocs} in
          (env, join [
            init,
            [CSRet {val = Some (CEVar {id = n})}]])
      else
        errorSingle [infoTm t] "Type error, should have been caught previously"

  | TmRecordUpdate _ & t -> errorSingle [infoTm t] "TODO: TmRecordUpdate"

  -- Declare variable and call `compileExpr` on body.
  | expr ->

    -- TODO(dlunde,2021-10-07) Throw error on types that cannot be returned,
    -- etc.

    match res with RReturn _ then
      if _isUnitTy (tyTm expr) then
        match expr with TmVar _ then (env, [])
        else (env, [CSExpr { expr = compileExpr env expr }])
      else (env, [CSRet { val = Some (compileExpr env expr) }])

    else match res with RNone _ then
      if _isUnitTy (tyTm expr) then
        match expr with TmVar _ then (env, [])
        else (env, [CSExpr { expr = compileExpr env expr }])
      else errorSingle [infoTm expr]
        "Type error, should have been caught previously"

    else match res with RIdent id then
      (env, [CSExpr {
        expr = _assign (CEVar { id = id }) (compileExpr env expr)
      }])

    else never


  sem compileStmts (env: CompileCEnv) (res: Result) (acc: [CStmt]) =

  | TmLet { ident = ident, tyBody = tyBody, body = body, inexpr = inexpr } ->

    -- Optimize direct allocations
    match body with TmConApp _ | TmRecord _ | TmSeq _ then
      match compileAlloc env (Some ident) body with (env, def, init, n) then
        let def = map (lam d. CSDef d) def in
        let env: CompileCEnv = env in
        let env = { env with allocs = concat def env.allocs } in
        let acc = join [ acc, init ] in
        compileStmts env res acc inexpr
      else never

    else
      let iu = _isUnitTy tyBody in
      let def =
        if iu then []
        else
          let ty = compileType env tyBody in
          [CSDef { ty = ty, id = Some ident, init = None () }]
      in
      let lres = if iu then RNone () else RIdent ident in
      match compileStmt env lres body with (env, stmts) then
        let acc = join [acc, def, stmts] in
        compileStmts env res acc inexpr
      else never

  | stmt ->
    match compileStmt env res stmt with (env, stmts) then
      (env, join [acc, stmts])
    else never

  | TmNever _ -> (env, snoc acc (CSNop {}))

  -- Ignore externals (handled elsewhere)
  | TmExt { inexpr = inexpr } -> compileStmts env res acc inexpr


  -----------------
  -- EXPRESSIONS --
  -----------------

  -- Only a subset of constants can be compiled
  sem compileOp (env : CompileCEnv) (info : Info) (args: [CExpr]) =

  -- Binary operators
  | CAddi _
  | CAddf _ -> CEBinOp { op = COAdd {}, lhs = head args, rhs = last args }
  | CSubi _
  | CSubf _ -> CEBinOp { op = COSub {}, lhs = head args, rhs = last args }
  | CMuli _
  | CMulf _ -> CEBinOp { op = COMul {}, lhs = head args, rhs = last args }
  | CDivi _
  | CDivf _ -> CEBinOp { op = CODiv {}, lhs = head args, rhs = last args }
  | CModi _ -> CEBinOp { op = COMod {}, lhs = head args, rhs = last args }
  | CEqi _
  | CEqf _  -> CEBinOp { op = COEq {},  lhs = head args, rhs = last args }
  | CLti _
  | CLtf _  -> CEBinOp { op = COLt {},  lhs = head args, rhs = last args }
  | CGti _
  | CGtf _  -> CEBinOp { op = COGt {},  lhs = head args, rhs = last args }
  | CLeqi _
  | CLeqf _ -> CEBinOp { op = COLe {},  lhs = head args, rhs = last args }
  | CGeqi _
  | CGeqf _ -> CEBinOp { op = COGe {},  lhs = head args, rhs = last args }
  | CNeqi _
  | CNeqf _ -> CEBinOp { op = CONeq {}, lhs = head args, rhs = last args }

  -- Unary operators
  | CNegf _
  | CNegi _ -> CEUnOp { op = CONeg {}, arg = head args }

  -- Not directly mapped to C operators
  | CPrint _ ->
    CEApp { fun = _printf, args = [CEString { s = "%s" }, head args] }
  | CDPrint _ ->
    -- TODO(larshum, 2022-03-29): Properly implement dprint support.
    CEApp { fun = _printf, args = [CEString { s = "" }] }
  | CInt2float _ -> CECast { ty = getCFloatType env, rhs = head args }
  | CFloorfi _ -> CECast { ty = getCIntType env, rhs = head args }

  -- List operators
  | CGet _ ->
    let lhs = CEMember { lhs = head args, id = _seqKey } in
    CEBinOp { op = COSubScript {}, lhs = lhs, rhs = last args }
  | CLength _ -> CEMember { lhs = head args, id = _seqLenKey }

  -- Tensor operators
  | CTensorGetExn _ ->
    let idx = tensorComputeLinearIndex (head args) (last args) in
    let data = CEMember {lhs = head args, id = _tensorDataKey} in
    CEBinOp {op = COSubScript {}, lhs = data, rhs = idx}
  | CTensorSetExn _ ->
    let idx = tensorComputeLinearIndex (head args) (get args 1) in
    let data = CEMember {lhs = head args, id = _tensorDataKey} in
    CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {op = COSubScript {}, lhs = data, rhs = idx},
      rhs = get args 2
    }
  | CTensorLinearGetExn _ ->
    let data = CEMember {lhs = head args, id = _tensorDataKey} in
    CEBinOp {op = COSubScript {}, lhs = data, rhs = last args}
  | CTensorLinearSetExn _ ->
    let data = CEMember {lhs = head args, id = _tensorDataKey} in
    CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {op = COSubScript {}, lhs = data, rhs = get args 1},
      rhs = get args 2
    }
  | CTensorRank _ -> CEMember {lhs = head args, id = _tensorRankKey}
  | CTensorShape _ -> tensorShapeCall (head args)

  -- NOTE(larshum, 2022-03-29): To ensure this construct can be used in GPU
  -- code, we do not use 'exit' as that is only available from CPU code.
  | CError _ -> CEApp {fun = _printf, args = [CEString {s = "%s\n"}, head args]}

  | c -> errorSingle [info] "Unsupported intrinsic in compileOp"


  sem compileExpr (env: CompileCEnv) =

  | TmVar { ty = ty, ident = ident } & t->
    if _isUnitTy ty then
      errorSingle [infoTm t] "Unit type var in compileExpr"
    else match mapLookup ident env.externals with Some ext then
      let ext : ExtInfo = ext in
      CEVar { id = nameNoSym ext.ident }
    else CEVar { id = ident }

  | TmApp _ & app ->
    recursive let rec: [Expr] -> Expr -> (Expr, [Expr]) = lam acc. lam t.
      match t with TmApp { lhs = lhs, rhs = rhs } then
        if _isUnitTy (tyTm rhs) then rec acc lhs
        else rec (cons rhs acc) lhs
      else (t, acc)
    in
    match rec [] app with (fun, args) then
      -- Function calls
      match fun with TmVar { ident = ident } then
        let ident =
          match mapLookup ident env.externals with Some ext then
            let ext : ExtInfo = ext in
            nameNoSym ext.ident
          else ident
        in
        CEApp { fun = ident, args = map (compileExpr env) args }

      -- Intrinsics
      else match fun with TmConst { val = val } then
        let args = map (compileExpr env) args in
        compileOp env (infoTm fun) args val

      else errorSingle [infoTm app] "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | (TmLam _) & t -> errorSingle [infoTm t] "Anonymous function in compileExpr."

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } & t ->
    if mapIsEmpty bindings then CEInt { i = 0 }
    else errorSingle [infoTm t] "ERROR: Records cannot be handled in compileExpr."

  -- Should not occur after ANF and type lifting.
  | (TmRecordUpdate _ | TmLet _
    | TmRecLets _ | TmType _ | TmConDef _
    | TmConApp _ | TmMatch _ | TmUtest _
    | TmSeq _ | TmExt _) & t ->
    errorSingle [infoTm t] "ERROR: Term cannot be handled in compileExpr."

  -- Literals
  | TmConst { val = val } & t ->
    match val      with CInt   { val = val } then CEInt   { i = val }
    else match val with CFloat { val = val } then CEFloat { f = val }
    else match val with CChar  { val = val } then CEChar  { c = val }
    else match val with CBool  { val = val } then
      let val = match val with true then 1 else 0 in
      CEInt { i = val }
    else errorSingle [infoTm t] "Unsupported literal"

  -- Should not occur
  | (TmNever _) & t -> errorSingle [infoTm t] "Never term found in compileExpr"

end

-------------------------
-- COMPILATION FOR GCC --
-------------------------

lang MExprCCompileAlloc = MExprCCompile

  -- Name -> CType -> [{ ty: CType, id: Option Name, init: Option CInit }]
  sem alloc (name: Name) =
  | CTyPtr { ty = CTyVar { id = ident } & ty } & ptrTy ->
    [
      -- Define name as pointer to allocated struct
      { ty = CTyArray { ty = ty, size = Some (CEInt { i = 1 }) }
      , id = Some name
      , init = None ()
      }
    ]
  | CTyArray _ & ty->
    [
      { ty = ty , id = Some name , init = None () }
    ]
  | ty -> print "\n\n"; dprint ty; error "Incorrect type in alloc"

  sem free =
  | name -> error "free currently unused"

end

let _argc = nameSym "argc"
let _argv = nameSym "argv"
let _main = nameSym "main"

let cGccCompilerNames = concat cCompilerNames [
  _argc,
  _argv,
  _main
]

lang MExprCCompileGCC = MExprCCompileAlloc + CProgAst
end

let compileGCC = use MExprCCompileGCC in
  lam typeEnv: [(Name,Type)].
  lam opts : CompileCOptions.
  lam prog: Expr.

    match compile typeEnv opts prog with (env, types, tops, inits, _) in

    let mainTy = CTyFun {
      ret = CTyInt {},
      params = [
        CTyInt {},
        CTyArray { ty = CTyPtr { ty = CTyChar {} }, size = None () }] }
    in
    let funWithType = use CAst in
      lam ty. lam id. lam params. lam body.
        match ty with CTyFun { ret = ret, params = tyParams } then
          CTFun {
            ret = ret,
            id = id,
            params =
              if eqi (length tyParams) (length params) then
                zipWith (lam ty. lam p. (ty,p)) tyParams params
              else
                error "Incorrect number of parameters in funWithType",
            body = body
          }
        else error "Non-function type given to funWithType"
    in
    let main = funWithType mainTy _main [_argc, _argv] inits in
    CPProg {
      includes = cIncludes,
      tops = join [types, tops, [main]]
    }

let printCompiledCProg = use CProgPrettyPrint in
  lam cprog: CProg. printCProg cGccCompilerNames cprog

-----------
-- TESTS --
-----------

lang Test =
  MExprCCompileAlloc + MExprPrettyPrint + MExprTypeCheck +
  MExprRemoveTypeAscription + MExprANF + MExprSym + BootParser +
  MExprTypeLift + SeqTypeNoStringTypeLift + TensorTypeTypeLift +
  CProgAst
end

mexpr
use Test in
let compile: CompileCOptions -> Expr -> CProg = lam opts. lam prog.

  -- Symbolize with empty environment
  let prog = symbolizeExpr symEnvDefault prog in

  -- Type check and annotate
  let prog = typeCheck prog in

  -- Remove redundant lets
  let prog = removeTypeAscription prog in

  -- ANF transformation
  let prog = normalizeTerm prog in

  -- Second type check (needed after ANF)
  let prog = typeCheck prog in

  -- Type lift
  match typeLift prog with (env, prog) then

  -- Remove redundant lets
  let prog = removeTypeAscription prog in

  -- Run C compiler
  let cprog = compileGCC env opts prog in

  (if false then
    printLn (printCompiledCProg cprog)
  else ());

  cprog

  else never
in

let testCompile: Expr -> String = lam expr.
  printCompiledCProg (compile (defaultCompileCOptions ()) expr) in

let testCompile32Bit : Expr -> String = lam expr.
  let opts = {{defaultCompileCOptions () with use32BitInts = true}
                                         with use32BitFloats = true} in
  printCompiledCProg (compile opts expr) in

let simpleLet = bindall_ [
  ulet_ "x" (int_ 1),
  int_ 0
] in
utest testCompile simpleLet with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "int64_t x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = 1);",
  "  return 0;",
  "}"
] using eqString in

let simpleFun = bindall_ [
  let_ "foo" (tyarrows_ [tyint_, tyint_, tyint_])
    (ulam_ "a" (ulam_ "b" (addi_ (var_ "a") (var_ "b")))),
  ulet_ "x" (appf2_ (var_ "foo") (int_ 1) (int_ 2)),
  int_ 0
] in
utest testCompile simpleFun with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "int64_t foo(int64_t a, int64_t b) {",
  "  return (a + b);",
  "}",
  "int64_t x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = foo(1, 2));",
  "  return 0;",
  "}"
] using eqString in

let constants = bindall_ [
  let_ "foo" (tyarrows_ [tyunit_, tyunit_])
    (ulam_ "a" (bindall_ [
      ulet_ "t" (addi_ (int_ 1) (int_ 2)),
      ulet_ "t" (addf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (muli_ (int_ 1) (int_ 2)),
      ulet_ "t" (mulf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (divf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (eqi_ (int_ 1) (int_ 2)),
      ulet_ "t" (eqf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (lti_ (int_ 1) (int_ 2)),
      ulet_ "t" (ltf_ (float_ 1.) (float_ 2.)),
      ulet_ "t" (negf_ (float_ 1.)),
      (print_ (str_ "Hello, world!"))
    ])),
  int_ 0
] in
utest testCompile constants with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "void foo() {",
  "  char (*t) = \"Hello, world!\";",
  "  int64_t t1;",
  "  (t1 = (1 + 2));",
  "  double t2;",
  "  (t2 = (1. + 2.));",
  "  int64_t t3;",
  "  (t3 = (1 * 2));",
  "  double t4;",
  "  (t4 = (1. * 2.));",
  "  double t5;",
  "  (t5 = (1. / 2.));",
  "  char t6;",
  "  (t6 = (1 == 2));",
  "  char t7;",
  "  (t7 = (1. == 2.));",
  "  char t8;",
  "  (t8 = (1 < 2));",
  "  char t9;",
  "  (t9 = (1. < 2.));",
  "  double t10;",
  "  (t10 = (-1.));",
  "  printf(\"%s\", t);",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

utest testCompile32Bit constants with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "void foo() {",
  "  char (*t) = \"Hello, world!\";",
  "  int32_t t1;",
  "  (t1 = (1 + 2));",
  "  float t2;",
  "  (t2 = (1. + 2.));",
  "  int32_t t3;",
  "  (t3 = (1 * 2));",
  "  float t4;",
  "  (t4 = (1. * 2.));",
  "  float t5;",
  "  (t5 = (1. / 2.));",
  "  char t6;",
  "  (t6 = (1 == 2));",
  "  char t7;",
  "  (t7 = (1. == 2.));",
  "  char t8;",
  "  (t8 = (1 < 2));",
  "  char t9;",
  "  (t9 = (1. < 2.));",
  "  float t10;",
  "  (t10 = (-1.));",
  "  printf(\"%s\", t);",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

let factorial = bindall_ [
  reclet_ "factorial" (tyarrow_ tyint_ tyint_)
    (lam_ "n" tyint_
      (if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n")
          (app_ (var_ "factorial")
            (subi_ (var_ "n") (int_ 1)))))),
   int_ 0
] in
utest testCompile factorial with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "int64_t factorial(int64_t n) {",
  "  char t;",
  "  (t = (n == 0));",
  "  if ((t == 1)) {",
  "    return 1;",
  "  } else {",
  "    int64_t t1;",
  "    (t1 = (n - 1));",
  "    int64_t t2;",
  "    (t2 = factorial(t1));",
  "    return (n * t2);",
  "  }",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

-- Mutually recursive odd and even functions
let oddEven = bindall_ [
  reclets_ [
    ("odd", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (if_ (eqi_ (var_ "x") (int_ 1))
         true_
         (if_ (lti_ (var_ "x") (int_ 1))
           false_
           (app_ (var_ "even")
             (subi_ (var_ "x") (int_ 1)))))),

    ("even", tyarrow_ tyint_ tybool_,
     lam_ "x" tyint_
       (if_ (eqi_ (var_ "x") (int_ 0))
          true_
          (if_ (lti_ (var_ "x") (int_ 0))
            false_
            (app_ (var_ "odd")
              (subi_ (var_ "x") (int_ 1))))))
  ],
  int_ 0
] in
utest testCompile oddEven with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "char odd(int64_t);",
  "char even(int64_t);",
  "char odd(int64_t x) {",
  "  char t;",
  "  (t = (x == 1));",
  "  if ((t == 1)) {",
  "    return 1;",
  "  } else {",
  "    char t1;",
  "    (t1 = (x < 1));",
  "    if ((t1 == 1)) {",
  "      return 0;",
  "    } else {",
  "      int64_t t2;",
  "      (t2 = (x - 1));",
  "      return even(t2);",
  "    }",
  "  }",
  "}",
  "char even(int64_t x1) {",
  "  char t3;",
  "  (t3 = (x1 == 0));",
  "  if ((t3 == 1)) {",
  "    return 1;",
  "  } else {",
  "    char t4;",
  "    (t4 = (x1 < 0));",
  "    if ((t4 == 1)) {",
  "      return 0;",
  "    } else {",
  "      int64_t t5;",
  "      (t5 = (x1 - 1));",
  "      return odd(t5);",
  "    }",
  "  }",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

let typedefs = bindall_ [

  type_ "Tree" [] (tyvariant_ []),
  type_ "Integer" [] tyint_,
  type_ "MyRec" [] (tyrecord_ [("k", (tycon_ "Integer"))]),
  type_ "MyRec2" [] (tyrecord_ [("k", (tycon_ "MyRec")), ("t", (tycon_ "Tree"))]),
  type_ "Integer2" [] (tycon_ "Integer"),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", (tycon_ "Integer2"))]) (tycon_ "Tree")),
  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tycon_ "Tree")), ("r", (tycon_ "Tree"))])
    (tycon_ "Tree")),

  int_ 0
] in
utest testCompile typedefs with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Tree Tree;",
  "typedef int64_t Integer;",
  "typedef struct Rec {Integer k;} Rec;",
  "typedef Rec MyRec;",
  "typedef struct Rec1 {MyRec k; Tree (*t);} Rec1;",
  "typedef Rec1 (*MyRec2);",
  "typedef Integer Integer2;",
  "typedef struct Rec2 {Integer2 v;} Rec2;",
  "typedef struct Rec3 {Tree (*l); Tree (*r); int64_t v;} Rec3;",
  "enum constrs {Leaf, Node};",
  "typedef struct Tree {enum constrs constr; union {Rec2 Leaf; Rec3 (*Node);};} Tree;",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

-- Potentially tricky case with type aliases
let alias = bindall_ [
  type_ "MyRec" [] (tyrecord_ [("k", tyint_)]),
  let_ "myRec" (tycon_ "MyRec") (urecord_ [("k", int_ 0)]),
  int_ 0
] in
utest testCompile alias with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Rec {int64_t k;} Rec;",
  "typedef Rec MyRec;",
  "Rec myRec;",
  "int main(int argc, char (*argv[])) {",
  "  ((myRec.k) = 0);",
  "  return 0;",
  "}"
] using eqString in

-- Externals test
let ext = bindall_ [
  ext_ "externalLog" false (tyarrow_ tyfloat_ tyfloat_),
  let_ "x" (tyfloat_) (app_ (var_ "externalLog") (float_ 2.)),
  int_ 0
] in
utest testCompile ext with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "double externalLog(double a1) {",
  "  return log(a1);",
  "}",
  "double x;",
  "int main(int argc, char (*argv[])) {",
  "  (x = log(2.));",
  "  return 0;",
  "}"
] using eqString in

let leaf_ = lam v.
  conapp_ "Leaf" (urecord_ [("v", int_ v)]) in

let node_ = lam v. lam left. lam right.
  conapp_ "Node" (urecord_ [("v", int_ v), ("l", left), ("r", right)]) in

let trees = bindall_ [

  type_ "Tree" [] (tyvariant_ []),

  condef_ "Leaf"
    (tyarrow_ (tyrecord_ [("v", tyint_)]) (tycon_ "Tree")),

  condef_ "Node" (tyarrow_
    (tyrecord_ [("v", tyint_), ("l", (tycon_ "Tree")), ("r", (tycon_ "Tree"))])
    (tycon_ "Tree")),

  ulet_ "tree"
    (node_ 1 (node_ 2 (leaf_ 3) (leaf_ 4)) (node_ 5 (leaf_ 6) (leaf_ 7))),

  reclet_
    "treeRec" (tyarrow_ (tycon_ "Tree") tyint_)
    (lam_ "t" (tycon_ "Tree")
       (match_ (var_ "t") (pcon_ "Node" (prec_ [
           ("v", pvar_ "v"),
           ("l", pvar_ "l"),
           ("r", pvar_ "r")
         ]))
         (addi_ (addi_ (var_ "v") (app_ (var_ "treeRec") (var_ "l")))
            (app_ (var_ "treeRec") (var_ "r")))
         (match_ (var_ "t") (pcon_ "Leaf" (prec_ [("v", pvar_ "v")]))
            (var_ "v") never_))
      ),

  ulet_ "sum" (app_ (var_ "treeRec") (var_ "tree")),

  int_ 0
] in

utest testCompile trees with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Tree Tree;",
  "typedef struct Rec {int64_t v;} Rec;",
  "typedef struct Rec1 {Tree (*l); Tree (*r); int64_t v;} Rec1;",
  "enum constrs {Leaf, Node};",
  "typedef struct Tree {enum constrs constr; union {Rec Leaf; Rec1 (*Node);};} Tree;",
  "Rec t;",
  "Tree t1[1];",
  "Rec t2;",
  "Tree t3[1];",
  "Rec1 t4[1];",
  "Tree t5[1];",
  "Rec t6;",
  "Tree t7[1];",
  "Rec t8;",
  "Tree t9[1];",
  "Rec1 t10[1];",
  "Tree t11[1];",
  "Rec1 t12[1];",
  "Tree tree[1];",
  "int64_t treeRec(Tree (*t13)) {",
  "  if (((t13->constr) == Node)) {",
  "    int64_t v1 = ((t13->Node)->v);",
  "    Tree (*l1) = ((t13->Node)->l);",
  "    Tree (*r1) = ((t13->Node)->r);",
  "    int64_t t14;",
  "    (t14 = treeRec(l1));",
  "    int64_t t15;",
  "    (t15 = (v1 + t14));",
  "    int64_t t16;",
  "    (t16 = treeRec(r1));",
  "    return (t15 + t16);",
  "  } else {",
  "    if (((t13->constr) == Leaf)) {",
  "      int64_t v2 = ((t13->Leaf).v);",
  "      return v2;",
  "    } else {",
  "      ;",
  "    }",
  "  }",
  "}",
  "int64_t sum;",
  "int main(int argc, char (*argv[])) {",
  "  ((t.v) = 7);",
  "  ((t1->constr) = Leaf);",
  "  ((t1->Leaf) = t);",
  "  ((t2.v) = 6);",
  "  ((t3->constr) = Leaf);",
  "  ((t3->Leaf) = t2);",
  "  ((t4->l) = t3);",
  "  ((t4->r) = t1);",
  "  ((t4->v) = 5);",
  "  ((t5->constr) = Node);",
  "  ((t5->Node) = t4);",
  "  ((t6.v) = 4);",
  "  ((t7->constr) = Leaf);",
  "  ((t7->Leaf) = t6);",
  "  ((t8.v) = 3);",
  "  ((t9->constr) = Leaf);",
  "  ((t9->Leaf) = t8);",
  "  ((t10->l) = t9);",
  "  ((t10->r) = t7);",
  "  ((t10->v) = 2);",
  "  ((t11->constr) = Node);",
  "  ((t11->Node) = t10);",
  "  ((t12->l) = t11);",
  "  ((t12->r) = t5);",
  "  ((t12->v) = 1);",
  "  ((tree->constr) = Node);",
  "  ((tree->Node) = t12);",
  "  (sum = treeRec(tree));",
  "  return 0;",
  "}"
] using eqString in

-- let leaf = match tree with node then leftnode else
let manyAllocs = bindall_ [

  ulet_ "rec" (match_ (bool_ true) (pbool_ true) (urecord_ [("a",int_ 1)]) (urecord_ [("a",int_ 2)])),

  int_ 0

] in

utest testCompile manyAllocs with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Rec {int64_t a;} Rec;",
  "Rec rec;",
  "int main(int argc, char (*argv[])) {",
  "  Rec alloc;",
  "  Rec alloc1;",
  "  if ((1 == 1)) {",
  "    ((alloc1.a) = 1);",
  "    (rec = alloc1);",
  "  } else {",
  "    ((alloc.a) = 2);",
  "    (rec = alloc);",
  "  }",
  "  return 0;",
  "}"
] using eqString in

-- NOTE(larshum, 2022-03-02): We use type-ascriptions so that the intrinsic
-- functions are treated as monomorphic, even though they are not.
let seq = bindall_ [
  let_ "s" (tyseq_ tyint_) (seq_ [int_ 1, int_ 2, int_ 3]),
  app_
    (bind_
      (let_ "len" (tyarrow_ (tyseq_ tyint_) tyint_) (uconst_ (CLength ())))
      (var_ "len"))
    (var_ "s")
] in

utest testCompile seq with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Seq {int64_t (*seq); int64_t len;} Seq;",
  "int64_t seqAlloc[3];",
  "Seq s;",
  "int main(int argc, char (*argv[])) {",
  "  ((seqAlloc[0]) = 1);",
  "  ((seqAlloc[1]) = 2);",
  "  ((seqAlloc[2]) = 3);",
  "  ((s.seq) = seqAlloc);",
  "  ((s.len) = 3);",
  "  return (s.len);",
  "}"
] using eqString in

let tensor = bindall_ [
  let_ "update" (tytensorsetexn_ tyint_)
    (ulam_ "t" (ulam_ "dims" (ulam_ "v"
      (appSeq_
        (bind_
          (let_ "set" (tytensorsetexn_ tyint_) (uconst_ (CTensorSetExn ())))
          (var_ "set"))
        [var_ "t", var_ "dims", var_ "v"])))),
  let_ "access" (tytensorgetexn_ tyfloat_)
    (ulam_ "t" (ulam_ "dims"
      (appSeq_
        (bind_
          (let_ "get" (tytensorgetexn_ tyfloat_) (uconst_ (CTensorGetExn ())))
          (var_ "get"))
        [var_ "t", var_ "dims"]))),
  let_ "rank" (tytensorrank_ tyint_)
    (ulam_ "t"
      (app_
        (bind_
          (let_ "r" (tytensorrank_ tyint_) (uconst_ (CTensorRank ())))
          (var_ "r"))
        (var_ "t"))),
  let_ "shape" (tytensorshape_ tyint_)
    (ulam_ "t"
      (app_
        (bind_
          (let_ "s" (tytensorshape_ tyint_) (uconst_ (CTensorShape ())))
          (var_ "s"))
        (var_ "t"))),
  int_ 0
] in

utest testCompile tensor with strJoin "\n" [
  "#include <stdint.h>",
  "#include <stdio.h>",
  "#include <math.h>",
  "typedef struct Tensor {int64_t id; int64_t (*data); int64_t dims[3]; int64_t rank; int64_t size;} Tensor;",
  "typedef struct Seq {int64_t (*seq); int64_t len;} Seq;",
  "typedef struct Tensor1 {int64_t id; double (*data); int64_t dims[3]; int64_t rank; int64_t size;} Tensor1;",
  "int64_t cartesian_to_linear_index0(int64_t dims1[3], int64_t rank1) {",
  "  return 0;",
  "}",
  "int64_t cartesian_to_linear_index1(int64_t dims1[3], int64_t rank1, int64_t i) {",
  "  if ((rank1 == 3)) {",
  "    return (((dims1[2]) * (dims1[1])) * i);",
  "  } else {",
  "    if ((rank1 == 2)) {",
  "      return ((dims1[1]) * i);",
  "    } else {",
  "      return i;",
  "    }",
  "  }",
  "}",
  "int64_t cartesian_to_linear_index2(int64_t dims1[3], int64_t rank1, int64_t i1, int64_t i2) {",
  "  if ((rank1 == 3)) {",
  "    return ((((dims1[2]) * (dims1[1])) * i1) + ((dims1[2]) * i2));",
  "  } else {",
  "    if ((rank1 == 2)) {",
  "      return (((dims1[1]) * i1) + i2);",
  "    } else {",
  "      printf(\"Accessed tensor of rank %ld using 2 indices\\n\", rank1);",
  "      return -1;",
  "    }",
  "  }",
  "}",
  "int64_t cartesian_to_linear_index3(int64_t dims1[3], int64_t rank1, int64_t i3, int64_t i4, int64_t i5) {",
  "  if ((rank1 == 3)) {",
  "    return (((((dims1[2]) * (dims1[1])) * i3) + ((dims1[2]) * i4)) + i5);",
  "  } else {",
  "    printf(\"Accessed tensor of rank %ld using 3 indices\\n\", rank1);",
  "    return -1;",
  "  }",
  "}",
  "int64_t cartesian_to_linear_index(int64_t dims1[3], int64_t rank1, Seq cartesian_idx) {",
  "  if (((cartesian_idx.len) == 1)) {",
  "    return cartesian_to_linear_index1(dims1, rank1, ((cartesian_idx.seq)[0]));",
  "  } else {",
  "    if (((cartesian_idx.len) == 2)) {",
  "      return cartesian_to_linear_index2(dims1, rank1, ((cartesian_idx.seq)[0]), ((cartesian_idx.seq)[1]));",
  "    } else {",
  "      if (((cartesian_idx.len) == 3)) {",
  "        return cartesian_to_linear_index3(dims1, rank1, ((cartesian_idx.seq)[0]), ((cartesian_idx.seq)[1]), ((cartesian_idx.seq)[2]));",
  "      } else {",
  "        return cartesian_to_linear_index0(dims1, rank1);",
  "      }",
  "    }",
  "  }",
  "}",
  "Seq tensor_shape(int64_t dims2[3], int64_t rank2) {",
  "  Seq s;",
  "  ((s.seq) = dims2);",
  "  ((s.len) = rank2);",
  "  return s;",
  "}",
  "void update(Tensor t, Seq dims3, int64_t v) {",
  "  (((t.data)[cartesian_to_linear_index((t.dims), (t.rank), dims3)]) = v);",
  "}",
  "double access(Tensor1 t1, Seq dims4) {",
  "  return ((t1.data)[cartesian_to_linear_index((t1.dims), (t1.rank), dims4)]);",
  "}",
  "int64_t rank3(Tensor t2) {",
  "  return (t2.rank);",
  "}",
  "Seq shape(Tensor t3) {",
  "  return tensor_shape((t3.dims), (t3.rank));",
  "}",
  "int main(int argc, char (*argv[])) {",
  "  return 0;",
  "}"
] using eqString in

-- let leaf = match tree with node then leftnode else
let seqs = bindall_ [

  -- Define nested sequence, and see how it is handled
  ulet_ "seq" (seq_ [seq_ [int_ 1], seq_ [int_ 2]]),

  -- Use "length" and "get" functions

  int_ 0

] in

()
