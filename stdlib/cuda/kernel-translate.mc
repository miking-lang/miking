-- Defines translate rules for CUDA kernels.

include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"

lang CudaKernelTranslate = CudaAst
  sem translateCudaTops (entryIds : Set Name) =
  | tops -> map (translateTopToCudaFormat entryIds) tops

  sem translateTopToCudaFormat (entryIds : Set Name) =
  | CTTyDef t ->
    CuTTop {attrs = [], top = CTTyDef {t with ty = replaceIntWithInt64 t.ty}}
  | CTDef t ->
    CuTTop {
      attrs = [CuADevice ()],
      top = CTDef {t with ty = replaceIntWithInt64 t.ty}}
  | CTFun t ->
    let wrapParamInPointer = lam param : (CType, Name).
      match param with (ty, id) in
      (CTyPtr {ty = ty}, id) in
    let replaceIntsInParam = lam param : (CType, Name).
      match param with (ty, id) in
      (replaceIntWithInt64 ty, id) in
    let params = map replaceIntsInParam t.params in
    let body = map replaceIntWithInt64Stmt t.body in
    let swapTuple = lam t : (a, b). match t with (x, y) in (y, x) in
    if setMem t.id entryIds then
      let outId = nameSym "out" in
      let outParam = (t.ret, outId) in
      let kernelParams = map wrapParamInPointer (cons outParam params) in
      let paramLookup : Map Name CType =
        mapFromSeq nameCmp (map swapTuple kernelParams) in
      let cudaId = nameSym (concat "cuda_" (nameGetStr t.id)) in
      let cudaFun = CTFun {
        ret = CTyVoid (),
        id = cudaId,
        params = kernelParams,
        body = translateKernelBody paramLookup outId body} in
      CuTTop {attrs = [CuAGlobal ()], top = cudaFun}
    else
      let ret = replaceIntWithInt64 t.ret in
      CuTTop {
        attrs = [CuADevice ()],
        top = CTFun {{{t with ret = ret}
                         with params = params}
                         with body = body}}

  sem replaceIntWithInt64 =
  | CTyInt _ -> CTyInt64 ()
  | ty -> smapCTypeCType replaceIntWithInt64 ty

  sem replaceIntWithInt64Expr =
  | CECast t -> CECast {{t with ty = replaceIntWithInt64 t.ty}
                           with rhs = replaceIntWithInt64Expr t.rhs}
  | CESizeOfType t -> CESizeOfType {t with ty = replaceIntWithInt64 t.ty}
  | expr -> smap_CExpr_CExpr replaceIntWithInt64Expr expr

  sem replaceIntWithInt64Init =
  | init -> smap_CInit_CExpr replaceIntWithInt64Expr init

  sem replaceIntWithInt64Stmt =
  | CSDef t ->
    let ty = replaceIntWithInt64 t.ty in
    let init = optionMap replaceIntWithInt64Init t.init in
    CSDef {{t with ty = ty} with init = init}
  | stmt ->
    let stmt = smap_CStmt_CStmt replaceIntWithInt64Stmt stmt in
    smap_CStmt_CExpr replaceIntWithInt64Expr stmt

  sem translateKernelBody (params : Map Name CType) (outId : Name) =
  | stmts ->
    -- 1. Replace the return statement with an assignment to the address
    -- pointed to by the output pointer parameter.
    let stmts = map (_replaceReturnWithOutPointer params outId) stmts in

    -- NOTE(larshum, 2022-01-18): We apply the below steps under the assumption
    -- that the accelerated code consists only of a (fully applied) map
    -- expression. The inlining makes it easier to identify what happens, and
    -- simplifies the translation to using thread and block indexing.

    -- 2. Inline declaration, definition and assignment to output parameter to
    -- one statement.
    let stmts = _inlineStmts stmts in

    -- 3. Translate body to use thread and block indexing.
    let stmts = _useCudaIndexing stmts in

    -- 4. Replace any uses of the 'int' type with 'int64_t'.
    let stmts = map replaceIntWithInt64Stmt stmts in

    stmts

  sem _replaceReturnWithOutPointer (params : Map Name CType) (outId : Name) =
  | CSRet {val = Some t} ->
    CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEUnOp {op = CODeref (), arg = CEVar {id = outId}},
      rhs = t}}
  | CSRet _ -> error "Found generated kernel function with void return type"
  | t -> t

  sem _inlineStmts =
  | stmts &
    [ CSDef {id = Some id1, init = None ()}
    , CSExpr {expr = CEBinOp {op = COAssign (), lhs = CEVar {id = id2}, rhs = e}}
    , CSExpr {expr = CEBinOp {op = COAssign (), lhs = out, rhs = CEVar {id = id3}}}] ->
    if and (nameEq id1 id2) (nameEq id1 id3) then
      [CSExpr {expr = CEBinOp {
        op = COAssign (),
        lhs = out, rhs = e}}]
    else stmts
  | stmts -> stmts

  sem _useCudaIndexing =
  | [CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEUnOp {op = CODeref (), arg = CEVar {id = outId}},
      rhs = CEMap {f = CEVar {id = funId}, s = CEVar {id = s}}}}] ->
    let indexId = nameSym "idx" in
    let getElem = lam seqId : Name.
      CEBinOp {
        op = COSubScript (),
        lhs = CEArrow {lhs = CEVar {id = seqId}, id = _seqKey},
        rhs = CEVar {id = indexId}}
    in
    let indexStmt = CSDef {
      ty = CTyInt (),
      id = Some indexId,
      init = Some (CIExpr {expr = CEBinOp {
        op = COAdd (),
        lhs = CEThreadIdx {dim = CuDX ()},
        rhs = CEBinOp {
          op = COMul (),
          lhs = CEBlockIdx {dim = CuDX ()},
          rhs = CEBlockDim {dim = CuDX ()}}}})} in
    let applyStmt = CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = getElem outId,
      rhs = CEApp {
        fun = funId,
        args = [getElem s]}}} in
    [ indexStmt
    , CSIf {
        cond = CEBinOp {
          op = COLt (), lhs = CEVar {id = indexId},
          rhs = CEArrow {lhs = CEVar {id = s}, id = _seqLenKey}},
        thn = [applyStmt],
        els = []} ]
  | _ -> error "Could not perform CUDA translation"
end
