-- Defines translate rules for CUDA kernels.

include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"

lang CudaKernelTranslate = CudaAst
  sem translateCudaTops (entryIds : Set Name) =
  | tops -> map (translateTop entryIds) tops

  sem translateTop (entryIds : Set Name) =
  | CTDef _ & def -> CuTTop {attrs = [CuADevice ()], top = def}
  | CTFun t & fun ->
    let wrapParamInPointer = lam param : (CType, Name).
      match param with (ty, id) in
      (CTyPtr {ty = ty}, id) in
    let swapTuple = lam t : (a, b). match t with (x, y) in (y, x) in
    if setMem t.id entryIds then
      let outId = nameSym "out" in
      let outParam = (t.ret, outId) in
      let kernelParams = map wrapParamInPointer (cons outParam t.params) in
      let paramLookup : Map Name CType =
        mapFromSeq nameCmp (map swapTuple kernelParams) in
      let cudaFun = CTFun {
        ret = CTyVoid (),
        id = t.id,
        params = kernelParams,
        body = translateKernelBody paramLookup outId t.body} in
      CuTTop {attrs = [CuAGlobal ()], top = cudaFun}
    else CuTTop {attrs = [CuADevice ()], top = fun}
  | t -> CuTTop {attrs = [], top = t}

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
