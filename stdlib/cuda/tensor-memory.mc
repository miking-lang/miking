-- CUDA management of tensor memory.

include "cuda/ast.mc"
include "cuda/wrapper.mc"

lang CudaTensorStatusUpdate = CudaAst
  -- After every update of a tensor value, we insert an update of the
  -- appropriate status. As we cannot know at runtime whether the code runs on
  -- the CPU or the GPU, we use a macro to detect this statically (different
  -- code is generated for CPU and GPU) and update the appropriate status.
  sem updateStatusAfterTensorSetStmt =
  | (CSExpr {expr = CEBinOp {
      op = COAssign (),
      lhs = CEBinOp {
        op = COSubScript (),
        lhs = CEMember {lhs = tensorExpr, id = key}}}}) & stmt ->
    if nameEq _tensorDataKey key then
      let setStateStmt = lam statusId.
        CSExpr {expr = CEBinOp {
          op = COAssign (),
          lhs = CEBinOp {
            op = COSubScript (),
            lhs = CEVar {id = _tensorStateData},
            rhs = CEMember {lhs = tensorExpr, id = _tensorIdKey}},
          rhs = CEVar {id = statusId}}} in
      let cudaArchVar = CEVar {id = nameNoSym "__CUDA_ARCH__"} in
      let isFirstThreadExpr = CEBinOp {
        op = COEq (),
        lhs = CEBinOp {
          op = COAdd (),
          lhs = CEBinOp {
            op = COMul (),
            lhs = CEBlockDim {dim = CuDX ()},
            rhs = CEBlockIdx {dim = CuDX ()}},
          rhs = CEThreadIdx {dim = CuDX ()}},
        rhs = CEInt {i = 0}} in
      let stateUpdateMacroStmt = CSIfMacro {
        cond = CEBinOp {
          op = COAnd (),
          lhs = CEApp {fun = nameNoSym "defined", args = [cudaArchVar]},
          rhs = CEBinOp {
            op = COGt (),
            lhs = cudaArchVar,
            rhs = CEInt {i = 0}}},
        thn = [setStateStmt _tensorStateCpuInvalid],
        els = [setStateStmt _tensorStateGpuInvalid]} in
      [stmt, stateUpdateMacroStmt]
    else [stmt]
  | stmt -> [stmt]

  -- Adds code for updating the status after every 'tensorSetExn' update (as
  -- this is C code, it is a write to the .data key of a tensor).
  sem updateStatusAfterTensorSet =
  | CuTTop (tt & {top = CTFun t}) ->
    let newBody = join (map updateStatusAfterTensorSetStmt t.body) in
    CuTTop {tt with top = CTFun {t with body = newBody}}
  | t -> t
end

lang CudaTensorMemory = CudaTensorStatusUpdate
  sem addCudaTensorMemoryManagement : [CuTop] -> [CuTop]
  sem addCudaTensorMemoryManagement =
  | tops -> map updateStatusAfterTensorSet tops
end
