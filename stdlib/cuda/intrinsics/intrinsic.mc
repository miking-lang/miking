-- Defines a base language fragment containing functions shared between
-- multiple intrinsics.

include "cuda/ast.mc"
include "cuda/compile.mc"

lang CudaIntrinsic = CudaAst + CudaCompile
  sem _getFunctionIdAndArgs =
  | CEVar {id = id} -> (id, [])
  | CEApp {fun = fun, args = args} -> (fun, args)
  | _ -> error "Unsupported function call"

  sem _getFunctionArgNames =
  | CEVar {id = id} -> []
  | CEApp {fun = fun, args = args} ->
    let getArgName = lam arg : CExpr.
      match arg with CEVar {id = id} then id
      else error "Unsupported function call"
    in
    map getArgName args
  | _ -> error "Unsupported function call"
end
