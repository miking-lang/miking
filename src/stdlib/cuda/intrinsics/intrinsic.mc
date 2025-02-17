-- Defines a base language fragment containing functions shared between
-- multiple intrinsics.

include "cuda/ast.mc"
include "cuda/compile.mc"

lang CudaIntrinsic = CudaAst + CudaCompile
  sem generateCudaIntrinsicFunction : CompileCEnv -> CExpr -> (Name, CuTop)

  sem generateCudaIntrinsicCall : CompileCEnv -> [CuTop] -> CExpr -> CExpr
                               -> ([CuTop], CStmt)

  sem _getSequenceElemType (env : CompileCEnv) =
  | ty ->
    -- TODO(larshum, 2022-02-08): Assumes 1d sequence
    match _unwrapType env.typeEnv ty with TySeq {ty = ty} then
      compileType env ty
    else errorSingle [infoTy ty] "Could not unwrap sequence type"

  sem _getStructDataElemType (env : CompileCEnv) =
  | cty ->
    recursive let findTypeId : CType -> Name = lam ty.
      match ty with CTyPtr t then findTypeId t.ty
      else match ty with CTyVar {id = id} then id
      else error "Expected struct type"
    in
    let typeId = findTypeId cty in
    _getSequenceElemType env (TyCon {ident = typeId, info = NoInfo ()})

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
