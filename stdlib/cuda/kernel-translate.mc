-- Translates C top-level definitions to the CUDA specific representation of
-- tops. This includes the addition of CUDA attributes, and providing distinct
-- names for the CUDA wrapper functions, which handle interaction with CUDA
-- kernels.

include "name.mc"
include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"

lang CudaKernelTranslate = CudaAst
  sem translateCudaTops (entryIds : Set Name) =
  | tops -> mapAccumL (translateTopToCudaFormat entryIds) (mapEmpty nameCmp) tops

  sem translateTopToCudaFormat (entryIds : Set Name) (acc : Map Name Name) =
  | CTTyDef t -> (acc, CuTTop {attrs = [], top = CTTyDef t})
  | CTDef t -> (acc, CuTTop {attrs = [CuAHost (), CuADevice ()], top = CTDef t})
  | CTFun t ->
    if setMem t.id entryIds then
      let cudaWrapperId = nameSym "cuda_wrap" in
      ( mapInsert t.id cudaWrapperId acc
      , CuTTop {attrs = [], top = CTFun {t with id = cudaWrapperId}})
    else
      let attrs = [CuAHost (), CuADevice ()] in
      (acc, CuTTop {attrs = attrs, top = CTFun t})
end
