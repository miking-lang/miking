-- Translates C top-level definitions to the CUDA specific representation of
-- tops. This includes the addition of CUDA attributes, and providing distinct
-- names for the CUDA wrapper functions, which handle interaction with CUDA
-- kernels. It also involves updating GPU variables to be pointers, rather than
-- being allocated on the (CPU) stack.

include "name.mc"
include "set.mc"
include "c/compile.mc"
include "cuda/ast.mc"
include "cuda/memory.mc"

lang CudaKernelTranslate = CudaAst + CudaMemoryManagement
  sem usePointerToGpuVariablesStmt (env : AllocEnv) =
  | CSDef (t & {id = Some id}) ->
    match allocEnvLookup id env with Some (Gpu _) then
      CSDef {t with ty = CTyPtr {ty = t.ty}}
    else CSDef t
  | stmt -> stmt

  sem translateCudaTops (cudaMemEnv : Map Name AllocEnv) =
  | tops ->
    let emptyEnv = mapEmpty nameCmp in
    mapAccumL (translateTopToCudaFormat cudaMemEnv) emptyEnv tops

  sem translateTopToCudaFormat (cudaMemEnv : Map Name AllocEnv) 
                               (acc : Map Name Name) =
  | CTTyDef t -> (acc, CuTTop {attrs = [], top = CTTyDef t})
  | CTDef t -> (acc, CuTTop {attrs = [CuAHost (), CuADevice ()], top = CTDef t})
  | CTFun t ->
    match mapLookup t.id cudaMemEnv with Some allocEnv then
      let cudaWrapperId = nameSym "cuda_wrap" in
      let body = map (usePointerToGpuVariablesStmt allocEnv) t.body in
      let cTop = CTFun {{t with id = cudaWrapperId}
                           with body = body} in
      let acc = mapInsert t.id cudaWrapperId acc in
      (acc, CuTTop {attrs = [], top = cTop})
    else
      let attrs = [CuAHost (), CuADevice ()] in
      (acc, CuTTop {attrs = attrs, top = CTFun t})
end
