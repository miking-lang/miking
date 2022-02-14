-- Translates the PMExpr AST to a CUDA-specific PMExpr representation which
-- includes explicit GPU kernel calls and memory management operations.
--
-- The translation assumes that the given PMExpr node is in ANF.

include "cuda/pmexpr-ast.mc"
include "pmexpr/utils.mc"

lang CudaMemoryManagement = CudaPMExprAst + PMExprVariableSub
  type CudaMemoryEnv = Map Name AllocEnv

  type AllocEnv = Map Name AllocMem

  sem allocEnvEmpty =
  | () -> mapEmpty nameCmp

  sem allocEnvInsert (id : Name) (mem : AllocMem) =
  | env -> mapInsert id mem env

  sem allocEnvLookup (id : Name) =
  | env -> mapLookup id env

  sem allocEnvRemove (id : Name) =
  | env -> mapRemove id env

  sem cudaMemMgrError =
  | info ->
    infoErrorExit info "Internal compiler error: CUDA memory management phase failed"

  sem toCudaPMExpr (accelerateData : Map Name AccelerateData) =
  | t -> toCudaPMExprH accelerateData (mapEmpty nameCmp) t

  sem toCudaPMExprH (accelerateData : Map Name AccelerateData)
                    (cudaEnv : Map Name AllocEnv) =
  | TmLet t ->
    match mapLookup t.ident accelerateData with Some data then
      let body = generateKernelApplications t.body in
      let env = allocEnvEmpty () in
      match addMemoryAllocations env body with (env, body) in
      match addFreeOperations env body with (_, body) in
      -- TODO(larshum, 2022-02-03): Here we should optimize away unnecessary
      -- operations, like allocating multiple copies of the same variable on
      -- the same memory space.
      let cudaEnv = mapInsert t.ident env cudaEnv in
      match toCudaPMExprH accelerateData cudaEnv t.inexpr with (cudaEnv, inexpr) in
      (cudaEnv, TmLet {{t with body = body} with inexpr = inexpr})
    else
      match toCudaPMExprH accelerateData cudaEnv t.inexpr with (cudaEnv, inexpr) in
      (cudaEnv, TmLet {t with inexpr = inexpr})
  | TmRecLets t ->
    match toCudaPMExprH accelerateData cudaEnv t.inexpr with (cudaEnv, inexpr) in
    (cudaEnv, TmRecLets {t with inexpr = inexpr})
  | t -> (cudaEnv, t)

  sem generateKernelApplications =
  | TmApp {lhs = TmApp {lhs = TmConst {val = CMap ()}, rhs = f}, rhs = s,
           ty = ty, info = info} ->
    TmMapKernel {f = f, s = s, ty = ty, info = info}
  | TmParallelReduce t ->
    TmReduceKernel {f = t.f, ne = t.ne, s = t.ne, commutative = false,
                    ty = t.ty, info = t.info}
  | t -> smap_Expr_Expr generateKernelApplications t

  sem addMemoryAllocations (env : AllocEnv) =
  | TmVar t ->
    -- NOTE(larshum, 2022-02-03): Ensure that the return variable is allocated
    -- on the CPU. Under the assumption that the AST is in ANF, the resulting
    -- expression must always be a variable.
    match allocEnvLookup t.ident env with Some (Cpu _) then
      (env, TmVar t)
    else
      let cpuId = nameSetNewSym t.ident in
      let varAlloc = TmLet {
        ident = cpuId, tyBody = t.ty,
        body = TmCopy {arg = TmVar t, toMem = Cpu (), ty = t.ty, info = t.info},
        inexpr = TmVar {t with ident = cpuId}, ty = t.ty, info = t.info} in
      (env, varAlloc)
  | TmLam t ->
    let env = allocEnvInsert t.ident (Cpu ()) env in
    match addMemoryAllocations env t.body with (env, body) in
    (env, TmLam {t with body = body})
  | TmLet t ->
    let toMem = if isKernel t.body then Gpu () else Cpu () in
    let env = allocEnvInsert t.ident toMem env in
    let vars : Map Name (AllocMem, Type) = collectVarsInExpr env t.body in
    let subMap =
      mapFoldWithKey
        (lam subMap : [Map Name (Info -> Expr)]. lam id : Name.
         lam memTy : (AllocMem, Type).
          match memTy with (mem, ty) in
          match ty with TySeq _ then
            if eqMem mem toMem then subMap
            else
              let altId = nameSetNewSym id in
              let exprFun = lam info.
                TmVar {ident = altId, ty = ty, info = info, frozen = false} in
              mapInsert id exprFun subMap
          else subMap)
        (mapEmpty nameCmp) vars in
    let env =
      mapFoldWithKey
        (lam acc : AllocEnv. lam. lam exprF : Info -> Expr.
          let expr = exprF (NoInfo ()) in
          match expr with TmVar vt then
            allocEnvInsert vt.ident toMem acc
          else cudaMemMgrError t.info)
        env subMap in
    match addMemoryAllocations env t.inexpr with (env, inexpr) in
    let letExpr = TmLet {{t with body = substituteVariables subMap t.body}
                            with inexpr = inexpr} in
    let letExpr =
      mapFoldWithKey
        (lam acc : Expr. lam id : Name. lam exprF : Info -> Expr.
          let expr = exprF (infoTm acc) in
          match expr with TmVar vt then
            let copyExpr = TmCopy {
              arg = TmVar {vt with ident = id}, toMem = toMem,
              ty = tyTm expr, info = infoTm expr} in
            TmLet {ident = vt.ident, tyBody = tyTm copyExpr, body = copyExpr,
                   inexpr = acc, ty = tyTm acc, info = infoTm acc}
          else cudaMemMgrError t.info)
        letExpr subMap in
    (env, letExpr)
  | t -> smapAccumL_Expr_Expr addMemoryAllocations env t

  sem addFreeOperations (env : AllocEnv) =
  | TmVar t ->
    let env = allocEnvRemove t.ident env in
    (env, TmVar t)
  | TmLam t ->
    let env = allocEnvRemove t.ident env in
    match addFreeOperations env t.body with (env, body) in
    (env, TmLam {t with body = body})
  | TmLet t ->
    let vars : Map Name (AllocMem, Type) = collectVarsInExpr env t.body in
    match addFreeOperations env t.inexpr with (env, inexpr) in
    match
      mapFoldWithKey
        (lam acc : (AllocEnv, [Expr]). lam id : Name. lam memTy : (AllocMem, Type).
          match memTy with (mem, ty) in
          match ty with TySeq _ then
            match acc with (env, accLets) in
            match allocEnvLookup id env with Some _ then
              let freeExpr = TmFree {arg = id, tyArg = ty, mem = mem,
                                     ty = tyunit_, info = t.info} in
              let freeLet = TmLet {
                ident = nameNoSym "", tyBody = tyunit_, body = freeExpr,
                inexpr = unit_, ty = t.ty, info = t.info} in
              let env = allocEnvRemove id env in
              (env, snoc accLets freeLet)
            else acc
          else acc)
        (env, []) vars
    with (env, freeLets) in
    (env, bindall_ (join [[TmLet {t with inexpr = unit_}], freeLets, [inexpr]]))
  | t -> smapAccumL_Expr_Expr addFreeOperations env t

  sem collectVarsInExpr (env : AllocEnv) =
  | t -> collectVarsInExprH env (mapEmpty nameCmp) t

  sem collectVarsInExprH (env : AllocEnv) (acc : Map Name (AllocMem, Type)) =
  | TmVar t ->
    match allocEnvLookup t.ident env with Some mem then
      mapInsert t.ident (mem, t.ty) acc
    else acc
  | t -> sfold_Expr_Expr (collectVarsInExprH env) acc t
end

lang TestLang = CudaMemoryManagement + MExprPrettyPrint
  sem isAtomic =
  | TmMapKernel _ -> false
  | TmCopy _ -> false
  | TmFree _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmMapKernel t ->
    match pprintCode indent env t.f with (env, f) in
    match pprintCode indent env t.s with (env, s) in
    (env, join ["mapKernel (", f, ") ", s])
  | TmCopy t ->
    match pprintCode indent env t.arg with (env, arg) in
    let fnName =
      match t.toMem with Cpu _ then "copyToCpu"
      else match t.toMem with Gpu _ then "copyToGpu"
      else never in
    (env, join [fnName, " ", arg])
  | TmFree t ->
    match pprintVarName env t.arg with (env, ident) in
    match t.mem with Cpu _ then
      (env, join ["freeCpu ", ident])
    else match t.mem with Gpu _ then
      (env, join ["freeGpu ", ident])
    else never
end

mexpr

use TestLang in

let f = nameSym "f" in
let g = nameSym "g" in
let h = nameSym "h" in
let s = nameSym "a" in
let s2 = nameSym "b" in
let s3 = nameSym "c" in
let x = nameSym "x" in
let y = nameSym "y" in
let main = nameSym "main" in
-- The functions f, g and h are assumed to be declared outside the scope of the
-- "main" accelerate function.
let typeVarEnv = mapFromSeq nameCmp [
  (f, tyarrow_ tyint_ tyint_),
  (g, tyarrows_ [tyint_, tyint_, tyint_]),
  (h, tyarrow_ tyint_ tyint_)] in
let typeEnv = {_typeEnvEmpty with varEnv = typeVarEnv} in
let t = typeAnnotExpr typeEnv
  (nlet_ main (tyarrow_ (tyseq_ tyint_) (tyseq_ tyint_)) (nlam_ s (tyseq_ tyint_)
    (bindall_ [
      nlet_ s2 (tyseq_ tyint_) (map_ (nvar_ f) (nvar_ s)),
      nlet_ y tyint_ (foldl_ (nvar_ g) (int_ 0) (nvar_ s2)),
      nlet_ s3 (tyseq_ tyint_) (map_ (app_ (nvar_ h) (nvar_ y)) (nvar_ s2)),
      nvar_ s3]))) in
let expected = nulet_ main (nulam_ s (bindall_ [
  ulet_ "t" (copyGpu_ (nvar_ s)),
  nulet_ s2 (mapKernel_ (nvar_ f) (var_ "t")),
  ulet_ "" (freeGpu_ (nameNoSym "t") (tyseq_ tyint_)),
  ulet_ "t3" (copyCpu_ (nvar_ s2)),
  nulet_ y (foldl_ (nvar_ g) (int_ 0) (var_ "t3")),
  ulet_ "" (freeCpu_ (nameNoSym "t3") (tyseq_ tyint_)),
  nulet_ s3 (mapKernel_ (app_ (nvar_ h) (nvar_ y)) (nvar_ s2)),
  ulet_ "" (freeGpu_ s2 (tyseq_ tyint_)),
  ulet_ "t6" (copyCpu_ (nvar_ s3)),
  ulet_ "" (freeGpu_ s3 (tyseq_ tyint_)),
  var_ "t6"])) in
let accelerateData = mapFromSeq nameCmp [(main,
  { identifier = main, bytecodeWrapperId = nameNoSym "bc"
  , params = [(s, tyseq_ tyint_)], returnType = tyseq_, info = NoInfo ()})] in
match toCudaPMExpr accelerateData t with (_, t) in
utest t with expected using eqExpr in

()
