-- An extension of the PMExpr AST with nodes specific to CUDA (it should
-- hopefully be compatible with OpenCL so that we can reuse it there in the
-- future).

include "name.mc"
include "pmexpr/ast.mc"

lang CudaPMExprAst = PMExprAst
  syn AllocMem =
  | Cpu ()
  | Gpu ()

  sem eqMem (lhs : AllocMem) =
  | rhs -> eqi (constructorTag lhs) (constructorTag rhs)

  syn Expr =
  | TmSeqMap {f : Expr, s : Expr, ty : Type, info : Info}
  | TmSeqFoldl {f : Expr, acc : Expr, s : Expr, ty : Type, info : Info}
  | TmMapKernel {f : Expr, s : Expr, ty : Type, info : Info}
  | TmReduceKernel {f : Expr, ne : Expr, s : Expr, commutative : Bool, ty : Type, info : Info}
  | TmCopy {arg : Expr, toMem : AllocMem, ty : Type, info : Info}
  | TmFree {arg : Name, tyArg : Type, mem : AllocMem, ty : Type, info : Info}

  sem isKernel =
  | TmMapKernel t -> true
  | TmReduceKernel t -> true
  | _ -> false

  sem tyTm =
  | TmSeqMap t -> t.ty
  | TmSeqFoldl t -> t.ty
  | TmMapKernel t -> t.ty
  | TmReduceKernel t -> t.ty
  | TmCopy t -> t.ty
  | TmFree t -> t.ty

  sem infoTm =
  | TmSeqMap t -> t.info
  | TmSeqFoldl t -> t.info
  | TmMapKernel t -> t.info
  | TmReduceKernel t -> t.info
  | TmCopy t -> t.info
  | TmFree t -> t.info

  sem withType (ty : Type) =
  | TmSeqMap t -> TmSeqMap {t with ty = ty}
  | TmSeqFoldl t -> TmSeqFoldl {t with ty = ty}
  | TmMapKernel t -> TmMapKernel {t with ty = ty}
  | TmReduceKernel t -> TmReduceKernel {t with ty = ty}
  | TmCopy t -> TmCopy {t with ty = ty}
  | TmFree t -> TmFree {t with ty = ty}

  sem withInfo (info : Info) =
  | TmSeqMap t -> TmSeqMap {t with info = info}
  | TmSeqFoldl t -> TmSeqFoldl {t with info = info}
  | TmMapKernel t -> TmMapKernel {t with info = info}
  | TmReduceKernel t -> TmReduceKernel {t with info = info}
  | TmCopy t -> TmCopy {t with info = info}
  | TmFree t -> TmFree {t with info = info}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmSeqMap t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, TmSeqMap {{t with f = tf} with s = s})
  | TmSeqFoldl t ->
    match f acc t.f with (acc, tf) in
    match f acc t.acc with (acc, tacc) in
    match f acc t.s with (acc, s) in
    (acc, TmSeqFoldl {{{t with f = tf} with acc = tacc} with s = s})
  | TmMapKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, TmMapKernel {{t with f = tf} with s = s})
  | TmReduceKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.ne with (acc, ne) in
    match f acc t.s with (acc, s) in
    (acc, TmReduceKernel {{{t with f = tf} with ne = ne} with s = s})
  | TmCopy t ->
    match f acc t.arg with (acc, arg) in
    (acc, TmCopy {t with arg = arg})
  | TmFree t -> (acc, TmFree t)

  sem smapAccumL_Expr_Type (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmFree t ->
    match f acc t.tyArg with (acc, tyArg) in
    (acc, TmFree {t with tyArg = tyArg})

  sem typeAnnotExpr (env : TypeEnv) =
  | TmSeqMap t ->
    let f = typeAnnotExpr env t.f in
    let s = typeAnnotExpr env t.s in
    let outElemTy =
      match tyTm f with TyArrow {to = to} then to
      else tyunknown_ in
    TmSeqMap {{{t with f = f}
                  with s = s}
                  with ty = tyseq_ outElemTy}
  | TmSeqFoldl t ->
    let f = typeAnnotExpr env t.f in
    let acc = typeAnnotExpr env t.acc in
    let s = typeAnnotExpr env t.s in
    TmSeqFoldl {{{{t with f = f}
                     with acc = acc}
                     with s = s}
                     with ty = tyTm acc}
  | TmMapKernel t ->
    let f = typeAnnotExpr env t.f in
    let s = typeAnnotExpr env t.s in
    let outElemTy =
      match tyTm f with TyArrow {to = to} then to
      else tyunknown_ in
    TmMapKernel {{{t with f = f}
                     with s = s}
                     with ty = tyseq_ outElemTy}
  | TmReduceKernel t ->
    let f = typeAnnotExpr env t.f in
    let ne = typeAnnotExpr env t.ne in
    let s = typeAnnotExpr env t.s in
    let seqElemTy =
      match tyTm s with TySeq {ty = elemTy} then elemTy
      else tyunknown_ in
    let kernelTy =
      optionGetOrElse
        (lam. tyunknown_)
        (compatibleType env seqElemTy ne) in
    TmReduceKernel {{{{t with f = f}
                         with ne = ne}
                         with s = s}
                         with ty = kernelTy}
  | TmCopy t ->
    let arg = typeAnnotExpr env t.arg in
    TmCopy {{t with arg = arg}
               with ty = tyTm arg}
  | TmFree t -> TmFree {t with ty = tyunit_}

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmSeqMap r ->
    match lhs with TmSeqMap l then
      match eqExprH env free l.f r.f with Some free then
        eqExprH env free l.s r.s
      else None ()
    else None ()
  | TmSeqFoldl r ->
    match lhs with TmSeqFoldl l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.acc r.acc with Some free then
          eqExprH env free l.s r.s
        else None ()
      else None ()
    else None ()
  | TmMapKernel r ->
    match lhs with TmMapKernel l then
      match eqExprH env free l.f r.f with Some free then
        eqExprH env free l.s r.s
      else None ()
    else None ()
  | TmReduceKernel r ->
    match lhs with TmReduceKernel l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.ne r.ne with Some free then
          eqExprH env free l.s r.s
        else None ()
      else None ()
    else None ()
  | TmCopy r ->
    match lhs with TmCopy l then
      eqExprH env free l.arg r.arg
    else None ()
  | TmFree r ->
    match lhs with TmFree l then
      match (env, free) with ({varEnv = varEnv}, {varEnv = freeVarEnv}) in
      match _eqCheck l.arg r.arg varEnv freeVarEnv with Some freeVarEnv then
        Some {free with varEnv = freeVarEnv}
      else None ()
    else None ()

  sem normalize (k : Expr -> Expr) =
  | TmSeqMap t ->
    k (TmSeqMap {{t with f = normalizeTerm t.f}
                    with s = normalizeTerm t.s})
  | TmSeqFoldl t ->
    k (TmSeqFoldl {{{t with f = normalizeTerm t.f}
                       with acc = normalizeTerm t.acc}
                       with s = normalizeTerm t.s})
  | TmMapKernel t ->
    k (TmMapKernel {{t with f = normalizeTerm t.f}
                       with s = normalizeTerm t.s})
  | TmReduceKernel t ->
    k (TmReduceKernel {{{t with f = normalizeTerm t.f}
                           with ne = normalizeTerm t.ne}
                           with s = normalizeTerm t.s})
  | TmCopy t -> k (TmCopy {t with arg = normalizeTerm t.arg})
  | TmFree t -> k (TmFree t)
end

let seqMap_ = lam f. lam s.
  use CudaPMExprAst in
  TmSeqMap {f = f, s = s, ty = tyunknown_, info = NoInfo ()}

let seqFoldl_ = lam f. lam acc. lam s.
  use CudaPMExprAst in
  TmSeqFoldl {f = f, acc = acc, s = s, ty = tyunknown_, info = NoInfo ()}

let mapKernel_ = lam f. lam s.
  use CudaPMExprAst in
  TmMapKernel {f = f, s = s, ty = tyunknown_, info = NoInfo ()}

let reduceKernel_ = lam f. lam ne. lam s.
  use CudaPMExprAst in
  TmReduceKernel {f = f, ne = ne, s = s, ty = tyunknown_, info = NoInfo ()}

let copyCpu_ = lam arg.
  use CudaPMExprAst in
  TmCopy {arg = arg, toMem = Cpu (), ty = tyunknown_, info = NoInfo ()}

let copyGpu_ = lam arg.
  use CudaPMExprAst in
  TmCopy {arg = arg, toMem = Gpu (), ty = tyunknown_, info = NoInfo ()}

let freeCpu_ = lam arg. lam tyArg.
  use CudaPMExprAst in
  TmFree {arg = arg, tyArg = tyArg, mem = Cpu (), ty = tyunknown_, info = NoInfo ()}

let freeGpu_ = lam arg. lam tyArg.
  use CudaPMExprAst in
  TmFree {arg = arg, tyArg = tyArg, mem = Gpu (), ty = tyunknown_, info = NoInfo ()}
