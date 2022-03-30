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
  | TmTensorSliceExn {t : Expr, slice : Expr, ty : Type, info : Info}
  | TmTensorSubExn {t : Expr, ofs : Expr, len : Expr, ty : Type, info : Info}
  | TmMapKernel {f : Expr, s : Expr, ty : Type, info : Info}
  | TmReduceKernel {f : Expr, ne : Expr, s : Expr, commutative : Bool, ty : Type, info : Info}
  | TmLoopKernel {n : Expr, f : Expr, ty : Type, info : Info}
  | TmCopy {arg : Name, toMem : AllocMem, ty : Type, info : Info}
  | TmFree {arg : Name, tyArg : Type, mem : AllocMem, ty : Type, info : Info}

  sem isKernel =
  | TmMapKernel t -> true
  | TmReduceKernel t -> true
  | TmLoopKernel t -> true
  | _ -> false

  sem tyTm =
  | TmSeqMap t -> t.ty
  | TmSeqFoldl t -> t.ty
  | TmTensorSliceExn t -> t.ty
  | TmTensorSubExn t -> t.ty
  | TmMapKernel t -> t.ty
  | TmReduceKernel t -> t.ty
  | TmLoopKernel t -> t.ty
  | TmCopy t -> t.ty
  | TmFree t -> t.ty

  sem infoTm =
  | TmSeqMap t -> t.info
  | TmSeqFoldl t -> t.info
  | TmTensorSliceExn t -> t.info
  | TmTensorSubExn t -> t.info
  | TmMapKernel t -> t.info
  | TmReduceKernel t -> t.info
  | TmLoopKernel t -> t.info
  | TmCopy t -> t.info
  | TmFree t -> t.info

  sem withType (ty : Type) =
  | TmSeqMap t -> TmSeqMap {t with ty = ty}
  | TmSeqFoldl t -> TmSeqFoldl {t with ty = ty}
  | TmTensorSliceExn t -> TmTensorSliceExn {t with ty = ty}
  | TmTensorSubExn t -> TmTensorSubExn {t with ty = ty}
  | TmMapKernel t -> TmMapKernel {t with ty = ty}
  | TmReduceKernel t -> TmReduceKernel {t with ty = ty}
  | TmLoopKernel t -> TmLoopKernel {t with ty = ty}
  | TmCopy t -> TmCopy {t with ty = ty}
  | TmFree t -> TmFree {t with ty = ty}

  sem withInfo (info : Info) =
  | TmSeqMap t -> TmSeqMap {t with info = info}
  | TmSeqFoldl t -> TmSeqFoldl {t with info = info}
  | TmTensorSliceExn t -> TmTensorSliceExn {t with info = info}
  | TmTensorSubExn t -> TmTensorSubExn {t with info = info}
  | TmMapKernel t -> TmMapKernel {t with info = info}
  | TmReduceKernel t -> TmReduceKernel {t with info = info}
  | TmLoopKernel t -> TmLoopKernel {t with info = info}
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
  | TmTensorSliceExn t ->
    match f acc t.t with (acc, tt) in
    match f acc t.slice with (acc, slice) in
    (acc, TmTensorSliceExn {{t with t = tt} with slice = slice})
  | TmTensorSubExn t ->
    match f acc t.t with (acc, tt) in
    match f acc t.ofs with (acc, ofs) in
    match f acc t.len with (acc, len) in
    (acc, TmTensorSubExn {{{t with t = tt} with ofs = ofs} with len = len})
  | TmMapKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.s with (acc, s) in
    (acc, TmMapKernel {{t with f = tf} with s = s})
  | TmReduceKernel t ->
    match f acc t.f with (acc, tf) in
    match f acc t.ne with (acc, ne) in
    match f acc t.s with (acc, s) in
    (acc, TmReduceKernel {{{t with f = tf} with ne = ne} with s = s})
  | TmLoopKernel t ->
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, TmLoopKernel {{t with n = n} with f = tf})
  | TmCopy t -> (acc, TmCopy t)
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
  | TmTensorSliceExn t ->
    let tt = typeAnnotExpr env t.t in
    let slice = typeAnnotExpr env t.slice in
    TmTensorSliceExn {{{t with t = tt}
                          with slice = slice}
                          with ty = tyTm tt}
  | TmTensorSubExn t ->
    let tt = typeAnnotExpr env t.t in
    let ofs = typeAnnotExpr env t.ofs in
    let len = typeAnnotExpr env t.len in
    TmTensorSubExn {{{{t with t = tt}
                         with ofs = ofs}
                         with len = len}
                         with ty = tyTm tt}
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
  | TmLoopKernel t ->
    let n = typeAnnotExpr env t.n in
    let f = typeAnnotExpr env t.f in
    let ty =
      match tyTm f with TyArrow {from = TyInt _, to = unit & (TyRecord {labels = []})} then
        unit
      else TyUnknown {info = t.info} in
    TmLoopKernel {{{t with n = n}
                      with f = f}
                      with ty = ty}
  | TmCopy t ->
    let ty =
      match mapLookup t.arg env.varEnv with Some ty then ty
      else tyunknown_ in
    TmCopy {t with ty = ty}
  | TmFree t -> TmFree {t with ty = tyunit_}

  sem typeCheckBase (env : TCEnv) =
  | TmSeqMap t ->
    let f = typeCheckExpr env t.f in
    let s = typeCheckExpr env t.s in
    let inElemType = newvar env.currentLvl t.info in
    let outElemType = newvar env.currentLvl t.info in
    unify env (tyTm s) (ityseq_ t.info inElemType);
    unify env (tyTm f) (ityarrow_ t.info inElemType outElemType);
    TmSeqMap {{{t with f = f}
                  with s = s}
                  with ty = TySeq {ty = outElemType, info = t.info}}
  | TmSeqFoldl t ->
    let f = typeCheckExpr env t.f in
    let acc = typeCheckExpr env t.acc in
    let s = typeCheckExpr env t.s in
    let sElemTy = newvar env.currentLvl t.info in
    unify env (tyTm s) (ityseq_ t.info sElemTy);
    unify env (tyTm f) (ityarrow_ t.info (tyTm acc)
                                  (ityarrow_ t.info sElemTy (tyTm acc)));
    TmSeqFoldl {{{{t with f = f}
                     with acc = acc}
                     with s = s}
                     with ty = tyTm acc}
  | TmTensorSliceExn t ->
    let tt = typeCheckExpr env t.t in
    let slice = typeCheckExpr env t.slice in
    let elemTy = newvar env.currentLvl t.info in
    unify env (tyTm tt) (tyWithInfo t.info (tytensor_ elemTy));
    unify env (tyTm slice) (ityseq_ t.info (tyWithInfo t.info tyint_));
    TmTensorSliceExn {{{t with t = tt}
                          with slice = slice}
                          with ty = tyTm tt}
  | TmTensorSubExn t ->
    let tt = typeCheckExpr env t.t in
    let ofs = typeCheckExpr env t.ofs in
    let len = typeCheckExpr env t.len in
    let elemTy = newvar env.currentLvl t.info in
    unify env (tyTm tt) (tyWithInfo t.info (tytensor_ elemTy));
    unify env (tyTm ofs) (tyWithInfo t.info tyint_);
    unify env (tyTm len) (tyWithInfo t.info tyint_);
    TmTensorSubExn {{{{t with t = tt}
                         with ofs = ofs}
                         with len = len}
                         with ty = tyTm tt}
  | TmMapKernel t ->
    let f = typeCheckExpr env t.f in
    let s = typeCheckExpr env t.s in
    let inElemType = newvar env.currentLvl t.info in
    let outElemType = newvar env.currentLvl t.info in
    unify env (tyTm s) (ityseq_ t.info inElemType);
    unify env (tyTm f) (ityarrow_ t.info inElemType outElemType);
    TmMapKernel {{{t with f = f}
                     with s = s}
                     with ty = TySeq {ty = outElemType, info = t.info}}
  | TmReduceKernel t ->
    let f = typeCheckExpr env t.f in
    let ne = typeCheckExpr env t.ne in
    let s = typeCheckExpr env t.s in
    let seqElemTy = newvar env.currentLvl t.info in
    let neTy = tyTm ne in
    unify env (tyTm s) (ityseq_ t.info neTy);
    unify env (tyTm f) (ityarrow_ t.info neTy (ityarrow_ t.info neTy neTy));
    TmReduceKernel {{{{t with f = f}
                         with ne = ne}
                         with s = s}
                         with ty = neTy}
  | TmLoopKernel t ->
    let n = typeCheckExpr env t.n in
    let f = typeCheckExpr env t.f in
    let unitType = tyWithInfo t.info tyunit_ in
    unify env (tyTm n) (tyWithInfo t.info tyint_);
    unify env (tyTm f) (ityarrow_ t.info (tyTm n) unitType);
    TmLoopKernel {{{t with n = n}
                      with f = f}
                      with ty = unitType}
  | TmCopy t ->
    match mapLookup t.arg env.varEnv with Some ty then
      TmCopy {t with ty = ty}
    else
      let msg = join [
        "Type check failed: copy referring to unbound variable: ",
        nameGetStr t.arg, "\n"] in
      infoErrorExit t.info msg
  | TmFree t -> TmFree {t with ty = tyWithInfo t.info tyunit_}


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
  | TmTensorSliceExn r ->
    match lhs with TmTensorSliceExn l then
      match eqExprH env free l.t r.t with Some free then
        eqExprH env free l.slice r.slice
      else None ()
    else None ()
  | TmTensorSubExn r ->
    match lhs with TmTensorSubExn l then
      match eqExprH env free l.t r.t with Some free then
        match eqExprH env free l.ofs r.ofs with Some free then
          eqExprH env free l.len r.len
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
  | TmLoopKernel r ->
    match lhs with TmLoopKernel l then
      match eqExprH env free l.n r.n with Some free then
        eqExprH env free l.f r.f
      else None ()
    else None ()
  | TmCopy r ->
    match lhs with TmCopy l then
      match (env, free) with ({varEnv = varEnv}, {varEnv = freeVarEnv}) in
      match _eqCheck l.arg r.arg varEnv freeVarEnv with Some freeVarEnv then
        Some {free with varEnv = freeVarEnv}
      else None ()
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
  | TmTensorSliceExn t ->
    k (TmTensorSliceExn {{t with t = normalizeTerm t.t}
                            with slice = normalizeTerm t.slice})
  | TmTensorSubExn t ->
    k (TmTensorSubExn {{{t with t = normalizeTerm t.t}
                           with ofs = normalizeTerm t.ofs}
                           with len = normalizeTerm t.len})
  | TmMapKernel t ->
    k (TmMapKernel {{t with f = normalizeTerm t.f}
                       with s = normalizeTerm t.s})
  | TmReduceKernel t ->
    k (TmReduceKernel {{{t with f = normalizeTerm t.f}
                           with ne = normalizeTerm t.ne}
                           with s = normalizeTerm t.s})
  | TmLoopKernel t ->
    k (TmLoopKernel {{t with n = normalizeTerm t.n}
                        with f = normalizeTerm t.f})
  | TmCopy t -> k (TmCopy t)
  | TmFree t -> k (TmFree t)
end

let seqMap_ = lam f. lam s.
  use CudaPMExprAst in
  TmSeqMap {f = f, s = s, ty = tyunknown_, info = NoInfo ()}

let seqFoldl_ = lam f. lam acc. lam s.
  use CudaPMExprAst in
  TmSeqFoldl {f = f, acc = acc, s = s, ty = tyunknown_, info = NoInfo ()}

let tensorSliceExn_ = lam t. lam slice.
  use CudaPMExprAst in
  TmTensorSliceExn {t = t, slice = slice, ty = tyunknown_, info = NoInfo ()}

let tensorSubExn_ = lam t. lam ofs. lam len.
  use CudaPMExprAst in
  TmTensorSubExn {t = t, ofs = ofs, len = len, ty = tyunknown_, info = NoInfo ()}

let mapKernel_ = lam f. lam s.
  use CudaPMExprAst in
  TmMapKernel {f = f, s = s, ty = tyunknown_, info = NoInfo ()}

let reduceKernel_ = lam f. lam ne. lam s.
  use CudaPMExprAst in
  TmReduceKernel {f = f, ne = ne, s = s, ty = tyunknown_, info = NoInfo ()}

let loopKernel_ = lam n. lam f.
  use CudaPMExprAst in
  TmLoopKernel {n = n, f = f, ty = tyunknown_, info = NoInfo ()}

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
