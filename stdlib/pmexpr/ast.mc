include "mexpr/anf.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/type-check.mc"

lang PMExprAst =
  KeywordMaker + MExprAst + MExprEq + MExprANF + MExprTypeCheck

  syn Expr =
  | TmAccelerate {e : Expr, ty : Type, info : Info}
  | TmFlatten {e : Expr, ty : Type, info : Info}
  | TmMap2 {f : Expr, as : Expr, bs : Expr, ty : Type, info : Info}
  | TmParallelReduce {f : Expr, ne : Expr, as : Expr, ty : Type, info : Info}
  | TmLoop {n : Expr, f : Expr, ty : Type, info : Info}
  | TmLoopAcc {ne : Expr, n : Expr, f : Expr, ty : Type, info : Info}
  | TmParallelLoop {n : Expr, f : Expr, ty : Type, info : Info}
  | TmPrintFloat {e : Expr, ty : Type, info : Info}
  | TmParallelSizeCoercion {e: Expr, size : Name, ty : Type, info : Info}
  | TmParallelSizeEquality {x1: Name, d1: Int, x2: Name, d2: Int, ty : Type, info : Info}

  sem isKeyword =
  | TmAccelerate _ -> true
  | TmFlatten _ -> true
  | TmMap2 _ -> true
  | TmParallelReduce _ -> true
  | TmLoop _ -> true
  | TmLoopAcc _ -> true
  | TmParallelLoop _ -> true
  | TmPrintFloat _ -> true

  sem matchKeywordString (info : Info) =
  | "accelerate" ->
    Some (1, lam lst. TmAccelerate {e = get lst 0, ty = TyUnknown {info = info},
                                    info = info})
  | "parallelMap" ->
    Some (2, lam lst. TmConst {val = CMap (), ty = TyUnknown {info = info}, info = info})
  | "flatten" ->
    Some (1, lam lst. TmFlatten {e = get lst 0, ty = TyUnknown {info = info},
                                 info = info})
  | "map2" ->
    Some (3, lam lst. TmMap2 {f = get lst 0, as = get lst 1,
                              bs = get lst 2,
                              ty = TyUnknown {info = info}, info = info})
  | "reduce" ->
    Some (3, lam lst. TmParallelReduce {f = get lst 0, ne = get lst 1,
                                        as = get lst 2,
                                        ty = TyUnknown {info = info},
                                        info = info})
  | "seqLoop" ->
    Some (2, lam lst. TmLoop {n = get lst 0, f = get lst 1,
                              ty = TyUnknown {info = info}, info = info})
  | "seqLoopAcc" ->
    Some (3, lam lst. TmLoopAcc {ne = get lst 0, n = get lst 1,
                                 f = get lst 2, ty = TyUnknown {info = info},
                                 info = info})
  | "loop" ->
    Some (2, lam lst. TmParallelLoop {n = get lst 0, f = get lst 1,
                                      ty = TyUnknown {info = info},
                                      info = info})
  | "printFloat" ->
    Some (1, lam lst. TmPrintFloat {e = get lst 0,
                                    ty = TyUnknown {info = info}, info = info})

  sem tyTm =
  | TmAccelerate t -> t.ty
  | TmFlatten t -> t.ty
  | TmMap2 t -> t.ty
  | TmParallelReduce t -> t.ty
  | TmLoop t -> t.ty
  | TmLoopAcc t -> t.ty
  | TmParallelLoop t -> t.ty
  | TmPrintFloat t -> t.ty
  | TmParallelSizeCoercion t -> t.ty
  | TmParallelSizeEquality t -> t.ty

  sem infoTm =
  | TmAccelerate t -> t.info
  | TmFlatten t -> t.info
  | TmMap2 t -> t.info
  | TmParallelReduce t -> t.info
  | TmLoop t -> t.info
  | TmLoopAcc t -> t.info
  | TmParallelLoop t -> t.info
  | TmPrintFloat t -> t.info
  | TmParallelSizeCoercion t -> t.info
  | TmParallelSizeEquality t -> t.info

  sem withType (ty : Type) =
  | TmAccelerate t -> TmAccelerate {t with ty = ty}
  | TmFlatten t -> TmFlatten {t with ty = ty}
  | TmMap2 t -> TmMap2 {t with ty = ty}
  | TmParallelReduce t -> TmParallelReduce {t with ty = ty}
  | TmLoop t -> TmLoop {t with ty = ty}
  | TmLoopAcc t -> TmLoopAcc {t with ty = ty}
  | TmParallelLoop t -> TmParallelLoop {t with ty = ty}
  | TmPrintFloat t -> TmPrintFloat {t with ty = ty}
  | TmParallelSizeCoercion t -> TmParallelSizeCoercion {t with ty = ty}
  | TmParallelSizeEquality t -> TmParallelSizeEquality {t with ty = ty}

  sem smapAccumL_Expr_Expr f acc =
  | TmAccelerate t ->
    match f acc t.e with (acc, e) in
    (acc, TmAccelerate {t with e = e})
  | TmFlatten t ->
    match f acc t.e with (acc, e) in
    (acc, TmFlatten {t with e = e})
  | TmMap2 t ->
    match f acc t.f with (acc, tf) in
    match f acc t.as with (acc, as) in
    match f acc t.bs with (acc, bs) in
    (acc, TmMap2 {{{t with f = tf} with as = as} with bs = bs})
  | TmParallelReduce t ->
    match f acc t.f with (acc, tf) in
    match f acc t.ne with (acc, ne) in
    match f acc t.as with (acc, as) in
    (acc, TmParallelReduce {{{t with f = tf} with ne = ne} with as = as})
  | TmLoop t ->
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, TmLoop {{t with n = n} with f = tf})
  | TmLoopAcc t ->
    match f acc t.ne with (acc, ne) in
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, TmLoopAcc {{{t with ne = ne} with n = n} with f = tf})
  | TmParallelLoop t ->
    match f acc t.n with (acc, n) in
    match f acc t.f with (acc, tf) in
    (acc, TmParallelLoop {{t with n = n} with f = tf})
  | TmPrintFloat t ->
    match f acc t.e with (acc, e) in
    (acc, TmPrintFloat {t with e = e})
  | TmParallelSizeCoercion t ->
    match f acc t.e with (acc, e) in
    (acc, TmParallelSizeCoercion {t with e = e})

  sem typeCheckExpr env =
  | TmAccelerate t ->
    let e = typeCheckExpr env t.e in
    TmAccelerate {{t with e = e}
                     with ty = tyTm e}
  | TmFlatten t ->
    let e = typeCheckExpr env t.e in
    let elemTy = newvar env.currentLvl t.info in
    unify env [infoTm e, t.info] (tyTm e) (ityseq_ t.info (ityseq_ t.info elemTy));
    TmFlatten {{t with e = e}
                  with ty = TySeq {ty = elemTy, info = t.info}}
  | TmMap2 t ->
    let f = typeCheckExpr env t.f in
    let as = typeCheckExpr env t.as in
    let bs = typeCheckExpr env t.bs in
    let aElemTy = newvar env.currentLvl t.info in
    let bElemTy = newvar env.currentLvl t.info in
    let outElemTy = newvar env.currentLvl t.info in
    unify env [infoTm as, t.info] (tyTm as) (ityseq_ t.info aElemTy);
    unify env [infoTm bs, t.info] (tyTm bs) (ityseq_ t.info bElemTy);
    unify env [infoTm f, t.info] (tyTm f)
      (ityarrow_ t.info aElemTy (ityarrow_ t.info bElemTy outElemTy));
    TmMap2 {{{{t with f = f}
                 with as = as}
                 with bs = bs}
                 with ty = TySeq {ty = outElemTy, info = t.info}}
  | TmParallelReduce t ->
    let f = typeCheckExpr env t.f in
    let ne = typeCheckExpr env t.ne in
    let as = typeCheckExpr env t.as in
    let accType = tyTm ne in
    unify env [infoTm as, t.info] (tyTm as) (ityseq_ t.info accType);
    unify env [infoTm f, t.info] (tyTm f)
      (ityarrow_ t.info accType (ityarrow_ t.info accType accType));
    TmParallelReduce {{{{t with f = f}
                           with ne = ne}
                           with as = as}
                           with ty = tyTm ne}
  | TmLoop t ->
    let n = typeCheckExpr env t.n in
    let f = typeCheckExpr env t.f in
    let unitType = tyWithInfo t.info tyunit_ in
    unify env [infoTm n, t.info] (tyTm n) (tyWithInfo t.info tyint_);
    unify env [infoTm f, t.info] (tyTm f) (ityarrow_ t.info (tyTm n) unitType);
    TmLoop {{{t with n = n}
                with f = f}
                with ty = unitType}
  | TmLoopAcc t ->
    let ne = typeCheckExpr env t.ne in
    let n = typeCheckExpr env t.n in
    let f = typeCheckExpr env t.f in
    unify env [infoTm n, t.info] (tyTm n) (tyWithInfo t.info tyint_);
    unify env [infoTm f, t.info] (tyTm f) (ityarrow_ t.info (tyTm ne)
                                         (ityarrow_ t.info (tyTm n) (tyTm ne)));
    TmLoopAcc {{{{t with ne = ne}
                    with n = n}
                    with f = f}
                    with ty = tyTm ne}
  | TmParallelLoop t ->
    let n = typeCheckExpr env t.n in
    let f = typeCheckExpr env t.f in
    let unitType = tyWithInfo t.info tyunit_ in
    unify env [infoTm n, t.info] (tyTm n) (tyWithInfo t.info tyint_);
    unify env [infoTm f, t.info] (tyTm f) (ityarrow_ t.info (tyTm n) unitType);
    TmParallelLoop {{{t with n = n}
                        with f = f}
                        with ty = unitType}
  | TmPrintFloat t ->
    let e = typeCheckExpr env t.e in
    let unitType = tyWithInfo t.info tyunit_ in
    unify env [infoTm e, t.info] (tyTm e) (tyWithInfo t.info tyfloat_);
    TmPrintFloat {{t with e = e} with ty = unitType}
  | TmParallelSizeCoercion t ->
    let e = typeCheckExpr env t.e in
    TmParallelSizeCoercion {{t with e = e} with ty = tyTm e}
  | TmParallelSizeEquality t ->
    TmParallelSizeEquality {t with ty = tyWithInfo t.info tyunit_}

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmAccelerate r ->
    match lhs with TmAccelerate l then
      eqExprH env free l.e r.e
    else None ()
  | TmFlatten r ->
    match lhs with TmFlatten l then
      eqExprH env free l.e r.e
    else None ()
  | TmMap2 r ->
    match lhs with TmMap2 l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.as r.as with Some free then
          eqExprH env free l.bs r.bs
        else None ()
      else None ()
    else None ()
  | TmParallelReduce r ->
    match lhs with TmParallelReduce l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.ne r.ne with Some free then
          eqExprH env free l.as r.as
        else None ()
      else None ()
    else None ()
  | TmLoop r ->
    match lhs with TmLoop l then
      match eqExprH env free l.n r.n with Some free then
        eqExprH env free l.f r.f
      else None ()
    else None ()
  | TmLoopAcc r ->
    match lhs with TmLoopAcc l then
      match eqExprH env free l.ne r.ne with Some free then
        match eqExprH env free l.n r.n with Some free then
          eqExprH env free l.f r.f
        else None ()
      else None ()
    else None ()
  | TmParallelLoop r ->
    match lhs with TmParallelLoop l then
      match eqExprH env free l.n r.n with Some free then
        eqExprH env free l.f r.f
      else None ()
    else None ()
  | TmPrintFloat r ->
    match lhs with TmPrintFloat l then
      eqExprH env free l.e r.e
    else None ()
  | TmParallelSizeCoercion r ->
    match lhs with TmParallelSizeCoercion l then
      match eqExprH env free l.e r.e with Some free then
        let free : EqEnv = free in
        match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) in
        match _eqCheck l.size r.size varEnv freeVarEnv with Some freeVarEnv then
          Some {free with varEnv = freeVarEnv}
        else None ()
      else None ()
    else None ()
  | TmParallelSizeEquality r ->
    match lhs with TmParallelSizeEquality l then
      match (env,free) with ({varEnv = varEnv},{varEnv = freeVarEnv}) in
      match _eqCheck l.x1 r.x1 varEnv freeVarEnv with Some freeVarEnv then
        if eqi l.d1 r.d1 then
          match _eqCheck l.x2 r.x2 varEnv freeVarEnv with Some freeVarEnv then
            if eqi l.d2 r.d2 then Some {free with varEnv = freeVarEnv}
            else None ()
          else None ()
        else None ()
      else None ()
    else None ()

  sem normalize (k : Expr -> Expr) =
  | TmAccelerate t ->
    k (TmAccelerate {t with e = normalizeTerm t.e})
  | TmFlatten t ->
    normalizeName (lam e. k (TmFlatten {t with e = e})) t.e
  | TmMap2 t ->
    normalizeNames
      (lam f.
        normalizeName
          (lam as.
            normalizeName
              (lam bs.
                k (TmMap2 {t with f = f, as = as, bs = bs}))
              t.bs)
          t.as)
      t.f
  | TmParallelReduce t ->
    normalizeNames
      (lam f.
        normalizeName
          (lam as.
            normalizeName
              (lam ne.
                k (TmParallelReduce {t with f = f, ne = ne, as = as}))
              t.ne)
          t.as)
      t.f
  | TmLoop t ->
    normalizeNames
      (lam n.
        normalizeName
          (lam f.
            k (TmLoop {t with n = n, f = f}))
          t.f)
      t.n
  | TmLoopAcc t ->
    normalizeNames
      (lam ne.
        normalizeName
          (lam n.
            normalizeName
              (lam f.
                k (TmLoopAcc {t with ne = ne, n = n, f = f}))
              t.f)
          t.n)
      t.ne
  | TmParallelLoop t ->
    normalizeNames
      (lam n.
        normalizeName
          (lam f.
            k (TmParallelLoop {t with n = n, f = f}))
          t.f)
      t.n
  | TmPrintFloat t ->
    normalizeName (lam e. k (TmPrintFloat {t with e = e})) t.e
  | TmParallelSizeCoercion t ->
    normalizeName (lam e. k (TmParallelSizeCoercion {t with e = e})) t.e
  | TmParallelSizeEquality t -> k (TmParallelSizeEquality t)
end

let accelerate_ = lam e.
  use PMExprAst in
  TmAccelerate {e = e, ty = tyunknown_, info = NoInfo ()}

let flatten_ = lam e.
  use PMExprAst in
  TmFlatten {e = e, ty = tyunknown_, info = NoInfo ()}

let map2_ = lam f. lam as. lam bs.
  use PMExprAst in
  TmMap2 {f = f, as = as, bs = bs, ty = tyunknown_, info = NoInfo ()}

let parallelReduce_ = lam f. lam ne. lam as.
  use PMExprAst in
  TmParallelReduce {f = f, ne = ne, as = as, ty = tyunknown_, info = NoInfo ()}

let loop_ = lam n. lam f.
  use PMExprAst in
  TmLoop {n = n, f = f, ty = tyunknown_, info = NoInfo ()}

let loopAcc_ = lam ne. lam n. lam f.
  use PMExprAst in
  TmLoopAcc {ne = ne, n = n, f = f, ty = tyunknown_, info = NoInfo ()}

let parallelLoop_ = lam n. lam f.
  use PMExprAst in
  TmParallelLoop {n = n, f = f, ty = tyunknown_, info = NoInfo ()}

let parallelSizeCoercion_ = lam e. lam size.
  use PMExprAst in
  TmParallelSizeCoercion {e = e, size = size, ty = tyunknown_, info = NoInfo ()}

let parallelSizeEquality_ = lam x1. lam d1. lam x2. lam d2.
  use PMExprAst in
  TmParallelSizeEquality {x1 = x1, d1 = d1, x2 = x2, d2 = d2,
                          ty = tyunknown_, info = NoInfo ()}

let printFloat_ = lam e.
  use PMExprAst in
  TmPrintFloat {e = e, ty = tyunknown_, info = NoInfo ()}

mexpr

use PMExprAst in

let id_ = ulam_ "x" (var_ "x") in
let singleton_ = ulam_ "x" (seq_ [var_ "x"]) in
let trueFunc_ = ulam_ "x" true_ in
let emptySeq_ = seq_ [] in
let zip_ = ulam_ "x" (ulam_ "y" (utuple_ [var_ "x", var_ "y"])) in
let unitfn_ = ulam_ "x" unit_ in
let addfn_ = ulam_ "acc" (ulam_ "i" (addi_ (var_ "acc") (var_ "i"))) in

let expr = app_ (var_ "accelerate") (app_ id_ (int_ 2)) in
utest makeKeywords expr with accelerate_ (app_ id_ (int_ 2)) using eqExpr in

let expr = app_ (var_ "flatten") emptySeq_ in
utest makeKeywords expr with flatten_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "map2") zip_ emptySeq_ emptySeq_ in
utest makeKeywords expr with map2_ zip_ emptySeq_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "reduce") id_ (int_ 0) emptySeq_ in
utest makeKeywords expr with parallelReduce_ id_ (int_ 0) emptySeq_ using eqExpr in

let expr = appf2_ (var_ "seqLoop") (int_ 10) unitfn_ in
utest makeKeywords expr with loop_ (int_ 10) unitfn_ using eqExpr in

let expr = appf3_ (var_ "seqLoopAcc") (int_ 0) (int_ 10) addfn_ in
utest makeKeywords expr with loopAcc_ (int_ 0) (int_ 10) addfn_ using eqExpr in

let expr = appf2_ (var_ "loop") (int_ 10) unitfn_ in
utest makeKeywords expr with parallelLoop_ (int_ 10) unitfn_ using eqExpr in

let expr = app_ (var_ "printFloat") (float_ 3.14) in
utest makeKeywords expr with printFloat_ (float_ 3.14) using eqExpr in

()
