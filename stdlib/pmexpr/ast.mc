include "mexpr/anf.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"

lang PMExprAst = KeywordMaker + MExprAst + MExprEq + MExprANF + MExprTypeAnnot

  syn Expr =
  | TmAccelerate {e : Expr, ty : Type, info : Info}
  | TmFlatten {e : Expr, ty : Type, info : Info}
  | TmParallelMap {f : Expr, as : Expr, ty : Type, info : Info}
  | TmParallelMap2 {f : Expr, as : Expr, bs : Expr, ty : Type, info : Info}
  | TmParallelReduce {f : Expr, ne : Expr, as : Expr, ty : Type, info : Info}
  | TmParallelSizeCoercion {e: Expr, size : Name, ty : Type, info : Info}
  | TmParallelSizeEquality {x1: Name, d1: Int, x2: Name, d2: Int, ty : Type, info : Info}

  sem isKeyword =
  | TmAccelerate _ -> true
  | TmFlatten _ -> true
  | TmParallelMap _ -> true
  | TmParallelMap2 _ -> true
  | TmParallelReduce _ -> true

  sem matchKeywordString (info : Info) =
  | "accelerate" ->
    Some (1, lam lst. TmAccelerate {e = get lst 0, ty = TyUnknown {info = info},
                                    info = info})
  | "parallelFlatten" ->
    Some (1, lam lst. TmFlatten {e = get lst 0, ty = TyUnknown {info = info},
                                 info = info})
  | "parallelMap" ->
    Some (2, lam lst. TmParallelMap {f = get lst 0, as = get lst 1,
                                     ty = TyUnknown {info = info}, info = info})
  | "parallelMap2" ->
    Some (3, lam lst. TmParallelMap2 {f = get lst 0, as = get lst 1,
                                      bs = get lst 2,
                                      ty = TyUnknown {info = info}, info = info})
  | "parallelReduce" ->
    Some (3, lam lst. TmParallelReduce {f = get lst 0, ne = get lst 1,
                                        as = get lst 2, ty = TyUnknown {info = info},
                                        info = info})

  sem tyTm =
  | TmAccelerate t -> t.ty
  | TmFlatten t -> t.ty
  | TmParallelMap t -> t.ty
  | TmParallelMap2 t -> t.ty
  | TmParallelReduce t -> t.ty
  | TmParallelSizeCoercion t -> t.ty
  | TmParallelSizeEquality t -> t.ty

  sem infoTm =
  | TmAccelerate t -> t.info
  | TmFlatten t -> t.info
  | TmParallelMap t -> t.info
  | TmParallelMap2 t -> t.info
  | TmParallelReduce t -> t.info
  | TmParallelSizeCoercion t -> t.info
  | TmParallelSizeEquality t -> t.info

  sem withType (ty : Type) =
  | TmAccelerate t -> TmAccelerate {t with ty = ty}
  | TmFlatten t -> TmFlatten {t with ty = ty}
  | TmParallelMap t -> TmParallelMap {t with ty = ty}
  | TmParallelMap2 t -> TmParallelMap2 {t with ty = ty}
  | TmParallelReduce t -> TmParallelReduce {t with ty = ty}
  | TmParallelSizeCoercion t -> TmParallelSizeCoercion {t with ty = ty}
  | TmParallelSizeEquality t -> TmParallelSizeEquality {t with ty = ty}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmAccelerate t ->
    match f acc t.e with (acc, e) in
    (acc, TmAccelerate {t with e = e})
  | TmFlatten t ->
    match f acc t.e with (acc, e) in
    (acc, TmFlatten {t with e = e})
  | TmParallelMap t ->
    match f acc t.f with (acc, tf) in
    match f acc t.as with (acc, as) in
    (acc, TmParallelMap {{t with f = tf} with as = as})
  | TmParallelMap2 t ->
    match f acc t.f with (acc, tf) in
    match f acc t.as with (acc, as) in
    match f acc t.bs with (acc, bs) in
    (acc, TmParallelMap2 {{{t with f = tf} with as = as} with bs = bs})
  | TmParallelReduce t ->
    match f acc t.f with (acc, tf) in
    match f acc t.ne with (acc, ne) in
    match f acc t.as with (acc, as) in
    (acc, TmParallelReduce {{{t with f = tf} with ne = ne} with as = as})
  | TmParallelSizeCoercion t ->
    match f acc t.e with (acc, e) in
    (acc, TmParallelSizeCoercion {t with e = e})

  sem typeAnnotExpr (env : TypeEnv) =
  | TmAccelerate t ->
    let e = typeAnnotExpr env t.e in
    let ty =
      optionGetOrElse
        (lam. tyTm e)
        (compatibleType env.tyEnv (tyTm e) t.ty) in
    TmAccelerate {{t with e = e} with ty = ty}
  | TmFlatten t ->
    let e = typeAnnotExpr env t.e in
    let ty =
      match tyTm e with TySeq {ty = TySeq {ty = elemTy, info = info}} then
        TySeq {ty = elemTy, info = info}
      else TyUnknown {info = infoTm e} in
    TmFlatten {{t with e = e} with ty = ty}
  | TmParallelMap t ->
    let f = typeAnnotExpr env t.f in
    let elemTy =
      match tyTm f with TyArrow {to = to} then to
      else tyunknown_ in
    TmParallelMap {{{t with f = f}
                       with as = typeAnnotExpr env t.as}
                       with ty = tyseq_ elemTy}
  | TmParallelMap2 t ->
    let f = typeAnnotExpr env t.f in
    let elemTy =
      match tyTm f with TyArrow {to = TyArrow {to = to}} then to
      else tyunknown_ in
    TmParallelMap2 {{{{t with f = f}
                         with as = typeAnnotExpr env t.as}
                         with bs = typeAnnotExpr env t.bs}
                         with ty = tyseq_ elemTy}
  | TmParallelReduce t ->
    let ne = typeAnnotExpr env t.ne in
    TmParallelReduce {{{{t with f = typeAnnotExpr env t.f}
                           with ne = ne}
                           with as = typeAnnotExpr env t.as}
                           with ty = tyTm ne}
  | TmParallelSizeCoercion t ->
    let e = typeAnnotExpr env t.e in
    TmParallelSizeCoercion {{t with e = e} with ty = tyTm e}
  | TmParallelSizeEquality t ->
    let ty = tyWithInfo t.info tyunit_ in
    TmParallelSizeEquality {t with ty = ty}

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmAccelerate r ->
    match lhs with TmAccelerate l then
      eqExprH env free l.e r.e
    else None ()
  | TmFlatten r ->
    match lhs with TmFlatten l then
      eqExprH env free l.e r.e
    else None ()
  | TmParallelMap r ->
    match lhs with TmParallelMap l then
      match eqExprH env free l.f r.f with Some free then
        eqExprH env free l.as r.as
      else None ()
    else None ()
  | TmParallelMap2 r ->
    match lhs with TmParallelMap2 l then
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
    k (TmFlatten {t with e = normalizeTerm t.e})
  | TmParallelMap t ->
    k (TmParallelMap {{t with f = normalizeTerm t.f}
                         with as = normalizeTerm t.as})
  | TmParallelMap2 t ->
    k (TmParallelMap2 {{{t with f = normalizeTerm t.f}
                           with as = normalizeTerm t.as}
                           with bs = normalizeTerm t.bs})
  | TmParallelReduce t ->
    k (TmParallelReduce {{{t with f = normalizeTerm t.f}
                             with ne = normalizeTerm t.ne}
                             with as = normalizeTerm t.as})
  | TmParallelSizeCoercion t ->
    k (TmParallelSizeCoercion {t with e = normalizeTerm t.e})
  | TmParallelSizeEquality t -> k (TmParallelSizeEquality t)
end

let accelerate_ = lam e.
  use PMExprAst in
  TmAccelerate {e = e, ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

let flatten_ = lam e.
  use PMExprAst in
  TmFlatten {e = e, ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

let parallelMap_ = lam f. lam as.
  use PMExprAst in
  TmParallelMap {f = f, as = as, ty = TyUnknown {info = NoInfo ()},
                 info = NoInfo ()}

let parallelMap2_ = lam f. lam as. lam bs.
  use PMExprAst in
  TmParallelMap2 {f = f, as = as, bs = bs, ty = TyUnknown {info = NoInfo ()},
                  info = NoInfo ()}

let parallelReduce_ = lam f. lam ne. lam as.
  use PMExprAst in
  TmParallelReduce {f = f, ne = ne, as = as, ty = TyUnknown {info = NoInfo ()},
                    info = NoInfo ()}

let parallelSizeCoercion_ = lam e. lam size.
  use PMExprAst in
  TmParallelSizeCoercion {e = e, size = size, ty = TyUnknown {info = NoInfo ()},
                          info = NoInfo ()}

let parallelSizeEquality_ = lam x1. lam d1. lam x2. lam d2.
  use PMExprAst in
  TmParallelSizeEquality {x1 = x1, d1 = d1, x2 = x2, d2 = d2,
                          ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

mexpr

use PMExprAst in

let id_ = ulam_ "x" (var_ "x") in
let singleton_ = ulam_ "x" (seq_ [var_ "x"]) in
let trueFunc_ = ulam_ "x" true_ in
let emptySeq_ = seq_ [] in
let zip_ = ulam_ "x" (ulam_ "y" (utuple_ [var_ "x", var_ "y"])) in

let expr = app_ (var_ "accelerate") (app_ id_ (int_ 2)) in
utest makeKeywords [] expr with accelerate_ (app_ id_ (int_ 2)) using eqExpr in

let expr = app_ (var_ "parallelFlatten") emptySeq_ in
utest makeKeywords [] expr with flatten_ emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelMap") id_ emptySeq_ in
utest makeKeywords [] expr with parallelMap_ id_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelMap2") zip_ emptySeq_ emptySeq_ in
utest makeKeywords [] expr with parallelMap2_ zip_ emptySeq_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelReduce") id_ (int_ 0) emptySeq_ in
utest makeKeywords [] expr with parallelReduce_ id_ (int_ 0) emptySeq_ using eqExpr in

()
