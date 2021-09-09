include "mexpr/anf.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"

lang MExprParallelKeywordMaker =
  KeywordMaker + MExprAst + MExprEq + MExprANF

  syn Expr =
  | TmAccelerate {e : Expr, ty : Type, info : Info}
  | TmParallelMap {f: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelMap2 {f: Expr, as: Expr, bs: Expr, ty: Type, info: Info}
  | TmParallelFlatMap {f: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelReduce {f: Expr, ne: Expr, as: Expr, ty: Type, info: Info}

  sem isKeyword =
  | TmAccelerate _ -> true
  | TmParallelMap _ -> true
  | TmParallelMap2 _ -> true
  | TmParallelFlatMap _ -> true
  | TmParallelReduce _ -> true

  sem matchKeywordString (info : Info) =
  | "accelerate" ->
    Some (1, lam lst. TmAccelerate {e = get lst 0, ty = TyUnknown {info = info},
                                    info = info})
  | "parallelMap" ->
    Some (2, lam lst. TmParallelMap {f = get lst 0, as = get lst 1,
                                     ty = TyUnknown {info = info}, info = info})
  | "parallelMap2" ->
    Some (3, lam lst. TmParallelMap2 {f = get lst 0, as = get lst 1,
                                      bs = get lst 2,
                                      ty = TyUnknown {info = info}, info = info})
  | "parallelFlatMap" ->
    Some (2, lam lst. TmParallelFlatMap {f = get lst 0, as = get lst 1,
                                         ty = TyUnknown {info = info},
                                         info = info})
  | "parallelReduce" ->
    Some (3, lam lst. TmParallelReduce {f = get lst 0, ne = get lst 1,
                                        as = get lst 2, ty = TyUnknown {info = info},
                                        info = info})

  sem ty =
  | TmAccelerate t -> t.ty
  | TmParallelMap t -> t.ty
  | TmParallelMap2 t -> t.ty
  | TmParallelFlatMap t -> t.ty
  | TmParallelReduce t -> t.ty

  sem withType (ty : Type) =
  | TmAccelerate t -> TmAccelerate {t with ty = ty}
  | TmParallelMap t -> TmParallelMap {t with ty = ty}
  | TmParallelMap2 t -> TmParallelMap2 {t with ty = ty}
  | TmParallelFlatMap t -> TmParallelFlatMap {t with ty = ty}
  | TmParallelReduce t -> TmParallelReduce {t with ty = ty}

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
  | TmAccelerate t ->
    match f acc t.e with (acc, e) then
      (acc, TmAccelerate {t with e = e})
    else never
  | TmParallelMap t ->
    match f acc t.f with (acc, tf) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelMap {{t with f = tf} with as = as})
      else never
    else never
  | TmParallelMap2 t ->
    match f acc t.f with (acc, tf) then
      match f acc t.as with (acc, as) then
        match f acc t.bs with (acc, bs) then
          (acc, TmParallelMap2 {{{t with f = tf} with as = as} with bs = bs})
        else never
      else never
    else never
  | TmParallelFlatMap t ->
    match f acc t.f with (acc, tf) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelFlatMap {{t with f = tf} with as = as})
      else never
    else never
  | TmParallelReduce t ->
    match f acc t.f with (acc, tf) then
      match f acc t.ne with (acc, ne) then
        match f acc t.as with (acc, as) then
          (acc, TmParallelReduce {{{t with f = tf} with ne = ne} with as = as})
        else never
      else never
    else never

  sem typeAnnotExpr (env : TypeEnv) =
  | TmAccelerate t ->
    let e = typeAnnotExpr env t.e in
    TmAccelerate {{t with e = e}
                     with ty = ty e}
  | TmParallelMap t ->
    let f = typeAnnotExpr env t.f in
    let elemTy =
      match ty f with TyArrow {to = to} then to
      else tyunknown_
    in
    TmParallelMap {{{t with f = f}
                       with as = typeAnnotExpr env t.as}
                       with ty = tyseq_ elemTy}
  | TmParallelMap2 t ->
    let f = typeAnnotExpr env t.f in
    let elemTy =
      match ty f with TyArrow {to = to} then to
      else tyunknown_
    in
    TmParallelMap2 {{{{t with f = f}
                         with as = typeAnnotExpr env t.as}
                         with bs = typeAnnotExpr env t.bs}
                         with ty = tyseq_ elemTy}
  | TmParallelFlatMap t ->
    let f = typeAnnotExpr env t.f in
    let targetSeqTy =
      match ty f with TyArrow {to = (TySeq _) & to} then to
      else tyseq_ tyunknown_
    in
    TmParallelFlatMap {{{t with f = f}
                           with as = typeAnnotExpr env t.as}
                           with ty = targetSeqTy}
  | TmParallelReduce t ->
    let ne = typeAnnotExpr env t.ne in
    TmParallelReduce {{{{t with f = typeAnnotExpr env t.f}
                           with ne = ne}
                           with as = typeAnnotExpr env t.as}
                           with ty = ty ne}

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmAccelerate r ->
    match lhs with TmAccelerate l then
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
  | TmParallelFlatMap r ->
    match lhs with TmParallelFlatMap l then
      match eqExprH env free l.f r.f with Some free then
        eqExprH env free l.as r.as
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

  sem isValue =
  | TmAccelerate _ -> false
  | TmParallelMap _ -> false
  | TmParallelMap2 _ -> false
  | TmParallelFlatMap _ -> false
  | TmParallelReduce _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmAccelerate t ->
    k (TmAccelerate {t with e = normalizeTerm t.e})
  | TmParallelMap t ->
    k (TmParallelMap {{t with f = normalizeTerm t.f}
                         with as = normalizeTerm t.as})
  | TmParallelMap2 t ->
    k (TmParallelMap2 {{{t with f = normalizeTerm t.f}
                           with as = normalizeTerm t.as}
                           with bs = normalizeTerm t.bs})
  | TmParallelFlatMap t ->
    k (TmParallelFlatMap {{t with f = normalizeTerm t.f}
                             with as = normalizeTerm t.as})
  | TmParallelReduce t ->
    k (TmParallelReduce {{{t with f = normalizeTerm t.f}
                             with ne = normalizeTerm t.ne}
                             with as = normalizeTerm t.as})
end

let accelerate_ = lam e.
  use MExprParallelKeywordMaker in
  TmAccelerate {e = e, ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

let parallelMap_ = lam f. lam as.
  use MExprParallelKeywordMaker in
  TmParallelMap {f = f, as = as, ty = TyUnknown {info = NoInfo ()},
                 info = NoInfo ()}
let parallelMap2_ = lam f. lam as. lam bs.
  use MExprParallelKeywordMaker in
  TmParallelMap2 {f = f, as = as, bs = bs, ty = TyUnknown {info = NoInfo ()},
                  info = NoInfo ()}
let parallelFlatMap_ = lam f. lam as.
  use MExprParallelKeywordMaker in
  TmParallelFlatMap {f = f, as = as, ty = TyUnknown {info = NoInfo ()},
                     info = NoInfo ()}
let parallelReduce_ = lam f. lam ne. lam as.
  use MExprParallelKeywordMaker in
  TmParallelReduce {f = f, ne = ne, as = as, ty = TyUnknown {info = NoInfo ()},
                    info = NoInfo ()}

mexpr

use MExprParallelKeywordMaker in

let id_ = ulam_ "x" (var_ "x") in
let singleton_ = ulam_ "x" (seq_ [var_ "x"]) in
let trueFunc_ = ulam_ "x" true_ in
let emptySeq_ = seq_ [] in
let zip_ = ulam_ "x" (ulam_ "y" (utuple_ [var_ "x", var_ "y"])) in

let expr = app_ (var_ "accelerate") (app_ id_ (int_ 2)) in
utest makeKeywords [] expr with accelerate_ (app_ id_ (int_ 2)) using eqExpr in

let expr = appf2_ (var_ "parallelMap") id_ emptySeq_ in
utest makeKeywords [] expr with parallelMap_ id_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelMap2") zip_ emptySeq_ emptySeq_ in
utest makeKeywords [] expr with parallelMap2_ zip_ emptySeq_ emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelFlatMap") singleton_ emptySeq_ in
utest makeKeywords [] expr with parallelFlatMap_ singleton_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelReduce") id_ (int_ 0) emptySeq_ in
utest makeKeywords [] expr with parallelReduce_ id_ (int_ 0) emptySeq_ using eqExpr in

()
