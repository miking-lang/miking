include "mexpr/anf.mc"
include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"

lang MExprParallelKeywordMaker =
  KeywordMaker + MExprAst + MExprEq + MExprANF

  syn Expr =
  | TmParallelMap {f: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelMap2 {f: Expr, as: Expr, bs: Expr, ty: Type, info: Info}
  | TmParallelReduce {f: Expr, ne: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelScan {f: Expr, ne: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelFilter {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelPartition {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelAll {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelAny {p: Expr, as: Expr, ty: Type, info: Info}
  | TmFlatten {s: Expr, ty: Type, info: Info}
  | TmSequentialFor {body: Expr, init: Expr, n: Expr, ty: Type, info: Info}

  sem isKeyword =
  | TmParallelMap _ -> true
  | TmParallelMap2 _ -> true
  | TmParallelReduce _ -> true
  | TmParallelScan _ -> true
  | TmParallelFilter _ -> true
  | TmParallelPartition _ -> true
  | TmParallelAll _ -> true
  | TmParallelAny _ -> true
  | TmFlatten _ -> true
  | TmSequentialFor _ -> true

  sem matchKeywordString (info : Info) =
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
  | "parallelScan" ->
    Some (3, lam lst. TmParallelScan {f = get lst 0, ne = get lst 1,
                                      as = get lst 2, ty = TyUnknown {info = info},
                                      info = info})
  | "parallelFilter" ->
    Some (2, lam lst. TmParallelFilter {p = get lst 0, as = get lst 1,
                                        ty = TyUnknown {info = info}, info = info})
  | "parallelPartition" ->
    Some (2, lam lst. TmParallelPartition {p = get lst 0, as = get lst 1,
                                           ty = TyUnknown {info = info}, info = info})
  | "parallelAll" ->
    Some (2, lam lst. TmParallelAll {p = get lst 0, as = get lst 1,
                                     ty = TyUnknown {info = info}, info = info})
  | "parallelAny" ->
    Some (2, lam lst. TmParallelAny {p = get lst 0, as = get lst 1,
                                     ty = TyUnknown {info = info}, info = info})
  | "flatten" ->
    Some (1, lam lst. TmFlatten {s = get lst 0, ty = TyUnknown {info = info},
                                 info = info})
  | "for" ->
    Some (3, lam lst. TmSequentialFor {body = get lst 0, init = get lst 1,
                                       n = get lst 2, ty = TyUnknown {info = info},
                                       info = info})

  sem ty =
  | TmParallelMap t -> t.ty
  | TmParallelMap2 t -> t.ty
  | TmParallelReduce t -> t.ty
  | TmParallelScan t -> t.ty
  | TmParallelFilter t -> t.ty
  | TmParallelPartition t -> t.ty
  | TmParallelAll t -> t.ty
  | TmParallelAny t -> t.ty
  | TmFlatten t -> t.ty
  | TmSequentialFor t -> t.ty

  sem smapAccumL_Expr_Expr (f : acc -> a -> (acc, b)) (acc : acc) =
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
  | TmParallelReduce t ->
    match f acc t.f with (acc, tf) then
      match f acc t.ne with (acc, ne) then
        match f acc t.as with (acc, as) then
          (acc, TmParallelReduce {{{t with f = tf} with ne = ne} with as = as})
        else never
      else never
    else never
  | TmParallelScan t ->
    match f acc t.f with (acc, tf) then
      match f acc t.ne with (acc, ne) then
        match f acc t.as with (acc, as) then
          (acc, TmParallelScan {{{t with f = tf} with ne = ne} with as = as})
        else never
      else never
    else never
  | TmParallelFilter t ->
    match f acc t.p with (acc, p) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelFilter {{t with p = p} with as = as})
      else never
    else never
  | TmParallelPartition t ->
    match f acc t.p with (acc, p) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelPartition {{t with p = p} with as = as})
      else never
    else never
  | TmParallelAll t ->
    match f acc t.p with (acc, p) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelAll {{t with p = p} with as = as})
      else never
    else never
  | TmParallelAny t ->
    match f acc t.p with (acc, p) then
      match f acc t.as with (acc, as) then
        (acc, TmParallelAny {{t with p = p} with as = as})
      else never
    else never
  | TmFlatten t ->
    match f acc t.s with (acc, s) then
      (acc, TmFlatten {t with s = s})
    else never
  | TmSequentialFor t ->
    match f acc t.body with (acc, body) then
      match f acc t.init with (acc, init) then
        match f acc t.n with (acc, n) then
          (acc, TmSequentialFor {{{t with body = body}
                                     with init = init}
                                     with n = n})
        else never
      else never
    else never

  sem symbolizeExpr (env : SymEnv) =
  | (TmParallelMap _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelMap2 _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelReduce _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelScan _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelFilter _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelPartition _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelAll _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelAny _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmFlatten _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmSequentialFor _) & t -> smap_Expr_Expr (symbolizeExpr env) t

  sem typeAnnotExpr (env : TypeEnv) =
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
  | TmParallelReduce t ->
    let ne = typeAnnotExpr env t.ne in
    TmParallelReduce {{{{t with f = typeAnnotExpr env t.f}
                           with ne = ne}
                           with as = typeAnnotExpr env t.as}
                           with ty = ty ne}
  | TmParallelScan t ->
    let ne = typeAnnotExpr env t.ne in
    TmParallelScan {{{{t with f = typeAnnotExpr env t.f}
                         with ne = ne}
                         with as = typeAnnotExpr env t.as}
                         with ty = ty ne}
  | TmParallelFilter t ->
    let as = typeAnnotExpr env t.as in
    TmParallelFilter {{{t with p = typeAnnotExpr env t.p}
                          with as = as}
                          with ty = ty as}
  | TmParallelPartition t ->
    let p = typeAnnotExpr env t.p in
    let ty =
      match ty p with TyArrow {from = from} then from
      else tyunknown_
    in
    TmParallelPartition {{{t with p = p}
                             with as = typeAnnotExpr env t.as}
                             with ty = tytuple_ [tyseq_ ty, tyseq_ ty]}
  | TmParallelAll t ->
    TmParallelAll {{{t with p = typeAnnotExpr env t.p}
                       with as = typeAnnotExpr env t.as}
                       with ty = tybool_}
  | TmParallelAny t ->
    TmParallelAny {{{t with p = typeAnnotExpr env t.p}
                       with as = typeAnnotExpr env t.as}
                       with ty = tybool_}
  | TmFlatten t ->
    let s = typeAnnotExpr env t.s in
    let ty =
      match ty s with TySeq {ty = TySeq {ty = elemTy}} then
        elemTy
      else tyunknown_
    in
    TmFlatten {{t with s = typeAnnotExpr env t.s}
                  with ty = tyseq_ ty}
  | TmSequentialFor t ->
    let body = typeAnnotExpr env t.body in
    let init = typeAnnotExpr env t.init in
    let n = typeAnnotExpr env t.n in
    TmSequentialFor {{{{t with body = body}
                          with init = init}
                          with n = n}
                          with ty = ty body}

  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
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
  | TmParallelScan r ->
    match lhs with TmParallelScan l then
      match eqExprH env free l.f r.f with Some free then
        match eqExprH env free l.ne r.ne with Some free then
          eqExprH env free l.as r.as
        else None ()
      else None ()
    else None ()
  | TmParallelFilter r ->
    match lhs with TmParallelFilter l then
      match eqExprH env free l.p r.p with Some free then
        eqExprH env free l.as r.as
      else None ()
    else None ()
  | TmParallelPartition r ->
    match lhs with TmParallelPartition l then
      match eqExprH env free l.p r.p with Some free then
        eqExprH env free l.as r.as
      else None ()
    else None ()
  | TmParallelAll r ->
    match lhs with TmParallelAll l then
      match eqExprH env free l.p r.p with Some free then
        eqExprH env free l.as r.as
      else None ()
    else None ()
  | TmParallelAny r ->
    match lhs with TmParallelAny l then
      match eqExprH env free l.p r.p with Some free then
        eqExprH env free l.as r.as
      else None ()
    else None ()
  | TmFlatten r ->
    match lhs with TmFlatten l then
      eqExprH env free l.s r.s
    else None ()
  | TmSequentialFor r ->
    match lhs with TmSequentialFor l then
      match eqExprH env free l.body r.body with Some free then
        match eqExprH env free l.init r.init with Some free then
          eqExprH env free l.n r.n
        else None ()
      else None ()
    else None ()

  sem isValue =
  | TmParallelMap _ -> false
  | TmParallelMap2 _ -> false
  | TmParallelReduce _ -> false
  | TmParallelScan _ -> false
  | TmParallelFilter _ -> false
  | TmParallelPartition _ -> false
  | TmParallelAll _ -> false
  | TmParallelAny _ -> false
  | TmFlatten _ -> false
  | TmSequentialFor _ -> false

  sem normalize (k : Expr -> Expr) =
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
  | TmParallelScan t ->
    k (TmParallelScan {{{t with f = normalizeTerm t.f}
                           with ne = normalizeTerm t.ne}
                           with as = normalizeTerm t.as})
  | TmParallelFilter t ->
    k (TmParallelFilter {{t with p = normalizeTerm t.p}
                            with as = normalizeTerm t.as})
  | TmParallelPartition t ->
    k (TmParallelPartition {{t with p = normalizeTerm t.p}
                               with as = normalizeTerm t.as})
  | TmParallelAll t ->
    k (TmParallelAll {{t with p = normalizeTerm t.p}
                         with as = normalizeTerm t.as})
  | TmParallelAny t ->
    k (TmParallelAny {{t with p = normalizeTerm t.p}
                          with as = normalizeTerm t.as})
  | TmFlatten t -> k (TmFlatten {t with s = normalizeTerm t.s})
  | TmSequentialFor t ->
    k (TmSequentialFor {{{t with body = normalizeTerm t.body}
                            with init = normalizeTerm t.init}
                            with n = normalizeTerm t.n})
end

let parallelMap_ = lam f. lam as.
  use MExprParallelKeywordMaker in
  TmParallelMap {f = f, as = as, ty = TyUnknown {info = NoInfo ()},
                 info = NoInfo ()}
let parallelMap2_ = lam f. lam as. lam bs.
  use MExprParallelKeywordMaker in
  TmParallelMap2 {f = f, as = as, bs = bs, ty = TyUnknown {info = NoInfo ()},
                  info = NoInfo ()}
let parallelReduce_ = lam f. lam ne. lam as.
  use MExprParallelKeywordMaker in
  TmParallelReduce {f = f, ne = ne, as = as, ty = TyUnknown {info = NoInfo ()},
                    info = NoInfo ()}
let parallelScan_ = lam f. lam ne. lam as.
  use MExprParallelKeywordMaker in
  TmParallelScan {f = f, ne = ne, as = as, ty = TyUnknown {info = NoInfo ()},
                  info = NoInfo ()}
let parallelFilter_ = lam p. lam as.
  use MExprParallelKeywordMaker in
  TmParallelFilter {p = p, as = as, ty = TyUnknown {info = NoInfo ()},
                    info = NoInfo ()}
let parallelPartition_ = lam p. lam as.
  use MExprParallelKeywordMaker in
  TmParallelPartition {p = p, as = as, ty = TyUnknown {info = NoInfo ()},
                       info = NoInfo ()}
let parallelAll_ = lam p. lam as.
  use MExprParallelKeywordMaker in
  TmParallelAll {p = p, as = as, ty = TyUnknown {info = NoInfo ()},
                 info = NoInfo ()}
let parallelAny_ = lam p. lam as.
  use MExprParallelKeywordMaker in
  TmParallelAny {p = p, as = as, ty = TyUnknown {info = NoInfo ()},
                 info = NoInfo ()}
let flatten_ = lam s.
  use MExprParallelKeywordMaker in
  TmFlatten {s = s, ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

let sequentialFor_ = lam body. lam init. lam n.
  use MExprParallelKeywordMaker in
  TmSequentialFor {body = body, init = init, n = n,
                   ty = TyUnknown {info = NoInfo ()}, info = NoInfo ()}

mexpr

use MExprParallelKeywordMaker in

let id_ = ulam_ "x" (var_ "x") in
let trueFunc_ = ulam_ "x" true_ in
let emptySeq_ = seq_ [] in
let zip_ = ulam_ "x" (ulam_ "y" (utuple_ [var_ "x", var_ "y"])) in

let expr = appf2_ (var_ "parallelMap") id_ emptySeq_ in
utest makeKeywords [] expr with parallelMap_ id_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelMap2") zip_ emptySeq_ emptySeq_ in
utest makeKeywords [] expr with parallelMap2_ zip_ emptySeq_ emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelReduce") id_ (int_ 0) emptySeq_ in
utest makeKeywords [] expr with parallelReduce_ id_ (int_ 0) emptySeq_ using eqExpr in

let expr = appf3_ (var_ "parallelScan") id_ (int_ 0) emptySeq_ in
utest makeKeywords [] expr with parallelScan_ id_ (int_ 0) emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelFilter") trueFunc_ emptySeq_ in
utest makeKeywords [] expr with parallelFilter_ trueFunc_ emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelPartition") trueFunc_ emptySeq_ in
utest makeKeywords [] expr with parallelPartition_ trueFunc_ emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelAll") trueFunc_ emptySeq_ in
utest makeKeywords [] expr with parallelAll_ trueFunc_ emptySeq_ using eqExpr in

let expr = appf2_ (var_ "parallelAny") trueFunc_ emptySeq_ in
utest makeKeywords [] expr with parallelAny_ trueFunc_ emptySeq_ using eqExpr in

let s = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in
let expr = app_ (var_ "flatten") s in
utest makeKeywords [] expr with flatten_ s using eqExpr in

let s = seq_ [int_ 1, int_ 2, int_ 3] in
let expr = app_ (var_ "indices") s in
utest makeKeywords [] expr with indices_ s using eqExpr in

()
