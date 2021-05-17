include "ast.mc"
include "eq.mc"
include "keyword-maker.mc"

lang MExprPatternKeywordMaker = KeywordMaker + MExprAst + MExprEq
  syn Expr =
  | TmParallelMap {f: Expr, as: Expr, info: Info}
  | TmParallelMap2 {f: Expr, as: Expr, bs: Expr, info: Info}
  | TmParallelReduce {f: Expr, ne: Expr, as: Expr, info: Info}
  | TmParallelScan {f: Expr, ne: Expr, as: Expr, info: Info}
  | TmParallelFilter {p: Expr, as: Expr, info: Info}
  | TmParallelPartition {p: Expr, as: Expr, info: Info}
  | TmParallelAll {p: Expr, as: Expr, info: Info}
  | TmParallelAny {p: Expr, as: Expr, info: Info}

  sem isKeyword =
  | TmParallelMap _ -> true
  | TmParallelMap2 _ -> true
  | TmParallelReduce _ -> true
  | TmParallelScan _ -> true
  | TmParallelFilter _ -> true
  | TmParallelPartition _ -> true
  | TmParallelAll _ -> true
  | TmParallelAny _ -> true

  sem matchKeywordString (info : Info) =
  | "parallelMap" ->
    Some (2, lam lst. TmParallelMap {f = get lst 0, as = get lst 1, info = info})
  | "parallelMap2" ->
    Some (3, lam lst. TmParallelMap2 {f = get lst 0, as = get lst 1,
                                      bs = get lst 2, info = info})
  | "parallelReduce" ->
    Some (3, lam lst. TmParallelReduce {f = get lst 0, ne = get lst 1,
                                        as = get lst 2, info = info})
  | "parallelScan" ->
    Some (3, lam lst. TmParallelScan {f = get lst 0, ne = get lst 1,
                                      as = get lst 2, info = info})
  | "parallelFilter" ->
    Some (2, lam lst. TmParallelFilter {p = get lst 0, as = get lst 1, info = info})
  | "parallelPartition" ->
    Some (2, lam lst. TmParallelPartition {p = get lst 0, as = get lst 1, info = info})
  | "parallelAll" ->
    Some (2, lam lst. TmParallelAll {p = get lst 0, as = get lst 1, info = info})
  | "parallelAny" ->
    Some (2, lam lst. TmParallelAny {p = get lst 0, as = get lst 1, info = info})

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmParallelMap t -> TmParallelMap {{t with f = f t.f}
                                         with as = f t.as}
  | TmParallelMap2 t -> TmParallelMap2 {{{t with f = f t.f}
                                            with as = f t.as}
                                            with bs = f t.bs}
  | TmParallelReduce t -> TmParallelReduce {{{t with f = f t.f}
                                                with ne = f t.ne}
                                                with as = f t.as}
  | TmParallelScan t -> TmParallelScan {{{t with f = f t.f}
                                            with ne = f t.ne}
                                            with as = f t.as}
  | TmParallelFilter t -> TmParallelFilter {{t with p = f t.p}
                                               with as = f t.as}
  | TmParallelPartition t -> TmParallelPartition {{t with p = f t.p}
                                                     with as = f t.as}
  | TmParallelAll t -> TmParallelAll {{t with p = f t.p}
                                         with as = f t.as}
  | TmParallelAny t -> TmParallelAny {{t with p = f t.p}
                                         with as = f t.as}

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
end

mexpr

use MExprPatternKeywordMaker in

let parallelMap_ = lam f. lam as.
  TmParallelMap {f = f, as = as, info = NoInfo ()} in
let parallelMap2_ = lam f. lam as. lam bs.
  TmParallelMap2 {f = f, as = as, bs = bs, info = NoInfo ()} in
let parallelReduce_ = lam f. lam ne. lam as.
  TmParallelReduce {f = f, ne = ne, as = as, info = NoInfo ()} in
let parallelScan_ = lam f. lam ne. lam as.
  TmParallelScan {f = f, ne = ne, as = as, info = NoInfo ()} in
let parallelFilter_ = lam p. lam as.
  TmParallelFilter {p = p, as = as, info = NoInfo ()} in
let parallelPartition_ = lam p. lam as.
  TmParallelPartition {p = p, as = as, info = NoInfo ()} in
let parallelAll_ = lam p. lam as.
  TmParallelAll {p = p, as = as, info = NoInfo ()} in
let parallelAny_ = lam p. lam as.
  TmParallelAny {p = p, as = as, info = NoInfo ()} in

let id_ = ulam_ "x" (var_ "x") in
let trueFunc_ = ulam_ "x" true_ in
let emptySeq_ = seq_ [] in

let expr = appf2_ (var_ "parallelMap") id_ emptySeq_ in
utest makeKeywords [] expr with parallelMap_ id_ emptySeq_ using eqExpr in

let zip_ = ulam_ "x" (ulam_ "y" (tuple_ [var_ "x", var_ "y"])) in
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

()
