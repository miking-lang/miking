include "ast.mc"
include "eq.mc"
include "keyword-maker.mc"

lang MExprPatternKeywordMaker = KeywordMaker + MExpr + MExprEq
  syn Expr =
  | TmParallelMap {f: Expr, as: Expr, info: Info}
  | TmParallelReduce {f: Expr, ne: Expr, as: Expr, info: Info}
  | TmParallelScan {f: Expr, ne: Expr, as: Expr, info: Info}
  | TmParallelFilter {p: Expr, as: Expr, info: Info}
  | TmParallelPartition {p: Expr, as: Expr, info: Info}
  | TmParallelAll {p: Expr, as: Expr, info: Info}
  | TmParallelAny {p: Expr, as: Expr, info: Info}

  sem isKeyword =
  | TmParallelMap _ -> true
  | TmParallelReduce _ -> true
  | TmParallelScan _ -> true
  | TmParallelFilter _ -> true
  | TmParallelPartition _ -> true
  | TmParallelAll _ -> true
  | TmParallelAny _ -> true

  sem matchKeywordString (info : Info) =
  | "parallelMap" ->
    Some (2, lam lst. TmParallelMap {f = get lst 0, as = get lst 1, info = info})
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
        eqExprH env free l.s r.s
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

let expr = ulam_ "x" (appf2_ (var_ "parallelMap") (ulam_ "x" (var_ "x")) (seq_ [])) in
dprintLn (makeKeywords [] expr)
