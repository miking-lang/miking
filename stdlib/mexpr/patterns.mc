include "mexpr/ast.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/pprint.mc"
include "mexpr/type-annot.mc"

lang MExprParallelKeywordMaker =
  KeywordMaker + MExprAst + MExprEq + MExprPrettyPrint

  syn Expr =
  | TmParallelMap {f: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelMap2 {f: Expr, as: Expr, bs: Expr, ty: Type, info: Info}
  | TmParallelReduce {f: Expr, ne: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelScan {f: Expr, ne: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelFilter {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelPartition {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelAll {p: Expr, as: Expr, ty: Type, info: Info}
  | TmParallelAny {p: Expr, as: Expr, ty: Type, info: Info}

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

  sem ty =
  | TmParallelMap t -> t.ty
  | TmParallelMap2 t -> t.ty
  | TmParallelReduce t -> t.ty
  | TmParallelScan t -> t.ty
  | TmParallelFilter t -> t.ty
  | TmParallelPartition t -> t.ty
  | TmParallelAll t -> t.ty
  | TmParallelAny t -> t.ty

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

  sem symbolizeExpr (env : SymEnv) =
  | (TmParallelMap _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelMap2 _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelReduce _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelScan _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelFilter _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelPartition _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelAll _) & t -> smap_Expr_Expr (symbolizeExpr env) t
  | (TmParallelAny _) & t -> smap_Expr_Expr (symbolizeExpr env) t

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

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmParallelMap t ->
    match pprintCode indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelMap ", f, " ", as])
      else never
    else never
  | TmParallelMap2 t ->
    match pprintCode indent env t.f with (env, f) then
      match pprintCode indent env t.as with (env, as) then
        match pprintCode indent env t.bs with (env, bs) then
          (env, join ["parallelMap2 ", f, " ", as, " ", bs])
        else never
      else never
    else never
  | TmParallelReduce t ->
    match pprintCode indent env t.f with (env, f) then
      match pprintCode indent env t.ne with (env, ne) then
        match pprintCode indent env t.as with (env, as) then
          (env, join ["parallelReduce ", f, " ", ne, " ", as])
        else never
      else never
    else never
  | TmParallelScan t ->
    match pprintCode indent env t.f with (env, f) then
      match pprintCode indent env t.ne with (env, ne) then
        match pprintCode indent env t.as with (env, as) then
          (env, join ["parallelScan ", f, " ", ne, " ", as])
        else never
      else never
    else never
  | TmParallelFilter t ->
    match pprintCode indent env t.p with (env, p) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelFilter ", p, " ", as])
      else never
    else never
  | TmParallelPartition t ->
    match pprintCode indent env t.p with (env, p) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelPartition ", p, " ", as])
      else never
    else never
  | TmParallelAll t ->
    match pprintCode indent env t.p with (env, p) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelAll ", p, " ", as])
      else never
    else never
  | TmParallelAny t ->
    match pprintCode indent env t.p with (env, p) then
      match pprintCode indent env t.as with (env, as) then
        (env, join ["parallelAny ", p, " ", as])
      else never
    else never
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

mexpr

use MExprParallelKeywordMaker in

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
