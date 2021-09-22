-- Promotes a sequential operation into a parallel one, after it has been
-- verified to follow certain properties.

include "mexpr/ast-builder.mc"
include "pmexpr/function-properties.mc"
include "pmexpr/ast.mc"

lang PMExprPromote = PMExprAst + PMExprFunctionProperties
  sem getInnerFunction =
  | TmLam t -> getInnerFunction t.body
  | TmApp t -> getInnerFunction t.lhs
  | TmLet (t & {inexpr = TmVar {ident = id}}) ->
    if nameEq t.ident id then
      getInnerFunction t.body
    else TmLet t
  | t -> t

  sem promote =
  | app & (TmApp {lhs = TmApp {lhs = TmApp {lhs = TmConst {val = CFoldl ()},
                                            rhs = arg1},
                               rhs = ne},
                  rhs = s}) ->
    let fBody = getInnerFunction arg1 in
    if isAssociative fBody then
      match getNeutralElement fBody with Some fNeutralElement then
        if eqExpr ne fNeutralElement then
          -- TODO(larshum, 2021-09-07): This operation should be translated
          -- to a flattening operation.
          match fBody with TmConst {val = CConcat ()} then
            app
          else
            TmParallelReduce {f = arg1, ne = ne, as = s, ty = ty app,
                              info = infoTm app}
        else app
      else app
    else app
  | t -> smap_Expr_Expr promote t
end

lang TestLang = PMExprPromote

mexpr

use TestLang in

let f1 = const_ (tyarrow_ tyint_ (tyarrow_ tyint_ tyint_)) (CAddi ()) in
let f2 = lam_ "x" tyint_ (lam_ "y" tyint_ (addi_ (var_ "x") (var_ "y"))) in
let f3 = lam_ "x" tyint_ (lam_ "y" tyint_ (muli_ (var_ "x") (var_ "y"))) in
let f4 = lam_ "x" (tyseq_ tyint_) (lam_ "y" (tyseq_ tyint_) (concat_ (var_ "x") (var_ "y"))) in

let ne1 = int_ 0 in
let ne2 = int_ 1 in
let ne3 = seq_ [] in

let s1 = seq_ [int_ 1, int_ 2, int_ 3] in
let s2 = seq_ [seq_ [int_ 1, int_ 2], seq_ [int_ 3, int_ 4]] in

let foldlAddiCurried = foldl_ f1 ne1 s1 in
utest promote foldlAddiCurried with parallelReduce_ f1 ne1 s1 using eqExpr in

let foldlAddi = foldl_ f2 ne1 s1 in
utest promote foldlAddi with parallelReduce_ f2 ne1 s1 using eqExpr in

let foldlMuli = foldl_ f3 ne2 s1 in
utest promote foldlMuli with parallelReduce_ f3 ne2 s1 using eqExpr in

let foldlAddiNonNeutral = foldl_ f2 ne2 s1 in
utest promote foldlAddiNonNeutral with foldlAddiNonNeutral using eqExpr in

-- NOTE(larshum, 2021-09-07): Translating foldl of concat into a reduce is not
-- valid in Futhark, because the array size is part of the type. Hence we
-- explicitly prevent that translation here.
let foldlConcat = foldl_ f4 ne3 s2 in
utest promote foldlConcat with foldlConcat using eqExpr in

()
