-- Translates a PMExpr program to a MExpr compatible program by erasing all
-- uses of accelerate and demoting parallel operations to their corresponding
-- sequential operations.

include "mexpr/ast-builder.mc"
include "pmexpr/ast.mc"

-- NOTE(larshum, 2021-11-24): This step runs before type checking, so there is
-- no need to propagate any types.
lang PMExprDemote = PMExprAst
  sem demoteParallel =
  | TmAccelerate t -> demoteParallel t.e
  | TmFlatten t -> foldl_ (uconst_ (CConcat ())) (seq_ []) (demoteParallel t.e)
  | TmParallelMap t -> map_ (demoteParallel t.f) (demoteParallel t.as)
  | TmParallelMap2 t ->
    bindall_ [
      ulet_ "a" (demoteParallel t.as),
      ulet_ "b" (demoteParallel t.bs),
      map_
        (lam_ "x" (tytuple_ [tyunknown_, tyunknown_])
          (appf2_ t.f (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))
        (create_ (length_ (var_ "a"))
          (ulam_ "i" (utuple_ [get_ (var_ "a") (var_ "i"),
                               get_ (var_ "b") (var_ "i")])))]
  | TmParallelReduce t ->
    foldl_ (demoteParallel t.f) (demoteParallel t.ne) (demoteParallel t.as)
  | t -> smap_Expr_Expr demoteParallel t
end

mexpr

use PMExprDemote in

let id = ulam_ "x" (var_ "x") in
utest demoteParallel (accelerate_ (app_ id (int_ 2)))
with app_ id (int_ 2) using eqExpr in

let s = seq_ [seq_ [int_ 1], seq_ [int_ 2]] in
let flattenSeqExpr = foldl_ (uconst_ (CConcat ())) (seq_ []) s in
utest demoteParallel (flatten_ s)
with foldl_ (uconst_ (CConcat ())) (seq_ []) s using eqExpr in

utest demoteParallel (parallelMap_ id s) with map_ id s using eqExpr in

utest demoteParallel (parallelReduce_ (uconst_ (CAddi ())) (int_ 0) (seq_ []))
with foldl_ (uconst_ (CAddi ())) (int_ 0) (seq_ []) using eqExpr in

utest demoteParallel (parallelMap2_ (uconst_ (CAddi ())) (flatten_ s) (flatten_ s))
with bindall_ [
  ulet_ "a" flattenSeqExpr,
  ulet_ "b" flattenSeqExpr,
  map_
    (ulam_ "x" (addi_ (tupleproj_ 0 (var_ "x")) (tupleproj_ 1 (var_ "x"))))
    (create_
      (length_ (var_ "a"))
      (ulam_ "i" (utuple_ [get_ (var_ "a") (var_ "i"),
                           get_ (var_ "b") (var_ "i")])))]
using eqExpr in

utest demoteParallel (parallelReduce_ (uconst_ (CAddi ())) (int_ 0) (flatten_ s))
with foldl_ (uconst_ (CAddi ())) (int_ 0) flattenSeqExpr using eqExpr in

utest demoteParallel (accelerate_ (parallelMap_ id (flatten_ s)))
with map_ id (foldl_ (uconst_ (CConcat ())) (seq_ []) s) using eqExpr in

()
