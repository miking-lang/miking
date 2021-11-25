-- Provides a function for translating utests that compare the size of a
-- sequence with an expression to a PMExpr size coercion term. Any utest that
-- does not satisfy this requirement is translated

include "pmexpr/ast.mc"

lang PMExprUtestSizeCoercion = PMExprAst
  sem replaceUtestsWithSizeCoercion =
  -- NOTE(larshum, 2021-11-25): As an example of what happens, a utest of the
  -- following form
  --
  --   utest length s with x [using eqi] in next
  --
  -- where s and x are variables, is translated to
  --
  --   let s = parallelSizeCoercion s x in
  --   next
  --
  -- If the utest has a different shape, it is removed instead.
  | TmUtest t ->
    let generateSizeCoercion = lam s : Expr. lam id : Name. lam sizeId : Name.
      let inexpr = replaceUtestsWithSizeCoercion t.next in
      let coercion =
        TmParallelSizeCoercion {e = s, size = sizeId,
                                ty = tyTm s, info = infoTm s} in
      TmLet {ident = id, tyBody = tyTm s, body = coercion,
             inexpr = inexpr, ty = t.ty, info = t.info}
    in
    match t.tusing with None _ | Some (TmConst {val = CEqi _}) then
      let p = (t.test, t.expected) in
      match p with (TmApp {lhs = TmConst {val = CLength _},
                           rhs = s & (TmVar {ident = id})},
                    TmVar {ident = expectedId}) then
        generateSizeCoercion s id expectedId
      else match p with (TmVar {ident = testId},
                         TmApp {lhs = TmConst {val = CLength _},
                                rhs = s & (TmVar {ident = id})}) then
        generateSizeCoercion s id testId
      else replaceUtestsWithSizeCoercion t.next
    else replaceUtestsWithSizeCoercion t.next
  | t -> smap_Expr_Expr replaceUtestsWithSizeCoercion t
end

mexpr

use PMExprUtestSizeCoercion in

let preprocess = lam t.
  typeAnnot (symbolize t)
in

let miscUtest = preprocess (utest_ (addi_ (int_ 1) (int_ 1)) (int_ 2) unit_) in
utest replaceUtestsWithSizeCoercion miscUtest with unit_ using eqExpr in

let s = nameSym "s" in
let t = nameSym "t" in
let n = nameSym "n" in
let exampleTerm = lam inexpr.
  nulam_ n
    (bind_
      (nulet_ s (seq_ []))
      inexpr) in

let utestImplicitUsing = preprocess (
  exampleTerm (utest_ (length_ (nvar_ s)) (nvar_ n) unit_)) in
let expected = exampleTerm (nulet_ s (parallelSizeCoercion_ (nvar_ s) n)) in
utest replaceUtestsWithSizeCoercion utestImplicitUsing with expected using eqExpr in

let utestExplicitEqi = preprocess (exampleTerm (
  utestu_ (length_ (nvar_ s)) (nvar_ n) unit_ (uconst_ (CEqi ())))) in
utest replaceUtestsWithSizeCoercion utestExplicitEqi with expected using eqExpr in

let utestExplicitNotEqi = preprocess (exampleTerm (
  utestu_ (length_ (nvar_ s)) (nvar_ n) unit_ (uconst_ (CGti ())))) in
let expected = exampleTerm unit_ in
utest replaceUtestsWithSizeCoercion utestExplicitNotEqi with expected using eqExpr in


()
