-- Provides a function for translating utests specified in certain ways into
-- size constraints in PMExpr, which are then used to guide the Futhark
-- compiler. All utests that are not specified in an expected way are removed
-- from the program.
--
-- NOTE(larshum, 2021-11-29): The text below should probably be placed in the
-- README in a section about how to handle size types.
--
-- A utest of the shape 'utest length e1 with length e2' is considered when the
-- expressions 'e1' and 'e2' are either identifiers or of the form 'head e',
-- where the same constraint applies recursively to e. This kind of utest
-- expresses an equality constraint between the parameters x1 and x2.

include "mexpr/type-check.mc"
include "pmexpr/ast.mc"

lang PMExprUtestSizeConstraint = PMExprAst
  -- Attempts to find the dimension of a sequence to which a length expression
  -- refers. By using `head s` one can refer to inner dimensions of a sequence.
  sem findDimension (params : Map Name Type) (dim : Int) =
  | TmVar {ident = id} -> if mapMem id params then Some (id, dim) else None ()
  | TmApp {lhs = TmConst {val = CHead _}, rhs = s} ->
    findDimension params (addi dim 1) s

  sem replaceUtestsWithSizeConstraintH (params : Map Name Type) =
  | TmUtest t ->
    let generateSizeEquality = lam s1 : Expr. lam s2 : Expr.
      match findDimension params 1 s1 with Some (x1, d1) then
        match findDimension params 1 s2 with Some (x2, d2) then
          let ty = tyWithInfo t.info tyunit_ in
          let inexpr = replaceUtestsWithSizeConstraintH params t.next in
          let eq = TmParallelSizeEquality {x1 = x1, d1 = d1, x2 = x2, d2 = d2,
                                           ty = ty, info = t.info} in
          Some (TmLet {ident = nameNoSym "", tyAnnot = ty, tyBody = ty, body = eq,
                       inexpr = inexpr, ty = t.ty, info = t.info})
        else None ()
      else None () in
    let generateSizeCoercion = lam s : Expr. lam id : Name. lam sizeId : Name.
      let inexpr = replaceUtestsWithSizeConstraintH params t.next in
      let coercion =
        TmParallelSizeCoercion {e = s, size = sizeId,
                                ty = tyTm s, info = infoTm s} in
      TmLet {ident = id, tyAnnot = tyTm s, tyBody = tyTm s, body = coercion,
             inexpr = inexpr, ty = t.ty, info = t.info} in
    let result =
      match t.tusing with None _ | Some (TmConst {val = CEqi _}) then
        let p = (t.test, t.expected) in
        match p with (TmApp {lhs = TmConst {val = CLength _}, rhs = s1},
                      TmApp {lhs = TmConst {val = CLength _}, rhs = s2}) then
          generateSizeEquality s1 s2
        else match p with (TmApp {lhs = TmConst {val = CLength _},
                             rhs = s & (TmVar {ident = id})},
                      TmVar {ident = expectedId}) then
          Some (generateSizeCoercion s id expectedId)
        else match p with (TmVar {ident = testId},
                           TmApp {lhs = TmConst {val = CLength _},
                                  rhs = s & (TmVar {ident = id})}) then
          Some (generateSizeCoercion s id testId)
        else None ()
      else None () in
    match result with Some e then e
    else replaceUtestsWithSizeConstraintH params t.next
  | t -> smap_Expr_Expr (replaceUtestsWithSizeConstraintH params) t

  sem replaceUtestsWithSizeConstraint =
  | TmLam t ->
    recursive let extractLambdas = lam acc : Map Name Type. lam e : Expr.
      match e with TmLam t then
        let acc = mapInsert t.ident t.tyParam acc in
        extractLambdas acc t.body
      else (acc, e) in
    recursive let replaceFunctionBody = lam body : Expr. lam e : Expr.
      match e with TmLam t then
        TmLam {t with body = replaceFunctionBody body t.body}
      else body in
    match extractLambdas (mapEmpty nameCmp) (TmLam t) with (params, body) in
    let newBody = replaceUtestsWithSizeConstraintH params body in
    replaceFunctionBody newBody (TmLam t)
  | TmUtest t -> replaceUtestsWithSizeConstraint t.next
  | t -> smap_Expr_Expr replaceUtestsWithSizeConstraint t
end

lang TestLang = PMExprUtestSizeConstraint + TypeCheck
end

mexpr

use TestLang in

let preprocess = lam t.
  typeCheck (symbolize t)
in

let topLevelUtest = preprocess (utest_ (addi_ (int_ 1) (int_ 1)) (int_ 2) unit_) in
utest replaceUtestsWithSizeConstraint topLevelUtest with unit_ using eqExpr in

let s = nameSym "s" in
let t = nameSym "t" in
let n = nameSym "n" in
let exampleTerm = lam inexpr.
  nulam_ n
    (bind_
      (nulet_ s (seq_ []))
      inexpr) in

let utestImplicitUsing = preprocess
  (exampleTerm (utest_ (length_ (nvar_ s)) (nvar_ n) unit_)) in
let expected = exampleTerm (nulet_ s (parallelSizeCoercion_ (nvar_ s) n)) in
utest replaceUtestsWithSizeConstraint utestImplicitUsing with expected using eqExpr in

let utestExplicitEqi = preprocess (exampleTerm
  (utestu_ (length_ (nvar_ s)) (nvar_ n) unit_ (uconst_ (CEqi ())))) in
utest replaceUtestsWithSizeConstraint utestExplicitEqi with expected using eqExpr in

let utestExplicitNonEqi = preprocess (exampleTerm (
  utestu_ (length_ (nvar_ s)) (nvar_ n) unit_ (uconst_ (CGti ())))) in
let expected = exampleTerm unit_ in
utest replaceUtestsWithSizeConstraint utestExplicitNonEqi with expected using eqExpr in

let s1 = nameSym "s1" in
let s2 = nameSym "s2" in
let utestSizeEquality = preprocess
  (nlam_ s1 (tyseq_ tyint_) (nlam_ s2 (tyseq_ tyint_)
    (utest_ (length_ (nvar_ s1)) (length_ (nvar_ s2)) unit_))) in
let expected =
  nlam_ s1 (tyseq_ tyint_) (nlam_ s2 (tyseq_ tyint_)
    (ulet_ "" (parallelSizeEquality_ s1 1 s2 1))) in
utest replaceUtestsWithSizeConstraint utestSizeEquality with expected using eqExpr in

let utestSizeEqMultiDim = preprocess
  (nlam_ s1 (tyseq_ (tyseq_ (tyseq_ tyint_))) (nlam_ s2 (tyseq_ (tyseq_ tyint_))
    (utest_ (length_ (head_ (nvar_ s2))) (length_ (head_ (head_ (nvar_ s1)))) unit_))) in
let expected =
  nlam_ s1 (tyseq_ tyint_) (nlam_ s2 (tyseq_ tyint_)
    (ulet_ "" (parallelSizeEquality_ s2 2 s1 3))) in
utest replaceUtestsWithSizeConstraint utestSizeEqMultiDim with expected using eqExpr in

()
