include "utest.mc"

include "side-effect.mc"
include "eval.mc"
include "boot-parser.mc"
include "eq.mc"
include "pprint.mc"
include "symbolize.mc"
include "type-check.mc"
include "ast-builder.mc"

/-
  This file implements constant folding and constant propagation
-/

-- Size limit on constant nodes that we want to propagate
let constantFoldCountMax = 100

lang ConstantFold = Eval + Ast
  -- Entry point for constant folding and constant propagation over a program
  sem constantFold : Expr -> Expr
  sem constantFold =| t ->
    readback (constantFoldExpr (evalCtxEmpty ()) t)

  -- Language framents should extend this semantic function. Note that the
  -- evaluation environment should, at all time, only contain values that are
  -- constants. See `isConstant` for the definition of a constant.
  sem constantFoldExpr : EvalCtx -> Expr -> Expr
  sem constantFoldExpr ctx =| t -> smap_Expr_Expr (constantFoldExpr ctx) t

  -- This semantic function restricts what is considered constants.
  sem isConstant : Expr -> Bool
  sem isConstant =| _ -> false

  -- This semantic function restricts what we propagate.
  sem doPropagate : Expr -> Bool
  sem doPropagate =| t ->
    and (isConstant t) (lti (countNodes t) constantFoldCountMax)

  -- Constant folding may produce additional evaluation terms such as partial
  -- applications of constants. This semantic function reads those back to
  -- standard terms.
  sem readback : Expr -> Expr
  sem readback =| t -> smap_Expr_Expr readback t

  -- Counts the number of expression nodes.
  sem countNodes : Expr -> Int
  sem countNodes =| t -> countNodesH 0 t

  sem countNodesH : Int -> Expr -> Int
  sem countNodesH n =| t ->
    let n = addi n 1 in sfold_Expr_Expr countNodesH n t
end

lang VarConstantFold = ConstantFold + VarAst
  sem constantFoldExpr ctx =
  | TmVar r ->
    match evalEnvLookup r.ident ctx.env with Some t then t
    else TmVar r
end

lang AppConstantFold = ConstantFold + AppEval + ConstSideEffect + ConstArity

  syn Expr =
  -- Partial constant application where all arguments are constant
  | PartialConstAppConsts { expr : Expr,  arity : Int }
  -- Partial constant application where some argument is NOT constant
  | PartialConstApp { expr : Expr,  arity : Int }

  -- This semantic function is only be called with an expression representing a
  -- constant function without side-effects applied on constant arguments.
  sem constantFoldConstAppConsts : Expr -> Expr
  sem constantFoldConstAppConsts =
  | t -> constantFoldConstApp t

  -- This semantic function is only called with an expression representing a
  -- constant function without side-effects applied to arguments that may not be
  -- constants.
  sem constantFoldConstApp : Expr -> Expr
  sem constantFoldConstApp =
  | t -> t

  sem constantFoldExpr ctx =
  | TmApp appr ->
    let lhs = constantFoldExpr ctx appr.lhs in
    let rhs = constantFoldExpr ctx appr.rhs in
    let t = TmApp { appr with lhs = lhs, rhs = rhs } in
    switch (lhs, isConstant rhs)
      -- Constant application on constant arguments
    case (TmConst constr, true) then
      if eqi (constArity constr.val) 1 then
        constantFoldConstAppConsts t
      else
        PartialConstAppConsts { expr = t, arity = pred (constArity constr.val) }
    case (PartialConstAppConsts pappr, true) then
      let expr = TmApp { appr with lhs = pappr.expr, rhs = rhs } in
      if neqi pappr.arity 1 then
        PartialConstAppConsts { expr = expr, arity = pred pappr.arity }
      else constantFoldConstAppConsts expr
      -- Constant application with some non-constant arguments
    case (TmConst constr, false) then
      if eqi (constArity constr.val) 1 then
        constantFoldConstApp t
      else
        PartialConstApp { expr = t, arity = pred (constArity constr.val) }
    case
      (PartialConstAppConsts pappr | PartialConstApp pappr, false)
    | (PartialConstAppConsts pappr, true)
    | (PartialConstApp pappr, true)
    then
      let expr = TmApp { appr with lhs = pappr.expr, rhs = rhs } in
      if neqi pappr.arity 1 then
        PartialConstApp { expr = expr, arity = pred pappr.arity }
      else constantFoldConstApp expr
    case _ then t
    end

  sem isConstant =
  | PartialConstAppConsts _ -> true
  | PartialConstApp _ -> false

  sem readback =
  | PartialConstAppConsts r | PartialConstApp r -> readback r.expr
end

lang LamAppConstantFold = ConstantFold + AppAst + LamAst
  sem constantFoldExpr ctx =
  | TmApp (appr & {lhs = TmLam lamr}) ->
    let rhs = constantFoldExpr ctx appr.rhs in
    if doPropagate rhs then
      let ctx = { ctx with env = evalEnvInsert lamr.ident rhs ctx.env } in
      constantFoldExpr ctx lamr.body
    else
      TmApp {
        appr with
        lhs = smap_Expr_Expr (constantFoldExpr ctx) (TmLam lamr),
        rhs = rhs
      }
end

lang LetConstantFold = ConstantFold + LetAst
  sem constantFoldExpr ctx =
  | TmLet r ->
    let body = constantFoldExpr ctx r.body in
    if doPropagate body then
      let ctx = { ctx with env = evalEnvInsert r.ident body ctx.env } in
      constantFoldExpr ctx r.inexpr
    else
      TmLet {
        r with
        body = body,
        inexpr = constantFoldExpr ctx r.inexpr
      }
end

lang RecordConstantFold = ConstantFold + RecordAst
  sem isConstant =
  | TmRecord r -> mapAll isConstant r.bindings
end

lang ConstConstantFold = ConstantFold + ConstAst
  sem isConstant =
  | TmConst _ -> true
end

lang DataConstantFold = ConstantFold + DataAst
  sem isConstant =
  | TmConApp r -> isConstant r.body
end

lang MatchConstantFold = ConstantFold + MatchEval
  sem constantFoldExpr ctx =
  | TmMatch r ->
    let target = constantFoldExpr ctx r.target in
    if isConstant target then
      match tryMatch ctx.env target r.pat with Some newEnv then
        constantFoldExpr { ctx with env = newEnv } r.thn
      else
        constantFoldExpr ctx r.els
    else
      let newEnv =
        match tryMatch (evalEnvEmpty ()) target r.pat with Some newEnv then
          evalEnvConcat (evalEnvFilter (lam x. isConstant x.1) newEnv) ctx.env
        else ctx.env
      in
      TmMatch {
        r with
        target = target,
        thn = constantFoldExpr { ctx with env = newEnv } r.thn,
        els = constantFoldExpr ctx r.els
      }
end

lang SeqConstantFold = ConstantFold + SeqAst
  sem isConstant =
  | TmSeq r -> forAll isConstant r.tms
end

lang ArithIntConstantFold = AppConstantFold + ArithIntAst + ArithIntArity
  sem constantFoldConstAppConsts =
  | TmApp (r & {
    lhs = TmConst {val = const & (CNegi _)},
    rhs = TmConst {val = CInt {val = n}}
  }) ->
    TmConst { val = CInt { val = negi n }, info = r.info, ty = r.ty }
  | TmApp (r & {
    lhs = TmApp {
      lhs = TmConst {
        val = const & (CAddi _ | CSubi _ | CMuli _ | CDivi _ | CModi _)},
      rhs = TmConst {val = CInt {val = n1}}},
    rhs = TmConst {val = CInt {val = n2}}
  }) ->
    TmConst {
      val = CInt { val = constantFoldConstAppInt2 const n1 n2 },
      info = r.info,
      ty = r.ty
    }

  sem constantFoldConstAppInt2 : Const -> (Int -> Int -> Int)
  sem constantFoldConstAppInt2 =
  | CAddi _ -> addi
  | CSubi _ -> subi
  | CMuli _ -> muli
  | CDivi _ -> divi
  | CModi _ -> modi
end

lang ArithFloatConstantFold = AppConstantFold + ArithFloatAst + ArithFloatArity
  sem constantFoldConstAppConsts =
  | TmApp (r & {
    lhs = TmConst {val = const & (CNegf _)},
    rhs = TmConst {val = CFloat {val = f}}
  }) ->
    TmConst { val = CFloat { val = negf f }, info = r.info, ty = r.ty }
  | TmApp (r & {
    lhs = TmApp {
      lhs = TmConst {
        val = const & (CAddf _ | CSubf _ | CMulf _ | CDivf _)},
      rhs = TmConst {val = CFloat {val = f1}}},
    rhs = TmConst {val = CFloat {val = f2}}
  }) ->
    TmConst {
      val = CFloat { val = constantFoldConstAppFloat2 const f1 f2 },
      info = r.info,
      ty = r.ty
    }

  sem constantFoldConstAppFloat2 : Const -> (Float -> Float -> Float)
  sem constantFoldConstAppFloat2 =
  | CAddf _ -> addf
  | CSubf _ -> subf
  | CMulf _ -> mulf
  | CDivf _ -> divf
end

lang SeqOpConstantFoldFirstOrder =
  AppConstantFold + SeqOpAst + IntAst + BoolAst + SeqOpArity

  sem constantFoldConstAppConsts =
  | TmApp {lhs = TmConst {val = CHead _}, rhs = TmSeq r} -> head r.tms
  | TmApp {lhs = TmConst {val = CTail _}, rhs = TmSeq r} ->
    TmSeq { r with tms = tail r.tms }
  | TmApp {
    lhs = TmApp {lhs = TmConst {val = CGet _}, rhs = TmSeq r},
    rhs = TmConst {val = CInt {val = i}}
  } ->
    get r.tms i
  | TmApp {
    lhs = TmApp {
      lhs = TmApp {lhs = TmConst {val = CSet _}, rhs = TmSeq r},
      rhs = TmConst {val = CInt {val = i}}},
    rhs = val
  } ->
    TmSeq { r with tms = set r.tms i val }
  | TmApp {lhs = TmConst {val = CReverse _}, rhs = TmSeq r} ->
    TmSeq { r with tms = reverse r.tms }
  | TmApp {
    lhs = TmApp {
      lhs = TmApp {lhs = TmConst {val = CSubsequence _}, rhs = TmSeq r},
      rhs = TmConst {val = CInt {val = ofs}}},
    rhs = TmConst {val = CInt {val = len}}
  } ->
    TmSeq { r with tms = subsequence r.tms ofs len }

  sem constantFoldConstApp =
  | TmApp {
    lhs = TmApp {lhs = TmConst {val = CCons _}, rhs = val},
    rhs = TmSeq r
  } ->
    TmSeq { r with tms = cons val r.tms }
  | TmApp {
    lhs = TmApp {lhs = TmConst {val = CSnoc _}, rhs = TmSeq r},
    rhs = val
  } ->
    TmSeq { r with tms = snoc r.tms val }
  | TmApp {
    lhs = TmApp {lhs = TmConst {val = CConcat _}, rhs = TmSeq r1},
    rhs = TmSeq r2
  } ->
    TmSeq { r1 with tms = concat r1.tms r2.tms }
  | TmApp (appr & {lhs = TmConst {val = CLength _}, rhs = TmSeq seqr}) ->
    TmConst {
      val = CInt { val = length seqr.tms },
      ty = appr.ty,
      info = appr.info
    }
  | TmApp (appr & {
    lhs = TmApp {lhs = TmConst {val = CSplitAt _}, rhs = TmSeq seqr},
    rhs = TmConst {val = CInt {val = i}}
  }) ->
    let t = splitAt seqr.tms i in
    tmTuple appr.info appr.ty
      [TmSeq { seqr with tms = t.0 }, TmSeq { seqr with tms = t.1 }]
end

lang MExprConstantFold = MExprAst +

  -- Terms
  VarConstantFold + AppConstantFold + LamAppConstantFold + LetConstantFold +
  RecordConstantFold + ConstConstantFold + MatchConstantFold + SeqConstantFold +

  -- Constant operations
  ArithIntConstantFold + ArithFloatConstantFold + SeqOpConstantFoldFirstOrder +

  -- Patterns
  NamedPatEval + SeqTotPatEval + SeqEdgePatEval + RecordPatEval + DataPatEval +
  IntPatEval + CharPatEval + BoolPatEval + AndPatEval + OrPatEval + NotPatEval
end

lang TestLang = MExprConstantFold +
  MExprPrettyPrint + MExprEq + BootParser + MExprSym + MExprTypeCheck
end

mexpr

use TestLang in

let _parse = lam prog.
  typeCheck
    (symbolize
       (parseMExprStringExn
          { _defaultBootParserParseMExprStringArg () with allowFree = false }
          prog))
in

let _toString = utestDefaultToString expr2str expr2str in

-------------------------------------------------
-- Test constant folding of integer arithmetic --
-------------------------------------------------

let prog = _parse "muli 3 2" in
let expected = _parse "6" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog = _parse "divi 3 (negi (subi 4 (addi (muli 3 2) 1)))" in
let expected = _parse "1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

-----------------------------------------------
-- Test constant folding of float arithmetic --
-----------------------------------------------

let prog = _parse "mulf 3. 2." in
let expected = _parse "6." in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog = _parse "divf 3. (negf (subf 4. (addf (mulf 3. 2.) 1.)))" in
let expected = _parse "1." in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

------------------------------------------
-- Test constant propagation of integer --
------------------------------------------

let prog = _parse "let x = 3 in let y = 2 in muli x y" in
let expected = _parse "6" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

---------------------------------------------------------------
-- Test constant propagation of partially applied intrinsics --
---------------------------------------------------------------

let prog =
  _parse "let f = addi 3 in let g = subi 2 in lam x. muli (f 1) (g 1)"
in
let expected = _parse "lam x. 4" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

--------------------------------------
-- Test constant folding of matches --
--------------------------------------

let prog =
  _parse "
    if true then true else false
    "
in
let expected = _parse "true" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    if false then true else false
    "
in
let expected = _parse "false" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    let x = 1 in let y = 2 in
    match x with y then y else y
    "
in
let expected = _parse "1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    let t = (0, 1) in t.1
    "
in
let expected = _parse "1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x. let t = (x, 1) in t.1
    "
in
let expected = _parse "lam x. let t = (x, 1) in t.1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x. match [x, 1] with [_, x] in x
    "
in
let expected = _parse "lam x. match [x, 1] with [_, x] in 1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

-----------------------------------------
-- Test constant folding for sequences --
-----------------------------------------

let prog =
  _parse "
    lam x.
      head [1, 2, 3]
    "
in
let expected = _parse "lam x. 1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      head [1, 2, x]
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      tail [1, 2, 3]
    "
in
let expected = _parse "lam x. [2, 3]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      tail [1, 2, x]
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      get [1, 2, 3] 0
    "
in
let expected = _parse "lam x. 1" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      get [1, 2, x] 0
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      set [1, 2, 3] 0 2
    "
in
let expected = _parse "lam x. [2, 2, 3]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      set [1, 2, x] 0 2
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      cons 0 [1, 2, 3]
    "
in
let expected = _parse "lam x. [0, 1, 2, 3]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      cons 0 [1, 2, x]
    "
in
let expected = _parse "lam x. [0, 1, 2, x]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      snoc [1, 2, 3] 4
    "
in
let expected = _parse "lam x. [1, 2, 3, 4]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      snoc [1, 2, x] 4
    "
in
let expected = _parse "lam x. [1, 2, x, 4]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      concat [1, 2, 3] [4]
    "
in
let expected = _parse "lam x. [1, 2, 3, 4]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      concat [1, 2, x] [4]
    "
in
let expected = _parse "lam x. [1, 2, x, 4]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      length [1, 2, 3]
    "
in
let expected = _parse "lam x. 3" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      length [1, 2, x]
    "
in
let expected = _parse "lam x. 3" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      reverse [1, 2, 3]
    "
in
let expected = _parse "lam x. [3, 2, 1]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      reverse [1, 2, x]
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      subsequence [1, 2, 3] 1 2
    "
in
let expected = _parse "lam x. [2, 3]" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      subsequence [1, 2, x] 1 2
    "
in
let expected = prog in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      splitAt [1, 2, 3] 1
    "
in
let expected = _parse "lam x. ([1], [2, 3])" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

let prog =
  _parse "
    lam x.
      splitAt [1, 2, x] 1
    "
in
let expected = _parse "lam x. ([1], [2, x])" in
let actual = constantFold prog in
utest actual with expected using eqExpr else _toString in

()
