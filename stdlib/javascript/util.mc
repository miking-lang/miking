
include "mexpr/ast.mc"
include "javascript/ast.mc"


----------------------
-- HELPER FUNCTIONS --
----------------------

-- Check for unit type
let _isUnitTy: Type -> Bool = use RecordTypeAst in lam ty: Type.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields else false

let _isCharSeq: [Expr] -> Bool = use MExprAst in lam tms: [Expr].
  if null tms then false -- Empty list is not a char sequence
  else forAll (
    lam c : Expr.
      match c with TmConst { val = CChar _ } then true else false
  ) tms

-- First, always check if the terms are characters using _isCharSeq
let _charSeq2String: [Expr] -> String = use MExprAst in lam tms: [Expr].
  let toChar = lam expr.
    match expr with TmConst { val = CChar { val = val } } in val
  in map toChar tms -- String is a list of characters

let _isCharPatSeq: [Pat] -> Bool = use MExprAst in lam pats: [Pat].
  if null pats then false -- Empty list is not a char sequence
  else forAll (
    lam c : Pat.
      match c with PatChar _ then true else false
  ) pats

-- First, always check if the terms are characters using _isCharPatSeq
let _charPatSeq2String: [Pat] -> String = use MExprAst in lam pats: [Pat].
  let toChar = lam pat.
    match pat with PatChar { val = val } in val
  in map toChar pats -- String is a list of characters


-------------------------------
-- OPERATOR HELPER FUNCTIONS --
-------------------------------

let _binOp : JSBinOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args. JSEBinOp { op = op, lhs = head args, rhs = last args }

let _unOp : JSUnOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args. JSEUnOp { op = op, rhs = head args }

let _assign : JSExpr -> JSExpr -> JSExpr = use JSExprAst in
  lam lhs. lam rhs. JSEBinOp { op  = JSOAssign {}, lhs = lhs, rhs = rhs }

-- Multi binary operator folding into nested binary operators.
-- Assume length of args is 2 or more.
let _binOpM : JSBinOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args.
  recursive let f = (lam args : [JSExpr]. lam acc : JSExpr.
    if null args then acc
    else f (tail args) (_binOp op [acc, head args])
  ) in
  f (tail args) (head args)
