include "javascript/ast.mc"
include "javascript/intrinsics.mc"

include "bool.mc"


-- Block Optimizations
lang JSOptimizeBlocks = JSExprAst

  sem flattenBlockHelper : JSExpr -> ([JSExpr], JSExpr)
  sem flattenBlockHelper =
  | JSEBlock { exprs = exprs, ret = ret } ->
    -- If the return value is a block, concat the expressions in that block with the
    -- expressions in the current block and set the return value to the return value
    -- of the current block
    -- For each expression in the current block, if it is a block, flatten it
    let flatExprs : [JSExpr] = filterNops (foldr (
      lam e. lam acc.
        let flatE = flattenBlockHelper e in
        match flatE with ([], e) then
          cons e acc
        else match flatE with (flatEExprs, flatERet) in
          join [acc, flatEExprs, [flatERet]]
    ) [] exprs) in

    -- Call flattenBlockHelper recursively on the return value
    let flatRet = flattenBlockHelper ret in
    match flatRet with ([], e) then
      -- Normal expressions are returned as is, thus concat them with the expressions
      -- in the current block
      (flatExprs, ret)
    else match flatRet with (retExprs, retRet) in
      (concat flatExprs retExprs, retRet)
  | expr -> ([], expr)

  sem flattenBlock : JSExpr -> JSExpr
  sem flattenBlock =
  | JSEBlock _ & block ->
    match flattenBlockHelper block with (exprs, ret) in
    JSEBlock { exprs = exprs, ret = ret }
  | expr -> expr

  sem immediatelyInvokeBlock : JSExpr -> JSExpr
  sem immediatelyInvokeBlock =
  | JSEBlock _ & block -> JSEIIFE { body = block }
  | expr -> expr

  sem filterNops : [JSExpr] -> [JSExpr]
  sem filterNops =
  | lst -> foldr (
    lam e. lam acc.
      match e with JSENop { } then acc else cons e acc
  ) [] lst

end

type JSTCOContext = {
  expr: JSExpr,
  foundTailCall: Bool
}

-- Tail Call Optimizations
lang JSOptimizeTailCalls = JSExprAst + JSIntrinsic

  sem optimizeTailCall : Name -> Info -> CompileJSContext -> JSExpr -> (CompileJSContext, JSExpr)
  sem optimizeTailCall name info ctx =
  | JSEFun _ & fun ->
    -- Outer most lambda in the function to be optimized
    let fun = foldFunc fun in
    match runOnTailPositional trampolineCapture fun with { expr = fun, foundTailCall = true } then
      let ctx = { ctx with trampolinedFunctions = mapInsert name fun ctx.trampolinedFunctions } in
      (ctx, fun)
    else
      -- Otherwise, return the function as is
      (ctx, fun)
  | _ -> errorSingle [info] "Non-lambda expressions cannot be optimized for tail calls when compiling to JavaScript"


  sem wrapCallToOptimizedFunction : Info -> JSExpr -> Int -> JSExpr -> JSExpr
  sem wrapCallToOptimizedFunction info fun nrArgs =
  | JSEApp _ & app ->
    -- Trampoline fully applied trampoline functions
    match fun with JSEFun { params = params } in
    if eqi (length params) nrArgs then
      -- Wrap the function application in a trampoline intrinsic
      intrinsicFromString intrGenNS "trampoline" [app]
    else
      errorSingle [info] "Tail call optimized functions must be fully applied when compiling to JavaScript"
  | _ -> errorSingle [info] "trampolineWrapCall invoked with non-function expression"


  -- Fold nested functions to the top level
  sem foldFunc : JSExpr -> JSExpr
  sem foldFunc =
  | JSEFun { params = params, body = body } ->
    let body = foldFunc body in
    match body with JSEFun { params = paramsNested, body = bodyNested } then
      JSEFun { params = concat params paramsNested, body = bodyNested }
    else JSEFun { params = params, body = body }
  | e -> e

  sem runOnTailPositional : (JSExpr -> JSExpr) -> JSExpr -> JSTCOContext
  sem runOnTailPositional action =
  | JSEApp { fun = fun } & t ->
    -- If the function is a tail call, run the action on the function
    -- and replace the function with the result
    match fun with JSEVar _ then {
      expr = action t,
      foundTailCall = true
    } else {
      expr = t,
      foundTailCall = false
    }
  | JSEFun      t -> runWithJSTCOCtx action t.body (lam e. JSEFun { t with body = e })
  | JSEIIFE     t -> runWithJSTCOCtx action t.body (lam e. JSEIIFE { t with body = e })
  | JSEBlock    t -> runWithJSTCOCtx action t.ret (lam e. JSEBlock { t with ret = e })
  | JSETernary  t -> runWithJSTCOCtx2 action t.thn t.els (lam e1. lam e2. JSETernary { t with thn = e1, els = e2 })
  | t -> { expr = t, foundTailCall = false } -- No terms where tail calls can be located


  sem runWithJSTCOCtx : (JSExpr -> JSExpr) -> JSExpr -> (JSExpr -> JSExpr) -> JSTCOContext
  sem runWithJSTCOCtx action expr =
  | constr ->
    let res = runOnTailPositional action expr in {
      expr = constr res.expr,
      foundTailCall = res.foundTailCall
    }

  sem runWithJSTCOCtx2 : (JSExpr -> JSExpr) -> JSExpr -> JSExpr -> (JSExpr -> JSExpr -> JSExpr) -> JSTCOContext
  sem runWithJSTCOCtx2 action expr1 expr2 =
  | constr ->
    let res1 = runOnTailPositional action expr1 in
    let res2 = runOnTailPositional action expr2 in {
      expr = constr res1.expr res2.expr,
      foundTailCall = or res1.foundTailCall res2.foundTailCall
    }

  -- Strategies for optimizing tail calls

  -- Wrap all calls in a trampoline capture that is immediately returned
  sem trampolineCapture : JSExpr -> JSExpr
  sem trampolineCapture =
  | JSEApp { fun = fun, args = args } ->
    -- Transform function calls to a trampoline capture intrinsic
    intrinsicFromString intrGenNS "trampolineCapture" [fun, JSEArray{ exprs = args }]
  | _ -> error "trampolineCapture called on non-function application expression"

  sem trampolineWrapCall : JSExpr -> JSExpr
  sem trampolineWrapCall =
  | JSEApp _ & app ->
    -- Wrap the function application in a trampoline intrinsic
    intrinsicFromString intrGenNS "trampoline" [app]
  | _ -> error "trampolineWrapCall invoked with non-function expression"

end



-- Pattern Matching Optimizations
lang JSOptimizePatterns = JSExprAst

  sem optimizePattern : JSExpr -> JSExpr
  sem optimizePattern =
  | JSEBinOp { op = JSOEq  {}, lhs = lhs, rhs = rhs } & p -- Same as and
  | JSEBinOp { op = JSOAnd {}, lhs = lhs, rhs = rhs } & p ->
    match lhs with JSEBool { b = true } then optimizePattern rhs else
    match rhs with JSEBool { b = true } then optimizePattern lhs else p
  | JSEBinOp { op = JSOOr {}, lhs = lhs, rhs = rhs } & p ->
    match lhs with JSEBool { b = false } then optimizePattern rhs else
    match rhs with JSEBool { b = false } then optimizePattern lhs else p
  | e -> e

  sem optimizePattern3 : JSExpr -> JSExpr
  sem optimizePattern3 =
  | expr -> optimizePattern (optimizePattern (optimizePattern expr))

end



lang JSOptimizeExprs = JSExprAst + JSOptimizePatterns

  sem optimizeConditionalBranch : JSExpr -> JSExpr
  sem optimizeConditionalBranch =
  | JSETernary { cond = cond, thn = thn, els = els } ->
    let cond = optimizePattern cond in
    let thn = optimizeConditionalBranch thn in
    let els = optimizeConditionalBranch els in
    match cond with JSEBool { b = true } then thn else
    match cond with JSEBool { b = false } then els else
    -- If the then branch is a boolean, optimize it
    match (cond, thn, els) with (JSEVar _ & c, JSEVar _ & t, JSEBool { b = false }) then
      JSEBinOp { op = JSOAnd {}, lhs = c, rhs = t }
    else match (cond, thn, els) with (JSEVar _ & c, JSEBool { b = true }, JSEVar _ & e) then
      JSEBinOp { op = JSOOr {}, lhs = c, rhs = e }
    else match (cond, thn, els) with (JSEVar _ & c, JSEBool { b = false }, JSEBool { b = true }) then
      JSEUnOp { op = JSONot {}, rhs = c }
    else match (cond, thn, els) with (JSEVar _ & c, JSEBool { b = true }, JSEBool { b = false }) then
      c
    else JSETernary { cond = cond, thn = thn, els = els }
  | p -> p

end
