include "javascript/ast.mc"
include "javascript/types.mc"
include "javascript/intrinsics.mc"

include "name.mc"
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

  sem optimizeTailCallFunc : CompileJSContext -> Name -> Info -> JSExpr -> JSExpr
  sem optimizeTailCallFunc ctx name info =
  | JSEFun _ & fun ->
    let fun = foldFunc fun in
    match fun with JSEFun r in
    -- Create a new function with the same name but with the _rec suffix
    -- This function will be used as the recursive body of the optimized function
    -- NOTE(william): nameNoSym might clash with a user-defined function!
    let recFunName = lam n. nameNoSym (concat (nameGetStr n) "_rec$") in
    let mod = lam fun.
      -- If found nested tail call, check if it is to a recursive function
      -- registered in the current context
      match fun with JSEVar { id = id } then
        if setMem id ctx.recursiveFunctions then
          -- If it is, replace the function with a trampoline capture call to
          -- the recursive function variant
          (true, JSEVar { id = recFunName id })
        else (false, fun)
      else (false, fun)
    in
    match runOnTailPosition (trampolineCapture mod) fun with { expr = recFun, foundTailCall = optimized } in
    if optimized then
      JSEBlock {
        exprs = [
          -- Declare the function as the recursive function variant
          JSEDef { id = recFunName name, expr = recFun },
          -- Next, declare a function with the original name that calls the
          -- recursive function variant and trampolines the result
          JSEDef {
            id = name,
            expr = JSEFun { r with
              body = intrinsicFromString intrGenNS "trampolineValue" [
                JSEApp {
                  fun = JSEVar { id = recFunName name },
                  args = map (lam p. JSEVar { id = p }) r.params,
                  curried = true
                }
              ]
            }
          }
        ],
        ret = JSENop { }
      }
    else
      fun



    -- TODO: replace the original function with a new optimized function that is renamed
    -- And create a new function with the old name that calls the new optimized function
    -- and trampolines the result.
    -- 1. Optimize the original function
    -- 2. Create a new function with a new name that calls the optimized function
    --    and trampolines the result
    -- 3. All non-recursive calls to the original function should be replaced with
    --    calls to the new function. All recursive calls to the original function
    --    should be left as is.

    -- 1. Optimize the function
    -- let fun = foldFunc fun in
    -- let recFunName = nameSym (concat (nameGetStr name) "_rec") in
    -- let mod = lam fun.
    --   match fun with JSEVar { id = id } then
    --     if nameEq name id then JSEVar { id = recFunName }
    --     else fun
    --   else fun
    -- in
    -- match runOnTailPosition (trampolineCapture mod) fun with { expr = fun, foundTailCall = optimized } in
    -- let fun = if optimized
    --   then intrinsicFromString intrGenNS "trampolineFunc" [JSEString { s = nameGetStr name }, fun]
    --   else fun in
    -- JSEDef { id = ident, expr = fun }

  | _ -> errorSingle [info] "Non-lambda expressions cannot be optimized for tail calls when compiling to JavaScript"


  -- Wrap all calls in a trampoline capture that is immediately returned
  sem trampolineCapture : (JSExpr -> (Bool, JSExpr)) -> JSExpr -> JSExpr
  sem trampolineCapture modifier =
  | JSEApp { fun = fun, args = args } & app ->
    -- Transform function calls to a trampoline capture intrinsic
    match modifier fun with (shouldCapture, fun) in
    if shouldCapture then
      intrinsicFromString intrGenNS "trampolineCapture" [fun, JSEArray{ exprs = args }]
    else app
  | _ -> error "trampolineCapture called on non-function application expression"



  -- Fold (collect) nested functions to the top level (a single function instead of a nested functions)
  sem foldFunc : JSExpr -> JSExpr
  sem foldFunc =
  | JSEFun { params = params, body = body } ->
    let body = foldFunc body in
    match body with JSEFun { params = paramsNested, body = bodyNested } then
      JSEFun { params = concat params paramsNested, body = bodyNested }
    else JSEFun { params = params, body = body }
  | e -> e

  sem runOnTailPosition : (JSExpr -> JSExpr) -> JSExpr -> JSTCOContext
  sem runOnTailPosition action =
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
  | JSEBinOp { op = JSOAnd{}, lhs = lhs, rhs = rhs } ->
    runWithJSTCOCtx action rhs (lam e. JSEBinOp { op = JSOAnd { }, lhs = lhs, rhs = e })
  | JSEBinOp { op = JSOOr{}, lhs = lhs, rhs = rhs } ->
    runWithJSTCOCtx action rhs (lam e. JSEBinOp { op = JSOOr { }, lhs = lhs, rhs = e })
  | t -> { expr = t, foundTailCall = false } -- No terms where tail calls can be located


  sem runWithJSTCOCtx : (JSExpr -> JSExpr) -> JSExpr -> (JSExpr -> JSExpr) -> JSTCOContext
  sem runWithJSTCOCtx action expr =
  | constr ->
    let res = runOnTailPosition action expr in {
      expr = constr res.expr,
      foundTailCall = res.foundTailCall
    }

  sem runWithJSTCOCtx2 : (JSExpr -> JSExpr) -> JSExpr -> JSExpr -> (JSExpr -> JSExpr -> JSExpr) -> JSTCOContext
  sem runWithJSTCOCtx2 action expr1 expr2 =
  | constr ->
    let res1 = runOnTailPosition action expr1 in
    let res2 = runOnTailPosition action expr2 in {
      expr = constr res1.expr res2.expr,
      foundTailCall = or res1.foundTailCall res2.foundTailCall
    }

end



lang JSOptimizeExprs = JSExprAst

  sem optimizeExpr3 : JSExpr -> JSExpr
  sem optimizeExpr3 =
  | expr -> optimizeExpr (optimizeExpr (optimizeExpr expr))

  sem optimizeExpr : JSExpr -> JSExpr
  sem optimizeExpr =
  | JSEBinOp { op = JSOEq  {}, lhs = lhs, rhs = rhs } & p ->
    match lhs with JSEBool { b = true } then optimizeExpr rhs else
    match rhs with JSEBool { b = true } then optimizeExpr lhs else
    match lhs with JSEBool { b = false } then JSEUnOp { op = JSONot {}, rhs = optimizeExpr rhs } else
    match rhs with JSEBool { b = false } then JSEUnOp { op = JSONot {}, rhs = optimizeExpr lhs } else p
  | JSEBinOp { op = JSOAnd {}, lhs = lhs, rhs = rhs } & p ->
    match lhs with JSEBool { b = true } then optimizeExpr rhs else
    match rhs with JSEBool { b = true } then optimizeExpr lhs else p

  | JSEBinOp { op = JSOOr {}, lhs = lhs, rhs = rhs } & p ->
    match lhs with JSEBool { b = false } then optimizeExpr rhs else
    match rhs with JSEBool { b = false } then optimizeExpr lhs else p

  | JSETernary { cond = cond, thn = thn, els = els } ->
    let cond = optimizeExpr cond in
    let thn = optimizeExpr thn in
    let els = optimizeExpr els in
    match cond with JSEBool { b = true } then thn else
    match cond with JSEBool { b = false } then els else
    -- If the then branch is a boolean, optimize it
    match els with JSEBool { b = false } then
      JSEBinOp { op = JSOAnd {}, lhs = cond, rhs = thn }
    else match thn with JSEBool { b = true } then
      JSEBinOp { op = JSOOr {}, lhs = cond, rhs = els }
    else match (thn, els) with (JSEBool { b = true }, JSEBool { b = false }) then
      cond
    else match (thn, els) with (JSEBool { b = false }, JSEBool { b = true }) then
      JSEUnOp { op = JSONot {}, rhs = cond }
    else JSETernary { cond = cond, thn = thn, els = els }

  | e -> smapJSExprJSExpr optimizeExpr e

end
