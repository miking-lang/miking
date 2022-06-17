include "javascript/ast.mc"


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
        else match flatE with (flatEExprs, flatERet) then
          join [acc, flatEExprs, [flatERet]]
        else never
    ) [] exprs) in

    -- Call flattenBlockHelper recursively on the return value
    let flatRet = flattenBlockHelper ret in
    match flatRet with ([], e) then
      -- Normal expressions are returned as is, thus concat them with the expressions
      -- in the current block
      (flatExprs, ret)
    else match flatRet with (retExprs, retRet) then
      (concat flatExprs retExprs, retRet)
    else never
  | expr -> ([], expr)

  sem flattenBlock : JSExpr -> JSExpr
  sem flattenBlock =
  | JSEBlock _ & block ->
    match flattenBlockHelper block with (exprs, ret) then
      JSEBlock { exprs = exprs, ret = ret }
    else never
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



-- Tail Call Optimizations
lang JSOptimizeTailCalls = JSExprAst

  sem optimizeTailCall : Name -> JSExpr -> JSExpr
  sem optimizeTailCall (name: Name) (info: Info) =
  | JSEFun { param = param, body = body } & fun ->
    -- Outer most lambda in the function to be optimized
    if hasTailRecCall name body then
      printLn (concat "Tail call optimization for: " (nameGetStr name));
      runOnTailPositional name trampoline fun
    else
      fun
  | _ -> errorSingle [info] "Non-lambda expressions cannot be optimized for tail calls when compiling to JavaScript"


  sem runOnTailPositional (name: Name) (action: (JSExpr -> JSExpr)) =
  | JSEApp _ & t ->
    -- If the function is a tail call, run the action on the function
    -- and replace the function with the result
    if isTailRecCall name t then action t else t
  | JSEFun { param = param, body = body } -> JSEFun { param = param, body = runOnTailPositional name action body }
  | JSETernary { cond = cond, thn = thn, els = els } ->
    JSETernary { cond = cond, thn = runOnTailPositional name action thn, els = runOnTailPositional name action els }
  | JSEIIFE { body = body } -> JSEIIFE { body = runOnTailPositional name action body }
  | JSEBlock { exprs = exprs, ret = ret } -> JSEBlock { exprs = exprs, ret = runOnTailPositional name action ret }
  | JSEVar _ & t -> t
  | e -> dprintLn e; error "Not yet implemented!"

  sem isTailRecCall (funName: Name) =
  | JSEApp { fun = fun } ->
    dprintLn fun;
    printLn (join ["Checking if previous tail call in ", nameGetStr funName, "..."]);
    -- Check if the function is a tail recursive call
    match fun with JSEVar { name = funName } then true
    else false
  | _ -> false

  sem hasTailRecCall : Name -> JSExpr -> Bool
  sem hasTailRecCall (funName: Name) =
  | _ -> true

  -- Strategies for optimizing tail calls
  sem trampoline : JSExpr -> JSExpr
  sem trampoline =
  | e -> e

end



-- Pattern Matching Optimizations
lang JSOptimizePatterns = JSExprAst

  sem optimizePattern : JSExpr -> JSExpr
  sem optimizePattern =
  | JSEBinOp {
      op = JSOEq {},
      lhs = JSEBool { b = true },
      rhs = e
    } -> e
  | e -> e

end
