include "bool.mc"
include "error.mc"
include "mexpr/ast.mc"
include "javascript/ast.mc"
include "javascript/operators.mc"


lang PatJSCompileLang = JSProgAst + NamedPat + SeqTotPat + SeqEdgePat +
                    RecordPat + DataPat + IntPat + OrPat +
                    CharPat + BoolPat + AndPat + NotPat
end

let tmpIgnoreJS = use PatJSCompileLang in
  JSEVar { id = nameSym "_" }


------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile = PatJSCompileLang

  -- Compile a single pattern without any binding operations.
  sem compileSinglePattern =
  | PatInt { val = val } -> JSEInt { i = val }
  | PatBool { val = val } -> JSEBool { b = val }
  | PatNamed { ident = PName name } -> JSEVar { id = name }
  | PatNamed { ident = PWildcard () } -> tmpIgnoreJS
  | PatSeqTot { pats = patterns } -> JSEArray { exprs = map (compileSinglePattern) patterns }
  | PatRecord   { bindings = bindings } ->
    let compileField = lam f. match f with (sid, expr) in
      (sidToString sid, compileSinglePattern expr)
    in
    JSEObject { fields = map (compileField) (mapToSeq bindings) }
  -- | PatSeqEdge  { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
  --   let hasPrefix = not (null prefix) in
  --   let hasMiddle = match middle with PName _ then true else false in
  --   let hasPostfix = not (null postfix) in
  --   let prefixExprs: [JSExpr] = map (compileSinglePattern) prefix in
  --   let middleExpr: JSExpr = compileSinglePattern (PatNamed { ident = middle, ty = ty, info = info }) in
  --   let postfixExprs: [JSExpr] = map (compileSinglePattern) postfix in
  --   switch (hasPrefix, hasMiddle, hasPostfix)
  --     case (false, false, false) then middleExpr
  --     case (true, false, false) then
  --       _assign (JSEArray { exprs = prefixExprs }) target
  --     case (true, true, false) then
  --       _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target
  --     case (true, true, true) then
  --       _binOpM (JSOAnd {}) [
  --         _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target,
  --         _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
  --         shortenMiddle (length postfixExprs) middleExpr
  --       ]
  --     case (false, true, true) then
  --       _binOpM (JSOAnd {}) [
  --         _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
  --         _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
  --         shortenMiddle (length postfixExprs) middleExpr
  --       ]
  --     case (false, true, false) then
  --       _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target
  --     case (false, false, true) then
  --       _binOpM (JSOAnd {}) [
  --         _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
  --         _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
  --       ]
  --     case (true, false, true) then
  --       _binOpM (JSOAnd {}) [
  --         _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
  --         _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
  --       ]
  --   end

  sem compileBindingPattern (target: JSExpr) =
  | PatNamed    { ident = PWildcard () } -> JSEBool { b = true }
  | (PatInt _ | PatBool _) & p -> _binOp (JSOEq {}) [target, compileSinglePattern p]
  | (PatNamed { ident = PName _ }
    | PatSeqTot _
    | PatSeqEdge _
    | PatRecord _) & p -> _assign (compileSinglePattern p) target
  | PatSeqEdge  { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
    let hasPrefix = not (null prefix) in
    let hasMiddle = match middle with PName _ then true else false in
    let hasPostfix = not (null postfix) in
    let prefixExprs: [JSExpr] = map (compileSinglePattern) prefix in
    let middleExpr: JSExpr = compileSinglePattern (PatNamed { ident = middle, ty = ty, info = info }) in
    let postfixExprs: [JSExpr] = map (compileSinglePattern) postfix in
    switch (hasPrefix, hasMiddle, hasPostfix)
      case (false, false, false) then middleExpr
      case (true, false, false) then
        _assign (JSEArray { exprs = prefixExprs }) target
      case (true, true, false) then
        _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target
      case (true, true, true) then
        _binOpM (JSOAnd {}) [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ]
      case (false, true, true) then
        _binOpM (JSOAnd {}) [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ]
      case (false, true, false) then
        _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target
      case (false, false, true) then
        _binOpM (JSOAnd {}) [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ]
      case (true, false, true) then
        _binOpM (JSOAnd {}) [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ]
    end
  | pat -> errorSingle [infoPat pat] "Pattern not supported"


  sem reverseExpr : JSExpr -> JSExpr
  sem reverseExpr =
  | e -> JSEApp {
      fun = JSEMember {
        expr = JSEApp { fun = JSEMember { expr = e, id = "slice" }, args = [], curried = false },
        id = "reverse"
      },
      args = [],
      curried = false
    }

  sem shortenMiddle : Int -> JSExpr -> JSExpr
  sem shortenMiddle n =
  | JSEVar _ & t -> _assign t (JSEApp {
      fun = JSEMember { expr = t, id = "slice" },
      args = [JSEInt { i = 0 }, JSEInt { i = negi n }],
      curried = false
    })

end
