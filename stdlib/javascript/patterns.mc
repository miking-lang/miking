include "bool.mc"
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
  sem compileSinglePattern (inSeq: Bool) =
  | PatNamed { ident = ident } ->
    match ident with PName name then JSEVar { id = name }
    else if inSeq then tmpIgnoreJS
    else JSEBool { b = true } -- Wildcard pattern name
  | PatInt { val = val } -> JSEInt { i = val }
  | PatBool { val = val } -> JSEBool { b = val }
  | PatRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr) then
        (sidToString sid, compileSinglePattern false expr)
      else never in
    JSEObject {
      fields = map (compileField) fieldSeq
    }
  | PatSeqTot { pats = patterns } -> JSEArray {
      exprs = map (compileSinglePattern true) patterns
    }
  -- | PatSeqEdge { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->


  sem compileBindingPattern (target: JSExpr) =
  | ( PatInt _
	  | PatBool _
	  ) & pat -> _binOp (JSOEq {}) [compileSinglePattern false pat, target]
  | PatNamed _ & pat  ->
    let patExpr = compileSinglePattern false pat in
    match patExpr with JSEVar _ then _assign patExpr target
    else patExpr -- Whildcard pattern, just return "true"
  | PatSeqEdge { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
    let hasPrefix = not (null prefix) in
    let hasMiddle = match middle with PName _ then true else false in
    let hasPostfix = not (null postfix) in
    let prefixExprs: [JSExpr] = map (compileSinglePattern true) prefix in
    let middleExpr: JSExpr = compileSinglePattern true (PatNamed { ident = middle, ty = ty, info = info }) in
    let postfixExprs: [JSExpr] = map (compileSinglePattern true) postfix in
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
        -- Todo: Also slice the middle array using `.slice(0, -length(postfix))` after the postfix match.
      case (false, true, true) then
        _binOpM (JSOAnd {}) [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ]
        -- Todo: Also slice the middle array using `.slice(0, -length(postfix))` after the postfix match.
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
  | pat ->
    _assign (compileSinglePattern false pat) target


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
