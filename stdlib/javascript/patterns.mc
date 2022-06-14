include "bool.mc"
include "mexpr/ast.mc"
include "javascript/ast.mc"
include "javascript/operators.mc"

------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile = JSProgAst + NamedPat + SeqTotPat + SeqEdgePat +
                    RecordPat + DataPat + IntPat + OrPat +
                    CharPat + BoolPat + AndPat + NotPat

  -- Compile a single pattern without any binding operations.
  sem compileSinglePattern =
  | PatNamed { ident = ident } ->
    match ident with PName name then JSEVar { id = name }
    else JSEBool { b = true } -- Wildcard pattern name
  | PatInt { val = val } -> JSEInt { i = val }
  | PatBool { val = val } -> JSEBool { b = val }
  | PatRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr) then
        (sidToString sid, compileSinglePattern expr)
      else never in
    JSEObject {
      fields = map (compileField) fieldSeq
    }
  | PatSeqTot { pats = patterns } -> JSEArray {
      exprs = map compileSinglePattern patterns
    }

  sem compileBindingPattern (target: JSExpr) =
  | ( PatInt _
	  | PatBool _
	  ) & pat -> _binOp (JSOEq {}) [compileSinglePattern pat, target]
  | PatNamed _ & pat  ->
    let patExpr = compileSinglePattern pat in
    match patExpr with JSEVar _ then _assign patExpr target
    else patExpr -- Whildcard pattern, just return "true"
  | PatSeqEdge { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
    let hasPrefix = not (null prefix) in
    let hasMiddle = match middle with PName _ then true else false in
    let hasPostfix = not (null postfix) in
    let prefixExprs: [JSExpr] = map compileSinglePattern prefix in
    let middleExpr: JSExpr = compileSinglePattern (PatNamed { ident = middle, ty = ty, info = info }) in
    let postfixExprs: [JSExpr] = map compileSinglePattern postfix in
    switch (hasPrefix, hasMiddle, hasPostfix)
      case (false, false, false) then middleExpr
      case (true, false, false) then
        _assign (JSEArray { exprs = prefixExprs }) target
      case (true, true, false) then
        _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target
      case (true, true, true) then
        _binOp (JSOAnd {}) [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr)
        ]
        -- Todo: Also slice the middle array using `.slice(0, -length(postfix))` after the postfix match.
      case (false, true, true) then
        _binOp (JSOAnd {}) [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr)
        ]
        -- Todo: Also slice the middle array using `.slice(0, -length(postfix))` after the postfix match.
      case (false, true, false) then
        _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target
      case (false, false, true) then
        let tmpIgnore = JSEVar { id = nameSym "__ignore__" } in
        _binOp (JSOAnd {}) [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [tmpIgnore]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnore)
        ]
      case (true, false, true) then
        let tmpIgnore = JSEVar { id = nameSym "__ignore__" } in
        _binOp (JSOAnd {}) [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [tmpIgnore]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnore)
        ]
    end
  | pat ->
    _assign (compileSinglePattern pat) target


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


end

