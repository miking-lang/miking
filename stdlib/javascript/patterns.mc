include "bool.mc"
include "error.mc"
include "common.mc"
include "stringid.mc"
include "mexpr/ast.mc"
include "javascript/ast.mc"
include "javascript/util.mc"


lang PatJSCompileLang = JSProgAst + NamedPat + SeqTotPat + SeqEdgePat +
                    RecordPat + DataPat + IntPat + OrPat +
                    CharPat + BoolPat + AndPat + NotPat
end

let tmpIgnoreJS = use PatJSCompileLang in
  JSEVar { id = nameSym "_" }

let compilePatsLen = use PatJSCompileLang in
  lam pats: [Pat]. lam target: JSExpr.
  _binOp (JSOEq {}) [JSEMember { expr = target, id = "length" }, JSEInt { i = length pats }]

------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile = PatJSCompileLang

  -- Compile a single pattern without any binding operations.
  sem compileSinglePattern : Pat -> (JSExpr, [JSExpr])
  sem compileSinglePattern =
  | PatInt { val = val } -> (JSEInt { i = val }, [])
  | PatBool { val = val } -> (JSEBool { b = val }, [])
  | PatChar { val = val } -> (JSEChar { c = val}, [])
  | PatNamed { ident = PName name } -> (JSEVar { id = name }, [])
  | PatNamed { ident = PWildcard () } -> (tmpIgnoreJS, [])
  | PatSeqTot { pats = patterns } ->
    match safeMapSinglePattern patterns with (elems, extra) in
    (JSEArray { exprs = elems }, extra)
  | PatRecord { bindings = bindings } -> match foldr (
      lam field: (SID, Pat). lam acc: ([(String, JSExpr)], [JSExpr]).
      match acc with (patts, extra) in
      match field with (sid, pat) in
      match safeCompileSinglePattern pat with (patExpr, patExtras) in
      (cons (sidToString sid, patExpr) patts, concat patExtras extra)
    ) ([], []) (mapToSeq bindings) with (fieldsExprs, extra) in
    (JSEObject { fields = fieldsExprs }, extra)


  -- Safely compile a pattern that might contain a nested sequence or record pattern.
  sem safeCompileSinglePattern : Pat -> (JSExpr, [JSExpr])
  sem safeCompileSinglePattern =
  | (PatSeqTot _ | PatSeqEdge _ | PatRecord  _) & p ->
    -- Replace the sequence pattern with a new variable
    let matchVar = JSEVar { id = nameSym "_nstd" } in
    -- Compile "<p> = <matchVar>" as a new binding operation
    let matchBinding = compileBindingPattern matchVar p in
    -- Append the new binding to the list of extra bindings
    -- and add the new variable to the list of elements in the patts list.
    (matchVar, [matchBinding])
  | p ->
    -- Append the new element to the list of elements
    -- and return the new list of elements and the extra bindings.
    compileSinglePattern p


  -- Compile a list of patterns into a list of expressions and a list of extra bindings.
  -- Fold the patterns into a a tuple of two lists, one with the elements in the patterns,
  -- and one with the extra binding patterns for sequence or record patterns
  -- those are replaced with a new variable and compiled as an extra
  -- operation in the resulting match expression.
  sem safeMapSinglePattern : [Pat] -> ([JSExpr], [JSExpr])
  sem safeMapSinglePattern =
  | pats -> foldr (
      lam pat: Pat. lam acc: ([JSExpr], [JSExpr]).
      match acc with (patts, extra) in
      match safeCompileSinglePattern pat with (patJS, extrasJS) in
      (cons patJS patts, concat extrasJS extra)
    ) ([], []) pats


  sem compileBindingPattern : JSExpr -> Pat -> JSExpr
  sem compileBindingPattern (target: JSExpr) =
  | PatNamed    { ident = PWildcard () } -> JSEBool { b = true }
  | (PatInt _ | PatBool _ | PatChar _) & p ->
    match compileSinglePattern p with (pat, []) in
    _binOp (JSOEq {}) [target, pat]
  | ( PatNamed { ident = PName _ }
    | PatSeqEdge _
    | PatRecord  _
    ) & p ->
    match compileSinglePattern p with (pat, extra) in
    _binOpM (JSOAnd {}) (cons (_assign (pat) target) extra)
  | PatSeqTot { pats = pats } & p ->
    if _isCharPatSeq pats then
      let str: String = _charPatSeq2String pats in
     _binOp (JSOEq {}) [target, JSEString { s = str }]
    else
      -- Check if the sequence is empty
      let lengthCheck = compilePatsLen pats target in
      if null pats then lengthCheck
      else
        match compileSinglePattern p with (pat, extra) in
        _binOpM (JSOAnd {}) (join [ [lengthCheck], [_assign (pat) target], extra])
  | PatSeqEdge  { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
    let hasPrefix = not (null prefix) in
    let hasMiddle = match middle with PName _ then true else false in
    let hasPostfix = not (null postfix) in
    match safeMapSinglePattern prefix with (prefixExprs, prefixExtra) in
    match compileSinglePattern (PatNamed { ident = middle, ty = ty, info = info }) with (middleExpr, []) in
    match safeMapSinglePattern postfix with (postfixExprs, postfixExtra) in
    let exprs: [JSExpr] = switch (hasPrefix, hasMiddle, hasPostfix)
      case (false, false, false) then [] -- Should never happen
      case (true, false, false) then
        [_assign (JSEArray { exprs = prefixExprs }) target]
      case (true, true, false) then
        [_assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target]
      case (true, true, true) then
        [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ]
      case (false, true, true) then
        [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ]
      case (false, true, false) then
        [_assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target]
      case (false, false, true) then
        [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ]
      case (true, false, true) then
        [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ]
    end in
    _binOpM (JSOAnd {}) (join [exprs, prefixExtra, postfixExtra])
  | pat ->
    dprintLn pat;
    errorSingle [infoPat pat] "Pattern not supported when compiling to JavaScript."


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
