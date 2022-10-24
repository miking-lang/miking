include "bool.mc"
include "seq.mc"
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
  lam pats: [Pat]. lam target: JSExpr. lam checkExactInsteadOfAtLeast: Bool.
  let op = (if checkExactInsteadOfAtLeast then (JSOEq {}) else (JSOGe {})) in
  _binOp op [JSEMember { expr = target, id = "length" }, JSEInt { i = length pats }]

------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile = PatJSCompileLang

  -- Compile a single pattern without any binding operations.
  sem compileSinglePattern : CompileJSContext -> Pat -> (CompileJSContext, JSExpr, [JSExpr])
  sem compileSinglePattern ctx =
  | PatInt { val = val } -> (ctx, JSEInt { i = val }, [])
  | PatBool { val = val } -> (ctx, JSEBool { b = val }, [])
  | PatChar { val = val } -> (ctx, JSEChar { c = val}, [])
  | PatNamed { ident = PName name } ->
    let ctx = { ctx with declarations = setInsert name ctx.declarations }in
    (ctx, JSEVar { id = name }, [])
  | PatNamed { ident = PWildcard () } -> (ctx, tmpIgnoreJS, [])
  | PatSeqTot { pats = patterns } ->
    match safeMapSinglePattern ctx patterns with (ctx, elems, extra) in
    (ctx, JSEArray { exprs = elems }, extra)
  | PatRecord { bindings = bindings } -> match foldr (
      lam field: (SID, Pat). lam acc: (CompileJSContext, [(String, JSExpr)], [JSExpr]).
      match acc with (ctx, patts, extra) in
      match field with (sid, pat) in
      match safeCompileSinglePattern ctx pat with (ctx, patExpr, patExtras) in
      (ctx, cons (sidToString sid, patExpr) patts, concat patExtras extra)
    ) (ctx, [], []) (mapToSeq bindings) with (ctx, fields, extra) in
    (ctx, JSEObject { fields = fields }, extra)


  -- Safely compile a pattern that might contain a nested sequence or record pattern.
  sem safeCompileSinglePattern : CompileJSContext -> Pat -> (CompileJSContext, JSExpr, [JSExpr])
  sem safeCompileSinglePattern ctx =
  | ( PatInt _
    | PatBool _
    | PatChar _
    | PatSeqTot _
    | PatSeqEdge _
    | PatRecord _
    | PatCon _
    ) & p ->
    -- Replace the sequence pattern with a new variable
    let id = nameSym "_nstd" in
    let matchVar = JSEVar { id = id } in
    -- Add the undeclared variable to the context
    let ctx = { ctx with declarations = setInsert id ctx.declarations } in
    -- Compile "<p> = <matchVar>" as a new binding operation
    match compileBindingPattern ctx matchVar p with (ctx, matchBinding) in
    -- Append the new binding to the list of extra bindings
    -- and add the new variable to the list of elements in the patts list.
    (ctx, matchVar, [matchBinding])
  | p ->
    -- Append the new element to the list of elements
    -- and return the new list of elements and the extra bindings.
    compileSinglePattern ctx p


  -- Compile a list of patterns into a list of expressions and a list of extra bindings.
  -- Fold the patterns into a a tuple of two lists, one with the elements in the patterns,
  -- and one with the extra binding patterns for sequence or record patterns
  -- those are replaced with a new variable and compiled as an extra
  -- operation in the resulting match expression.
  sem safeMapSinglePattern : CompileJSContext -> [Pat] -> (CompileJSContext, [JSExpr], [JSExpr])
  sem safeMapSinglePattern ctx =
  | pats -> foldr (
      lam pat: Pat. lam acc: (CompileJSContext, [JSExpr], [JSExpr]).
      match acc with (ctx, patts, extra) in
      match safeCompileSinglePattern ctx pat with (ctx, patJS, extrasJS) in
      (ctx, cons patJS patts, concat extrasJS extra)
    ) (ctx, [], []) pats


  sem compileBindingPattern : CompileJSContext -> JSExpr -> Pat -> (CompileJSContext, JSExpr)
  sem compileBindingPattern ctx target =
  | PatNamed    { ident = PWildcard () } -> (ctx, JSEBool { b = true })
  | PatNamed    { ident = PName name } & p ->
    match compileSinglePattern ctx p with (ctx, pat, _) in
    (ctx, _assign pat target )
  | (PatInt _ | PatBool _ | PatChar _) & p ->
    match compileSinglePattern ctx p with (ctx, pat, []) in
    (ctx, _binOp (JSOEq {}) [target, pat])
  | ( PatSeqEdge _
    | PatRecord  _
    ) & p ->
    match compileSinglePattern ctx p with (ctx, pat, extra) in
    (ctx, _binOpM (JSOAnd {}) (cons (_assign (pat) target) extra) )
  | PatSeqTot { pats = pats } -> compilePats ctx pats target true
  | PatSeqEdge  { prefix = prefix, middle = middle, postfix = postfix, ty = ty, info = info } ->
    let hasPrefix = not (null prefix) in
    let hasMiddle = match middle with PName _ then true else false in
    let hasPostfix = not (null postfix) in
    match safeMapSinglePattern ctx prefix with (ctx, prefixExprs, prefixExtra) in
    match compileSinglePattern ctx (PatNamed { ident = middle, ty = ty, info = info }) with (ctx, middleExpr, []) in
    match safeMapSinglePattern ctx postfix with (ctx, postfixExprs, postfixExtra) in
    match (switch (hasPrefix, hasMiddle, hasPostfix)
      case (false, false, false) then (ctx, []) -- Should never happen
      case (true, false, false) then
        match compilePats ctx prefix target false with (ctx, prefixBinding) in
        (ctx, [prefixBinding])
      case (true, true, false) then
        (ctx, [_assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target])
      case (true, true, true) then
        (ctx, [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ])
      case (false, true, true) then
        (ctx, [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr middleExpr),
          shortenMiddle (length postfixExprs) middleExpr
        ])
      case (false, true, false) then
        (ctx, [_assign (JSEArray { exprs = [_unOp (JSOSpread {}) [middleExpr]] }) target])
      case (false, false, true) then
        (ctx, [
          _assign (JSEArray { exprs = [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ])
      case (true, false, true) then
        (ctx, [
          _assign (JSEArray { exprs = concat prefixExprs [_unOp (JSOSpread {}) [tmpIgnoreJS]] }) target,
          _assign (JSEArray { exprs = reverse postfixExprs }) (reverseExpr tmpIgnoreJS)
        ])
    end) with (ctx, exprs) in
    (ctx, _binOpM (JSOAnd {}) (join [exprs, prefixExtra, postfixExtra]) )
  | PatCon { ident = ident, subpat = subpat } ->
    let typeCheck = _binOp (JSOEq {}) [JSEMember { expr = target, id = "type" }, JSEString { s = ident.0 }] in
    match compileBindingPattern ctx (JSEMember { expr = target, id = "value" }) subpat with (ctx, valueAssign) in
    (ctx, _binOp (JSOAnd {}) [typeCheck, valueAssign] )
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


  sem compilePats : CompileJSContext -> [Pat] -> JSExpr -> Bool -> (CompileJSContext, JSExpr)
  sem compilePats ctx pats target =
  | checkExactInsteadOfAtLeast ->
    if _isCharPatSeq pats then (ctx, _binOp (JSOEq {}) [target, JSEString { s = _charPatSeq2String pats }] )
    else
      let lengthCheck = compilePatsLen pats target checkExactInsteadOfAtLeast in
      let allWildcards = forAll (lam p. match p with PatNamed { ident = PWildcard () } then true else false) pats in
      if allWildcards then (ctx, lengthCheck)
      else
        match safeMapSinglePattern ctx pats with (ctx, elems, extra) in
        (ctx, _binOpM (JSOAnd {}) (join [ [lengthCheck], [_assign (JSEArray { exprs = elems }) target], extra]) )

end
