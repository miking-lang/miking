include "bool.mc"
include "seq.mc"
include "error.mc"
include "common.mc"
include "stringid.mc"
include "mexpr/ast.mc"
include "javascript/ast.mc"
include "javascript/util.mc"


------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile =
  JSProgAst + NamedPat + SeqTotPat + SeqEdgePat + RecordPat + DataPat +
  IntPat + OrPat + CharPat + BoolPat + AndPat + NotPat

  sem getPatNameVar : PatName -> JSExpr
  sem getPatNameVar =
  | PWildcard _ -> JSEVar {id = nameSym "_"}
  | PName name -> JSEVar {id = name}

  sem namedPatExpr : Pat -> JSExpr
  sem namedPatExpr =
  | PatNamed {ident = id} -> getPatNameVar id
  | pat -> errorSingle [infoPat pat] "Expected PatNamed in JS pattern compilation"

  -- Compiles a pattern match of the provided target and pattern. The resulting
  -- condition evaluates to true if they match and binds the variables of the
  -- pattern within the conditional expression.
  sem compilePattern : CompileJSContext -> JSExpr -> Pat -> (CompileJSContext, JSExpr)
  sem compilePattern ctx target =
  | PatNamed {ident = PWildcard _} ->
    (ctx, _binOp (JSOEq ()) [target, JSEBool {b = true}])
  | PatNamed {ident = PName name} ->
    -- NOTE(larshum, 2022-12-19): We first assign the target to the variable
    -- defined in the pattern. Then we OR this with true, so that the
    -- conditional always results in true.
    (ctx, _binOp (JSOOr ()) [_assign (JSEVar {id = name}) target, JSEBool {b = true}])
  | PatInt {val = val} ->
    (ctx, _binOp (JSOEq ()) [target, JSEInt {i = val}])
  | PatBool {val = val} ->
    (ctx, _binOp (JSOEq ()) [target, JSEBool {b = val}])
  | PatChar {val = val} ->
    (ctx, _binOp (JSOEq ()) [target, JSEChar {c = val}])
  | PatRecord {bindings = bindings} ->
    let objectFields =
      mapFoldWithKey
        (lam acc. lam id. lam p. cons (sidToString id, namedPatExpr p) acc)
        [] bindings in
    (ctx, _binOp (JSOOr ()) [
      _assign (JSEObject {fields = objectFields}) target, JSEBool {b = true}])
  | PatSeqTot {pats = pats} ->
    let lengthCond = _binOp (JSOEq ()) [
      JSEMember {expr = target, id = "length"}, JSEInt {i = length pats}] in
    let bindingExpr = _assign (JSEArray { exprs = map namedPatExpr pats }) target in
    (ctx, _binOp (JSOAnd ()) [lengthCond, bindingExpr])
  | PatSeqEdge t ->
    let minSeqLength = addi (length t.prefix) (length t.postfix) in
    let lengthCond = _binOp (JSOGe ()) [
      JSEMember {expr = target, id = "length"}, JSEInt {i = minSeqLength}] in
    let prefixExprs = map namedPatExpr t.prefix in
    let middleExpr = getPatNameVar t.middle in
    let postfixExprs = map namedPatExpr t.postfix in
    let bindingExprs = [
      _assign (JSEArray {exprs = snoc prefixExprs (_unOp (JSOSpread ()) [middleExpr])}) target,
      _assign (JSEArray {exprs = reverse postfixExprs}) (reverseExpr middleExpr),
      shortenMiddle (length postfixExprs) middleExpr] in
    (ctx, _binOpM (JSOAnd ()) (cons lengthCond bindingExprs))
  | PatCon t ->
    let ty = JSEMember {expr = target, id = "type"} in
    let strTy = JSEString {s = nameGetStr t.ident} in
    let valueMatch = _binOp (JSOOr ()) [
      _assign (JSEMember {expr = target, id = "value"}) (namedPatExpr t.subpat),
      JSEBool {b = true}] in
    (ctx, _binOp (JSOAnd ()) [_binOp (JSOEq {}) [ty, strTy], valueMatch])
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
