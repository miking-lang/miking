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

  sem compileBindingPattern (target: JSExpr) =
  | ( PatInt _
	  | PatBool _
	  ) & pat -> _binOp JSOEq {} [compileSinglePattern pat, target]
  | PatNamed _ & pat  ->
    let patExpr = compileSinglePattern pat in
    match patExpr with JSEVar _ then _assign patExpr target
    else patExpr -- Whildcard pattern, just return "true"
  | pat ->
    _assign (compileSinglePattern pat) target

end

