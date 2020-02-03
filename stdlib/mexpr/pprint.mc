include "option.mc"
include "seq.mc"
include "string.mc"

include "mexpr/ast.mc"

let spacing = lam indent. makeseq indent ' '
let newline = lam indent. concat "\n" (spacing indent)

-- Set spacing on increment
let incr = lam indent. addi indent 4

lang VarPrettyPrint = VarAst
	sem pprintCode (indent : Int) =
	| TmVar x -> x

	sem pprintAst (indent : Int) =
	| TmVar x -> strJoin "" ["TmVar \"", x, "\""]
end

lang AppPrettyPrint = AppAst
	sem pprintCode (indent : Int) =
	| TmApp t ->
	  let l = pprintCode indent t.0 in
	  let r = pprintCode indent t.1 in
	  strJoin "" ["(", l, " ", r, ")"]

	sem pprintAst (indent : Int) =
	| TmApp t ->
	  let newind = incr indent in
	  let l = pprintAst newind t.0 in
	  let r = pprintAst newind t.1 in
	  strJoin "" ["TmApp (\n", spacing newind, l, ",\n", spacing newind, r, "\n", spacing indent, ")"]
end

lang FunPrettyPrint = FunAst
	sem pprintCode (indent : Int) =
	| TmLam t ->
	  let name = t.0 in
	  let body = pprintCode indent t.2 in
	  strJoin "" ["lam ", name, ".\n", spacing indent, body]

	sem pprintAst (indent : Int) =
	| TmLam t ->
	  let newind = incr indent in
	  let name = t.0 in
	  let body = pprintAst newind t.2 in
	  strJoin "" ["TmLam (\"", name, "\", None,\n", spacing newind, body, "\n", spacing indent, ")"]
end

lang LetPrettyPrint = LetAst
	sem pprintCode (indent : Int) =
	| TmLet t ->
	  let name = t.0 in
	  let bodyexpr = pprintCode (incr indent) t.2 in
	  let inexpr = pprintCode indent t.3 in
	  strJoin "" ["let ", name, " = \n", spacing (incr indent), bodyexpr, "\n", spacing indent, "in\n", spacing indent, inexpr]

	sem pprintAst (indent : Int) =
	| TmLet t ->
	  let newind = incr indent in
	  let name = t.0 in
	  let bodyexpr = pprintAst newind t.2 in
	  let inexpr = pprintAst newind t.3 in
	  strJoin "" ["TmLet (\"", name, "\", None,\n", spacing newind, bodyexpr, ",\n", spacing newind, inexpr, "\n", spacing indent, ")"]
end

lang RecLetsPrettyPrint = RecLetsAst
	sem pprintCode (indent : Int) =
	| TmRecLets t ->
	  let lets = t.0 in
	  let inexpr = pprintCode indent t.1 in
	  let pprintLets = lam acc. lam l.
	  	let name = l.0 in
	  	let body = pprintCode (incr (incr indent)) l.2 in
	  	strJoin "" [acc, newline (incr indent), "let ", name, " =", newline (incr (incr indent)), body]
	  in
	  strJoin "" [foldl pprintLets "recursive" lets, newline indent, "in", newline indent, inexpr]

	sem pprintAst (indent : Int) =
	| TmRecLets t ->
	  let newind = incr indent in
	  let lets = t.0 in
	  let inexpr = pprintAst newind t.1 in
	  let pprintLets = lam acc. lam l.
	  	let name = l.0 in
	  	let body = pprintAst (incr (incr newind)) l.2 in
	  	let s = strJoin "" [newline (incr newind), "(\"", name, "\", None,", newline (incr (incr newind)), body, newline (incr newind), ")"] in
	  	concat acc [s]
	  in
	  let lstr = strJoin "," (foldl pprintLets [] lets) in
	  strJoin "" ["TmRecLets ([", lstr, newline newind, "],", newline newind, inexpr, newline indent, ")"]
end

lang ConstPrettyPrint = ConstAst
	sem getConstStringCode (indent : Int) =
	-- intentionally left blank

	sem getConstStringAst (indent : Int) =
	-- intentionally left blank

	sem pprintCode (indent : Int) =
	| TmConst c -> getConstStringCode indent c

	sem pprintAst (indent : Int) =
	| TmConst c -> strJoin "" ["TmConst (", getConstStringAst indent c, ")"]
end

lang UnitPrettyPrint = UnitAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CUnit -> "()"

	sem getConstStringAst (indent : Int) =
	| CUnit -> "CUnit"
end

lang IntPrettyPrint = IntAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CInt i -> int2string i

	sem getConstStringAst (indent : Int) =
	| CInt i -> strJoin "" ["CInt ", int2string i]
end

lang ArithIntPrettyPrint = ArithIntAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CAddi -> "addi"
	| CAddi2 i -> strJoin "" ["(addi ", int2string i, ")"]

	sem getConstStringAst (indent : Int) =
	| CAddi -> "CAddi"
	| CAddi2 i -> strJoin "" ["CAddi2 ", int2string i]
end

lang BoolPrettyPrint = BoolAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CBool b -> if b then "true" else "false"
	| CNot -> "not"
	| CAnd -> "and"
	| CAnd2 b -> strJoin "" ["(and ", getConstStringCode indent b, ")"]
	| COr -> "or"
	| COr2 b -> strJoin "" ["(or ", getConstStringCode indent b, ")"]

	sem getConstStringAst (indent : Int) =
	| CBool b -> strJoin "" ["CBool ", if b then "true" else "false"]
	| CNot -> "CNot"
	| CAnd -> "CAnd"
	| CAnd2 b -> strJoin "" ["CAnd ", if b then "true" else "false"]
	| COr -> "COr"
	| COr2 b -> strJoin "" ["COr ", if b then "true" else "false"]

	sem pprintCode (indent : Int) =
	| TmIf t ->
	  let cond = pprintCode indent t.0 in
	  let thn = pprintCode (incr indent) t.1 in
	  let els = pprintCode (incr indent) t.2 in
	  strJoin "" ["if ", cond, " then\n", spacing (incr indent), thn "\n", spacing indent,
	                            "else\n", spacing (incr indent), els]

	sem pprintAst (indent : Int) =
	| TmIf t ->
	  let newind = incr indent in
	  let cond = pprintAst newind t.0 in
	  let thn = pprintAst newind t.1 in
	  let els = pprintAst newind t.2 in
	  strJoin "" ["TmIf (\n", spacing newind, cond, ",\n", spacing newind, thn, ",\n", spacing newind, els, "\n", spacing indent, ")"]
end

lang CmpPrettyPrint = CmpAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CEqi -> "eqi"
	| CEqi2 i -> strJoin "" ["(eqi ", int2string i, ")"]

	sem getConstStringAst (indent : Int) =
	| CEqi -> "CEqi"
	| CEqi2 i -> strJoin "" ["CEqi2 ", int2string i]
end

lang SeqPrettyPrint = SeqAst + ConstPrettyPrint
	sem getConstStringCode (indent : Int) =
	| CNth -> "nth"
	| CNth2 tms -> strJoin "" ["(nth ", pprintCode indent (TmSeq tms), ")"]
	| CSeq tms -> pprintCode indent (TmSeq tms)

	sem getConstStringAst (indent : Int) =
	| CNth -> "CNth"
	| CNth2 tms ->
	  let newind = incr indent in
	  if gti (length tms) 0 then
	    let tmsstr = strJoin (concat ",\n" (indent newind)) (map (pprintAst newind) tms) in
	    strJoin "" ["CNth2 [\n", spacing newind, tmsstr, "\n", spacing indent, "]"]
	  else
	    "CNth2 []"
	| CSeq tms ->
	  let newind = incr indent in
	  if gti (length tms) 0 then
	    let tmsstr = strJoin (concat ",\n" (indent newind)) (map (pprintAst newind) tms) in
	    strJoin "" ["CSeq [\n", spacing newind, tmsstr, "\n", spacing indent, "]"]
	  else
	    "CSeq []"

	sem pprintCode (indent : Int) =
	| TmSeq tms -> strJoin "" ["[", strJoin ", " (map (pprintCode indent) tms), "]"]

	sem pprintAst (indent : Int) =
	| TmSeq tms ->
	  let newind = incr indent in
	  if gti (length tms) 0 then
	    let tmsstr = strJoin (concat ",\n" (indent newind)) (map (pprintAst newind) tms) in
	    strJoin "" ["TmSeq [\n", spacing newind, tmsstr, "\n", spacing indent, "]"]
	  else
	    "TmSeq []" -- strJoin "" ["TmSeq (", strJoin ", " (map pprintAst tms), ")"]
end

lang TuplePrettyPrint = TupleAst
	sem pprintCode (indent : Int) =
	| TmTuple tms -> strJoin "" ["(", strJoin ", " (map (pprintCode indent) tms), ")"]
	| TmProj t -> strJoin "" [pprintCode indent t.0, ".", int2string t.1]

	sem pprintAst (indent : Int) =
	| TmTuple tms ->
	  let newind = incr indent in
	  if gti (length tms) 0 then
	    let tmsstr = strJoin (concat ",\n" (indent newind)) (map (pprintAst newind) tms) in
	    strJoin "" ["TmTuple [\n", spacing newind, tmsstr, "\n", spacing indent, "]"]
	  else
	    "TmTuple (_)" -- strJoin "" ["TmTuple (", strJoin ", " (map pprintAst tms), ")"]
	| TmProj t ->
	  let newind = incr indent in
	  strJoin "" ["TmProj (\n", spacing newind, pprintAst newind t.0, ",\n", spacing newind, int2string t.1, "\n", spacing indent, ")"]
end

lang DataPrettyPrint = DataAst
	sem pprintCode (indent : Int) =
	| TmConDef t ->
	  let name = t.0 in
	  let body = pprintCode indent t.1 in
	  strJoin "" ["con ", name, " in\n", spacing indent, body]

	sem pprintAst (indent : Int) =
	| TmConDef t ->
	  let newind = incr indent in
	  let name = t.0 in
	  let body = pprintAst newind t.1 in
	  strJoin "" ["TmConDef (\"", name, "\",\n", spacing newind, body, "\n", spacing indent, ")"]
end

lang MatchPrettyPrint = MatchAst
	sem pprintCode (indent : Int) =
	| TmMatch t ->
	  let target = pprintCode indent t.0 in
	  -- This is outdated, update it with the new pattern syntax
	  -- (Though I am unsure about how it looks when parsed...)
	  let k2 = t.1 in
	  let x = t.2 in
	  let _ = error "TmMatch not yet implemented for pretty printer." in
	  let thn = pprintCode (incr indent) t.3 in
	  let els = pprintCode (incr indent) t.4 in
	  strJoin "" ["match ", target, " with ", k2, " ", x, " then\n",
	              spacing (incr indent), thn, "\n", spacing indent, "else\n",
	              spacing (incr indent), els]

	sem pprintAst (indent : Int) =
	| TmMatch t ->
	  let newind = incr indent in
	  let target = pprintAst newind t.0 in
	  -- Same issue as for pprintCode
	  let k2 = t.1 in
	  let x = t.2 in
	  let _ = error "TmMatch not yet implemented for pretty printer." in
	  let thn = pprintAst newind t.3 in
	  let els = pprintAst newind t.4 in
	  strJoin "" ["TmMatch (\n", spacing newind target, ",\n",
	              spacing newind, "\"", k2, "\", \"", x, "\",\n",
	              spacing newind, thn, ",\n",
	              spacing newind, els, "\n", spacing indent, ")"]
end

lang UtestPrettyPrint = UtestAst
	sem pprintCode (indent : Int) =
	| TmUtest t ->
	  let test = pprintCode indent t.0 in
	  let expected = pprintCode indent t.1 in
	  let next = pprintCode indent t.2 in
	  strJoin "" ["utest ", test, " with ", expected, " in\n", spacing indent, next]

	sem pprintAst (indent : Int) =
	| TmUtest t ->
	  let newind = incr indent in
	  let test = pprintAst newind t.0 in
	  let expected = pprintAst newind t.1 in
	  let next = pprintAst newind t.2 in
	  strJoin "" ["TmUtest (\n",
	              spacing newind, test, ",\n",
	              spacing newind, expected, ",\n",
	              spacing newind, next, "\n", spacing indent, ")"]
end

lang MExprPrettyPrint = VarPrettyPrint + AppPrettyPrint + FunPrettyPrint +
                        LetPrettyPrint + RecLetsPrettyPrint + ConstPrettyPrint +
                        UnitPrettyPrint + IntPrettyPrint + ArithIntPrettyPrint +
                        BoolPrettyPrint + CmpPrettyPrint + SeqPrettyPrint +
                        TuplePrettyPrint + DataPrettyPrint + MatchPrettyPrint +
                        UtestPrettyPrint

mexpr
use MExprPrettyPrint in
let simple_ast =
    TmLet ("foo", None,
      TmLam ("a", None, TmLam ("b", None,
        TmLet ("bar", None,
          TmLam ("x", None,
            TmApp (
              TmApp (
                TmVar "addi",
                TmVar "b"
              ),
              TmVar "x"
            )
          ),
          TmLet ("babar", None,
            TmConst (CInt 3),
            TmApp (
              TmApp (
                TmVar "addi",
                TmApp (
                  TmVar "bar",
                  TmVar "babar"
                )
              ),
              TmVar "a"
            )
          )
        )
      )),
      TmConst CUnit
    )
in

--let _ = print "\n\n" in
--let _ = print (pprintCode 0 simple_ast) in
--let _ = print "\n\n" in
--let _ = print (pprintAst 0 simple_ast) in
--let _ = print "\n\n" in

utest geqi (length (pprintCode 0 simple_ast)) 0 with true in
utest geqi (length (pprintAst 0 simple_ast)) 0 with true in
()
