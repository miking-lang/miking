include "mexpr/attribute-grammar.mc"
include "common.mc"
include "seq.mc"
include "map.mc"

lang Invariant = AttributeGrammar
  sem printInvariantSummary : Attr Loc -> ()
  sem printInvariantSummary =
  | _ -> ()

  sem checkInvariants : [Attr Loc] -> Expr -> ()
  sem checkInvariants attrs = | ast ->
    let start = wallTimeMs () in
    let res = processAst attrs ast in
    let timeMs = subf (wallTimeMs ()) start in
    printLn (join ["  Invariants: associated attributes in ", float2string timeMs, "ms."]);
    mapFoldWithKey (lam. lam. lam attr. printInvariantSummary attr) () res
end
