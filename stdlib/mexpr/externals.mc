-- Various functions for manipulating externals in MExpr ASTs

include "ast.mc"
include "boot-parser.mc"

include "map.mc"
include "name.mc"

lang CollectExternals = ExtAst

  -- Collects all external definitions in a program and returns a
  -- map from external string identifiers to the variable names
  -- they introduce. For example,
  --
  --   external id : Float -> Float
  --
  -- results in a map entry from the string id to the introduced name id.
  sem collectExternals =
  | expr -> collectExternalsHelper (mapEmpty cmpString) expr

  sem collectExternalsHelper (acc: Map String Name) =
  | TmExt t & expr ->
    let str = nameGetStr t.ident in
    -- Assumption: No two externals have the same string identifier (this is
    -- enforced elsewhere)
    let acc = mapInsert str t.ident acc in
    sfold_Expr_Expr collectExternalsHelper acc expr
  | expr -> sfold_Expr_Expr collectExternalsHelper acc expr

end

lang ReadExternals = BootParser

  sem readExternals =
  | filename ->
    parseMCoreFile
      { defaultBootParserParseMCoreFileArg with eliminateDeadCode = false } filename

end

lang Test = CollectExternals + ReadExternals + BootParser
end

mexpr
use Test in

let _parse = parseMExprString [] in

let t = _parse "
  external extA : () -> () in
  external extB : Float -> Float in
  external extC : Int -> Float in
  ()
------------------------" in
utest collectExternals t with mapFromSeq cmpString [
  let str = "extA" in (str, nameNoSym str),
  let str = "extB" in (str, nameNoSym str),
  let str = "extC" in (str, nameNoSym str)
] using mapEq nameEq in

dprint (readExternals "ext/math-ext.mc");

()
