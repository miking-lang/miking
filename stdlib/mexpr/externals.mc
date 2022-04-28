-- Various functions for manipulating externals in MExpr ASTs

include "ast.mc"
include "boot-parser.mc"
include "ast-builder.mc"
include "eq.mc"

include "map.mc"
include "name.mc"
include "sys.mc"

let _error = "Error in externals.mc: not an external in externalsMap"

lang Externals = ExtAst

  -- Collects all external definitions in a program and returns a
  -- map from external string identifiers to the variable names
  -- they introduce. For example,
  --
  --   external id : Float -> Float
  --
  -- results in a map entry from the string id to the introduced name id.
  sem collectExternals : Expr -> Map String Expr
  sem collectExternals =
  | expr -> collectExternalsHelper (mapEmpty cmpString) expr

  sem collectExternalsHelper : Map String Expr -> Expr -> Map String Expr
  sem collectExternalsHelper acc =
  | TmExt t & expr ->
    let str = nameGetStr t.ident in
    -- Assumption: No two externals have the same string identifier (this is
    -- enforced elsewhere)
    let acc = mapInsert str expr acc in
    sfold_Expr_Expr collectExternalsHelper acc expr
  | expr -> sfold_Expr_Expr collectExternalsHelper acc expr

  sem prependExternals : Map String Expr -> Expr -> Expr
  sem prependExternals externalsMap =
  | expr -> mapFoldWithKey (lam acc. lam _k. lam v.
        match v with TmExt t then TmExt { t with inexpr = acc }
        else error _error
      ) expr externalsMap

  sem mergeExternalsPreferLeft
    : Map String Expr -> Map String Expr -> Map String Expr
  sem mergeExternalsPreferLeft e1 =
  | e2 -> mapFoldWithKey (lam e2. lam k. lam v. mapInsert k v e2) e2 e1

end

lang MExprExternals = Externals + BootParser

  sem readExternalsFromFile : String -> Map String Expr
  sem readExternalsFromFile =
  | filename ->
    let tmpFile = sysTempFileMake () in
    writeFile tmpFile (join ["include \"", filename, "\""]);
    let r = collectExternals (parseMCoreFile
      { defaultBootParserParseMCoreFileArg
        with eliminateDeadCode = false } tmpFile) in
    sysDeleteFile tmpFile; r

end


lang Test = Externals + MExprExternals + MExprEq
end

-----------
-- TESTS --
-----------

mexpr
use Test in

let _externalsToNames: Map String Expr -> Map String Name = lam m.
  mapMap (lam v. match v with TmExt t then t.ident else error _error) m
in

-- Test collectExternals
let _testCollect = lam prog: String.
  let expr = parseMExprString [] prog in
  let m = collectExternals expr in
  _externalsToNames m
in

-- Top-level
let t = "
  external extA : () -> () in
  external extB : Float -> Float in
  external extC : Int -> Float in
  ()
------------------------" in
utest _testCollect t with mapFromSeq cmpString [
  let str = "extA" in (str, nameNoSym str),
  let str = "extB" in (str, nameNoSym str),
  let str = "extC" in (str, nameNoSym str)
] using mapEq nameEq in

-- Nested
let t = "
  let x =
    external extA : () -> () in
    external extB : Float -> Float in
    external extC : Int -> Float in
    ()
  in x
------------------------" in
utest _testCollect t with mapFromSeq cmpString [
  let str = "extA" in (str, nameNoSym str),
  let str = "extB" in (str, nameNoSym str),
  let str = "extC" in (str, nameNoSym str)
] using mapEq nameEq in

-- Test prependExternals
let _testPrepend: Map String Expr -> Expr = lam m. prependExternals m unit_ in
let _ext = lam str. lam inexpr. bind_ (ext_ str false tyunit_) inexpr in
recursive let _eqExtExpr: Expr -> Expr -> Bool = lam e1. lam e2.
  match (e1,e2) with (TmExt t1, TmExt t2) then
    if nameEq t1.ident t2.ident then _eqExtExpr t1.inexpr t2.inexpr
    else false
  else eqExpr e1 e2
in

utest _testPrepend (mapFromSeq cmpString [
  let str = "extA" in (str, _ext str unit_),
  let str = "extB" in (str, _ext str (int_ 1)), -- The inexpr (int) is ignored
  let str = "extC" in (str, _ext str unit_)
]) with bindall_ [
  _ext "extC" unit_,
  _ext "extB" unit_,
  _ext "extA" unit_,
  unit_
] using _eqExtExpr in

-- Test mergeExternalsPreferLeft
let _testMerge = lam m1: Map String Name. lam m2: Map String Name.
  let m1 = mapMap (lam v. next_ v false tyunit_) m1 in
  let m2 = mapMap (lam v. next_ v false tyunit_) m2 in
  let m = mergeExternalsPreferLeft m1 m2 in
  _externalsToNames m
in

let extNameA = nameSym "extA" in
let extNameB = nameSym "extB" in
let extNameC = nameSym "extC" in
let extNameD = nameSym "extD" in
let extNameE = nameSym "extE" in
utest _testMerge (mapFromSeq cmpString [
  ("extA", extNameA),
  ("extB", extNameB),
  ("extC", extNameC)
]) (mapFromSeq cmpString [
  ("extA", nameSym "extA"),
  ("extD", extNameD),
  ("extE", extNameE)
]) with (mapFromSeq cmpString [
  ("extA", extNameA),
  ("extB", extNameB),
  ("extC", extNameC),
  ("extD", extNameD),
  ("extE", extNameE)
]) using mapEq nameEq in

()
