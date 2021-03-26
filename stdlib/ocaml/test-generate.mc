include "generate.mc"
include "process-helpers.mc"
include "mexpr/boot-parser.mc"

mexpr

use OCamlTest in

-- Test semantics

-- Parse helper
let parseAsMExpr = lam s.
  use BootParser in
  parseMExprString s
  -- use MExprParser in parseExpr (initPos "") s
in

let ocamlEvalPrint = lam strConvert. lam p.
  let res =
    ocamlCompileWithConfig {warnings=false}
                           (join ["print_string (", strConvert, "(", p, "))"])
  in
  let out = (res.run "" []).stdout in
  res.cleanup ();
  parseAsMExpr out
in

let ocamlEvalPrintInt = ocamlEvalPrint "string_of_int" in

let bootEvalPrint = lam strConvert. lam p.
  let p =
    join ["include \"string.mc\" mexpr print (", strConvert, "(", p, "))"]
  in
  let td = phTempDirMake () in
  let dir = phTempDirName td in
  let dir = "/tmp" in
  let pfile = phJoinPath dir "program.mc" in

  phWriteToFile p pfile;

  let command = ["mi", "program.mc"] in
  let r = phRunCommand command "" dir in
  if neqi r.returncode 0 then
     print (join ["'mi' failed on program:\n\n",
            phReadFile pfile,
            "\n\nexit code: ",
            int2string r.returncode,
            "\n\nstandard error:\n", r.stderr]);
      phTempDirDelete td;
      exit 1
  else
    let out = r.stdout in
    phTempDirDelete td;
    parseAsMExpr out
in

let bootEvalPrintInt = bootEvalPrint "int2string" in

-- NOTE(oerikss, 2021-03-05): We pre- pretty-print the premable here to make
-- the test run faster. This is an ugly hack!
let premableStr =
  let str = expr2str (bind_ _preamble (int_ 0)) in
  let len = length str in
  subsequence str 0 (subi len 1)
in

-- NOTE(oerikss, 2021-03-05): Here we paste the pre- pretty-printed preamable
-- to our program. This is part of the above mentioned hack.
let ocamlExpr2str = lam ast.
  concat premableStr (expr2str ast)
in

let objWrapGenerate = lam a. _objWrapNoPremable (generate a) in

let mexpr2str = lam ast.
  use MExprPrettyPrint in
  expr2str ast
in

let bootInt = lam ast. bootEvalPrintInt (mexpr2str ast) in
let ocamlInt = lam ast.
  ocamlEvalPrintInt (ocamlExpr2str (objWrapGenerate ast))
in

-- -- Match
-- let matchChar1 = symbolize
--  (match_ (char_ 'a')
--    (pchar_ 'a')
--    true_
--    false_) in
-- utest matchChar1 with objWrapGenerate matchChar1 using sameSemantics in

--  let matchChar2 = symbolize
--    (match_ (char_ 'a')
--      (pchar_ 'b')
--      true_
--      false_) in
--  utest matchChar2 with objWrapGenerate matchChar2 using sameSemantics in

-- let matchSeq = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest matchSeq with objWrapGenerate matchSeq using sameSemantics in

-- let noMatchSeq1 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2, int_ 3])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeq1 with objWrapGenerate noMatchSeq1 using sameSemantics in

-- let noMatchSeqLen = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeqLen with objWrapGenerate noMatchSeqLen using sameSemantics in

-- let noMatchSeqLen2 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pseqtot_ [pint_ 1, pvar_ "a", pvar_ "b"])
--     (addi_ (var_ "a") (var_ "b"))
--     (int_ 42)) in
-- utest noMatchSeqLen2 with objWrapGenerate noMatchSeqLen2 using sameSemantics in

-- let matchOr1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr1 with objWrapGenerate matchOr1 using sameSemantics in

-- let matchOr2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 1])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr2 with objWrapGenerate matchOr2 using sameSemantics in

-- let matchOr3 = symbolize
--   (match_ (seq_ [int_ 3, int_ 1])
--     (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchOr3 with objWrapGenerate matchOr3 using sameSemantics in

-- let matchNestedOr1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr1 with objWrapGenerate matchNestedOr1 using sameSemantics in

-- let matchNestedOr2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 1])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr2 with objWrapGenerate matchNestedOr2 using sameSemantics in

-- let matchNestedOr3 = symbolize
--   (match_ (seq_ [int_ 3, int_ 7])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr3 with objWrapGenerate matchNestedOr3 using sameSemantics in

-- let matchNestedOr4 = symbolize
--   (match_ (seq_ [int_ 4, int_ 7])
--     (por_ (por_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ [pint_ 2, pvar_ "a"]))
--           (pseqtot_ [pint_ 3, pvar_ "a"]))
--     (var_ "a")
--     (int_ 42)) in
-- utest matchNestedOr4 with objWrapGenerate matchNestedOr4 using sameSemantics in

-- let matchNot1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--     true_
--     false_) in
-- utest matchNot1 with objWrapGenerate matchNot1 using sameSemantics in

-- let matchNot2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2])
--     (pnot_ (pseqtot_ [pint_ 1, pvar_ "a"]))
--     true_
--     false_) in
-- utest matchNot2 with objWrapGenerate matchNot2 using sameSemantics in

-- let matchAnd1 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--     (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--     (int_ 53)) in
-- utest matchAnd1 with objWrapGenerate matchAnd1 using sameSemantics in

-- let matchAnd2 = symbolize
--   (match_ (seq_ [int_ 2, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pvar_ "b"))
--     (addi_ (var_ "a") (get_ (var_ "b") (int_ 1)))
--     (int_ 53)) in
-- utest matchAnd2 with objWrapGenerate matchAnd2 using sameSemantics in

-- let matchAnd3 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ [pint_ 1, pvar_ "a"]) (pseqtot_ []))
--     (var_ "a")
--     (int_ 53)) in
-- utest matchAnd3 with objWrapGenerate matchAnd3 using sameSemantics in

-- let matchAnd4 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pand_ (pseqtot_ []) (pseqtot_ [pint_ 1, pvar_ "a"]))
--     (var_ "a")
--     (int_ 53)) in
-- utest matchAnd4 with objWrapGenerate matchAnd4 using sameSemantics in

-- let matchSeqEdge1 = symbolize
--   (match_ (seq_ [int_ 1])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge1 with objWrapGenerate matchSeqEdge1 using sameSemantics in

-- let matchSeqEdge2 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge2 with objWrapGenerate matchSeqEdge2 using sameSemantics in

-- let matchSeqEdge3 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3])
--     (pseqedge_ [pvar_ "a"] "b" [pvar_ "c"])
--     (addi_ (var_ "a") (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge3 with objWrapGenerate matchSeqEdge3 using sameSemantics in

-- let matchSeqEdge4 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (pseqedge_ [pvar_ "a", pvar_ "d"] "b" [pvar_ "c"])
--     (addi_ (addi_ (var_ "d") (var_ "a")) (var_ "c"))
--     (int_ 75)) in
-- utest matchSeqEdge4 with objWrapGenerate matchSeqEdge4 using sameSemantics in

-- let matchSeqEdge5 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [pint_ 1] "b" []))
--     (match_ (var_ "b")
--       (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--       (addi_ (var_ "a") (var_ "c"))
--       (int_ 84))
--     (int_ 75)) in
-- utest matchSeqEdge5 with objWrapGenerate matchSeqEdge5 using sameSemantics in

-- let matchSeqEdge6 = symbolize
--   (match_ (seq_ [int_ 1, int_ 2, int_ 3, int_ 4])
--     (por_ (pseqedge_ [pint_ 2] "b" []) (pseqedge_ [] "b" [pint_ 4]))
--     (match_ (var_ "b")
--       (pseqedgew_ [pvar_ "a"] [pvar_ "c"])
--       (addi_ (var_ "a") (var_ "c"))
--       (int_ 84))
--     (int_ 75)) in
-- utest matchSeqEdge6 with objWrapGenerate matchSeqEdge6 using sameSemantics in

-- let matchSeqEdge7 = symbolize
--   (match_ (seq_ [int_ 1])
--     (pseqedgew_ [pvar_ "a"] [])
--     (var_ "a")
--     (int_ 75)) in
-- utest matchSeqEdge7 with objWrapGenerate matchSeqEdge7 using sameSemantics in

-- Ints
let addInt1 = addi_ (int_ 1) (int_ 2) in
utest bootInt addInt1 with ocamlInt addInt1 in

let addInt2 = addi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
utest bootInt addInt2 with ocamlInt addInt2 in

let testMulInt = muli_ (int_ 2) (int_ 3) in
utest bootInt testMulInt with ocamlInt testMulInt in

let testModInt = modi_ (int_ 2) (int_ 3) in
utest bootInt testModInt with ocamlInt testModInt in

let testDivInt = divi_ (int_ 2) (int_ 3) in
utest bootInt testDivInt with ocamlInt testDivInt in

let testNegInt = addi_ (int_ 2) (negi_ (int_ 2)) in
utest bootInt testNegInt with ocamlInt testNegInt in

-- let compareInt1 = eqi_ (int_ 1) (int_ 2) in
-- utest bootInt compareInt1 with ocamlInt compareInt1 in

-- let compareInt2 = lti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest bootInt compareInt2 with ocamlInt compareInt2 in

-- let compareInt3 = leqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest bootInt compareInt3 with ocamlInt compareInt3 in

-- let compareInt4 = gti_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest bootInt compareInt4 with ocamlInt compareInt4 in

-- let compareInt5 = geqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest bootInt compareInt5 with ocamlInt compareInt5 in

-- let compareInt6 = neqi_ (addi_ (int_ 1) (int_ 2)) (int_ 3) in
-- utest bootInt compareInt6 with ocamlInt compareInt6 in

-- let shiftInt1 = slli_ (int_ 5) (int_ 2) in
-- utest bootInt shiftInt1 with ocamlInt shiftInt1 in

-- let shiftInt2 = srli_ (int_ 5) (int_ 2) in
-- utest bootInt shiftInt2 with ocamlInt shiftInt2 in

-- let shiftInt3 = srai_ (int_ 5) (int_ 2) in
-- utest bootInt shiftInt3 with ocamlInt shiftInt3 in

-- ---- Floats
-- let addFloat1 = addf_ (float_ 1.) (float_ 2.) in
-- utest addFloat1 with objWrapGenerate addFloat1 using sameSemantics in

-- let addFloat2 = addf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest addFloat2 with objWrapGenerate addFloat2 using sameSemantics in

-- let testMulFloat = mulf_ (float_ 2.) (float_ 3.) in
-- utest testMulFloat with objWrapGenerate testMulFloat using sameSemantics in

-- let testDivFloat = divf_ (float_ 6.) (float_ 3.) in
-- utest testDivFloat with objWrapGenerate testDivFloat using sameSemantics in

-- let testNegFloat = addf_ (float_ 2.) (negf_ (float_ 2.)) in
-- utest testNegFloat with objWrapGenerate testNegFloat using sameSemantics in

-- let compareFloat1 = eqf_ (float_ 1.) (float_ 2.) in
-- utest compareFloat1 with objWrapGenerate compareFloat1 using sameSemantics in

-- let compareFloat2 = ltf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat2 with objWrapGenerate compareFloat2 using sameSemantics in

-- let compareFloat3 = leqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat3 with objWrapGenerate compareFloat3 using sameSemantics in

-- let compareFloat4 = gtf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat4 with objWrapGenerate compareFloat4 using sameSemantics in

-- let compareFloat5 = geqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat5 with objWrapGenerate compareFloat5 using sameSemantics in

-- let compareFloat6 = neqf_ (addf_ (float_ 1.) (float_ 2.)) (float_ 3.) in
-- utest compareFloat6 with objWrapGenerate compareFloat6 using sameSemantics in


-- -- Chars
-- let charLiteral = char_ 'c' in
-- utest charLiteral with objWrapGenerate charLiteral
-- using sameSemantics in

-- let compareChar1 = eqc_ (char_ 'a') (char_ 'b') in
-- utest compareChar1 with objWrapGenerate compareChar1 using sameSemantics in

-- let compareChar2 = eqc_ (char_ 'a') (char_ 'a') in
-- utest compareChar2 with objWrapGenerate compareChar2 using sameSemantics in

-- let testCharToInt = char2int_ (char_ '0') in
-- utest testCharToInt with objWrapGenerate testCharToInt using sameSemantics in

-- let testIntToChar = int2char_ (int_ 48) in
-- utest testIntToChar with objWrapGenerate testIntToChar using sameSemantics in


-- -- Abstractions
-- let fun =
--   symbolize
--   (appSeq_
--     (ulam_ "@" (ulam_ "%" (addi_ (var_ "@") (var_ "%"))))
--     [int_ 1, int_ 2])
-- in
-- utest fun with objWrapGenerate fun using sameSemantics in

-- let funShadowed =
--   symbolize
--   (appSeq_
--     (ulam_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))))
--     [ulam_ "@" (var_ "@"), int_ 2])
-- in
-- utest funShadowed with objWrapGenerate funShadowed using sameSemantics in

-- -- Lets
--  let testLet =
--   symbolize
--   (bindall_ [ulet_ "^" (int_ 1), addi_ (var_ "^") (int_ 2)])
-- in
-- utest testLet with objWrapGenerate testLet using sameSemantics in

-- let testLetShadowed =
--   symbolize
--   (bindall_ [ulet_ "@" (ulam_ "@" (addi_ (var_ "@") (var_ "@"))),
--              app_ (var_ "@") (int_ 1)])
-- in
-- utest testLetShadowed with objWrapGenerate testLetShadowed
-- using sameSemantics in

-- let testLetRec =
--   symbolize
--   (bind_
--      (ureclets_add "$" (ulam_ "%" (app_ (var_ "@") (int_ 1)))
--      (ureclets_add "@" (ulam_ "" (var_ ""))
--      reclets_empty))
--    (app_ (var_ "$") (var_ "@")))
-- in
-- utest testLetRec with objWrapGenerate testLetRec using sameSemantics in

-- -- Sequences
-- let testEmpty = symbolize (length_ (seq_ [])) in
-- utest testEmpty with objWrapGenerate testEmpty using sameSemantics in

-- let nonEmpty = seq_ [int_ 1, int_ 2, int_ 3] in
-- let len = length_ nonEmpty in
-- let fst = get_ nonEmpty (int_ 0) in
-- let snd = get_ nonEmpty (int_ 1) in
-- let thrd = get_ nonEmpty (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in

-- let testCreate = create_ (int_ 2) (ulam_ "_" (int_ 0)) in
-- let len = length_ testCreate in
-- let fst = get_ testCreate (int_ 0) in
-- let lst = get_ testCreate (int_ 1) in
-- utest int_ 2 with objWrapGenerate len using sameSemantics in
-- utest int_ 0 with objWrapGenerate fst using sameSemantics in
-- utest int_ 0 with objWrapGenerate lst using sameSemantics in

-- let testSet = set_ (seq_ [int_ 1, int_ 2]) (int_ 0) (int_ 3) in
-- let len = length_ testSet in
-- let fst = get_ testSet (int_ 0) in
-- let snd = get_ testSet (int_ 1) in
-- utest int_ 2 with objWrapGenerate len using sameSemantics in
-- utest int_ 3 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in

-- let testCons = cons_  (int_ 1) (seq_ [int_ 2, int_ 3]) in
-- let len = length_ testCons in
-- let fst = get_ testCons (int_ 0) in
-- let snd = get_ testCons (int_ 1) in
-- let thrd = get_ testCons (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in

-- let testSnoc = snoc_ (seq_ [int_ 1, int_ 2]) (int_ 3) in
-- let len = length_ testSnoc in
-- let fst = get_ testSnoc (int_ 0) in
-- let snd = get_ testSnoc (int_ 1) in
-- let thrd = get_ testSnoc (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 1 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 3 with objWrapGenerate thrd using sameSemantics in

-- let testReverse = reverse_ (seq_ [int_ 1, int_ 2, int_ 3]) in
-- let len = length_ testReverse in
-- let fst = get_ testReverse (int_ 0) in
-- let snd = get_ testReverse (int_ 1) in
-- let thrd = get_ testReverse (int_ 2) in
-- utest int_ 3 with objWrapGenerate len using sameSemantics in
-- utest int_ 3 with objWrapGenerate fst using sameSemantics in
-- utest int_ 2 with objWrapGenerate snd using sameSemantics in
-- utest int_ 1 with objWrapGenerate thrd using sameSemantics in

-- let testSeq = seq_ [int_ 1, int_ 2, int_ 3] in
-- let testSubseq1 = subsequence_ testSeq (int_ 0) (int_ 2) in
-- let testSubseq2 = subsequence_ testSeq (int_ 1) (int_ 2) in
-- let testSubseq3 = subsequence_ testSeq (int_ 2) (int_ 100) in
-- let fst = get_ testSubseq3 (int_ 0) in
-- utest int_ 2 with objWrapGenerate (length_ testSubseq1) using sameSemantics in
-- utest int_ 2 with objWrapGenerate (length_ testSubseq2) using sameSemantics in
-- utest int_ 1 with objWrapGenerate (length_ testSubseq3) using sameSemantics in
-- utest int_ 3 with objWrapGenerate fst using sameSemantics in

-- -- -- TODO(Oscar Eriksson, 2020-11-16) Test splitAt when we have implemented tuple
-- -- -- projection.

-- -- -- TODO(Oscar Eriksson, 2020-11-30) Test symbol operations when we have
-- -- -- implemented tuples/records.

-- -- Float-Integer conversions
-- let testFloorfi = floorfi_ (float_ 1.5) in
-- utest testFloorfi with objWrapGenerate testFloorfi using sameSemantics in

-- let testCeilfi = ceilfi_ (float_ 1.5) in
-- utest testCeilfi with objWrapGenerate testCeilfi using sameSemantics in

-- let testRoundfi = roundfi_ (float_ 1.5) in
-- utest testRoundfi with objWrapGenerate testRoundfi using sameSemantics in

-- let testInt2float = int2float_ (int_ 1) in
-- utest testInt2float with objWrapGenerate testInt2float using sameSemantics in

-- let testString2float = string2float_ (str_ "1.5") in
-- utest testString2float with objWrapGenerate testString2float using sameSemantics in

-- -- File operations
-- let testFileExists = fileExists_ (str_ "test_file_ops") in
-- utest testFileExists with objWrapGenerate testFileExists using sameSemantics in

-- -- -- IO operations
-- -- let testPrint = print_ (str_ "tested print") in
-- -- utest testPrint with generate testPrint using sameSemantics in

-- -- Random number generation operations
-- let testSeededRandomNumber =
--  symbolize
--  (bindall_ [ulet_ "_" (randSetSeed_ (int_ 42)),
--             randIntU_ (int_ 0) (int_ 10)])
-- in
-- utest testSeededRandomNumber with objWrapGenerate testSeededRandomNumber
-- using sameSemantics in

-- -- Time operations

-- -- NOTE(larshum, 2020-12-14): Cannot test time operations until unit types
-- -- are supported.

-- -- let testWallTimeMs = wallTimeMs_ unit_ in
-- -- utest testWallTimeMs with objWrapGenerate testWallTimeMs using sameSemantics in

-- -- let testSleepMs = sleepMs_ (int_ 10) in
-- -- utest testSleepMs with objWrapGenerate testSleepMs using sameSemantics in

-- -- TODO(oerikss, 2020-12-14): Sys operations are not tested

-- -- TODO(larshum, 2021-03-06): Add tests for boot parser, map and tensor
-- -- intrinsics

()
