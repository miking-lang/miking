include "bool.mc"
include "string.mc"
include "mexpr/info.mc"

recursive let f = lam acc. lam n.
  if eqi n 0 then acc
  else f (cons n acc) (subi n 1)
end

let utestCurrentFile = ref ""
let utestPassed = ref 0
let utestLocalOK = ref true
let utestFailed = ref 0

let utestTestPassed = lam.
  print ".";
  modref utestPassed (addi (deref utestPassed) 1)

let utestTestFailed =
  lam line   : Int.
  lam lhsStr : String.
  lam rhsStr : String.
  printLn "";
  printLn (join [" ** Unit test FAILED on line ", int2string line, " **"]);
  printLn (join ["    LHS: ", lhsStr]);
  printLn (join ["    RHS: ", rhsStr]);
  modref utestFailed (addi (deref utestFailed) 1)

let utestPrintSummary = lam.
  let failed = deref utestFailed in
  let passed = deref utestPassed in
  if eqi failed 0 then
    printLn " OK"
  else
    printLn "";
    printLn (join ["ERROR! ", int2string passed,
                 " successful tests and ", int2string failed,
                 " failed tests."])

let utestPrintFileSummary = lam.
  if deref utestLocalOK then printLn " OK"
  else printLn ""

let utestRunner =
  lam info   : Info.
  lam printf : a -> String.
  lam eqfunc : a -> a -> Bool.
  lam lhs    : a.
  lam rhs    : a.
  lam.
  -- We assume that Utests always have an info field
  match info with Info t then
    -- Check whether we are using a new file
    let currFile = deref utestCurrentFile in
    (if null currFile then
       print (join [t.filename, ": "]);
       modref utestCurrentFile t.filename
     else if eqString currFile t.filename then ()
     else
       utestPrintFileSummary ();
       print (join [t.filename, ": "]);
       modref utestCurrentFile t.filename);

    -- Comparison
    if eqfunc lhs rhs then
      utestTestPassed ()
    else
      utestTestFailed t.row1 (printf lhs) (printf rhs)
  else never

let printInt = lam n.
  use MExprAst in
  match n with TmConst {val = CInt {val = n}} then
    int2string n
  else never

let utestInt = lam info. lam l. lam r.
  utestRunner info printInt eqi_ l r

let utestBool = lam info. lam l. lam r.
  let printBool = lam b. if b then "true" else "false" in
  utestRunner info printBool eqBool l r

let utestSeq = lam info. lam seqPrint. lam seqEq. lam l. lam r.
  utestRunner info seqPrint seqEq l r

mexpr

let utestInfo = lam line.
  Info {filename = "utestrunner.mc",
        row1 = line, col1 = 0, row2 = line, col1 = 0}
in

utest 1 with 1 in
utest 1 with 2 in
utest 2 with 1 in
utest 2 with 2 in

utest true with true in
utest true with false in
utest false with true in
utest false with false in

utest [1,2,3] with f [] 3 in
utest [1,2,3] with f [] 4 in

-- Emulated versions of utests
utestInt (utestInfo 82) 1 1;
utestInt (utestInfo 83) 1 2;
utestInt (utestInfo 84) 2 1;
utestInt (utestInfo 85) 2 2;

utestBool (utestInfo 87) true true;
utestBool (utestInfo 88) true false;
utestBool (utestInfo 89) false true;
utestBool (utestInfo 90) false false;

utestSeq (utestInfo 92) (printSeq int2string) (eqSeq eqi) [1,2,3] (f [] 3);
utestSeq (utestInfo 93) (printSeq int2string) (eqSeq eqi) [1,2,3] (f [] 4);

utestPrintSummary ();

()
