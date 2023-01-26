include "bool.mc"
include "common.mc"
include "seq.mc"
include "string.mc"

let numFailed = ref 0
let numPassed = ref 0

let utestTestPassed : () -> () = lam.
  modref numPassed (addi (deref numPassed) 1);
  print "."

let utestTestFailed : String -> String -> String -> String -> () =
  lam info. lam lstr. lam rstr. lam usingstr.
  modref numFailed (addi (deref numFailed) 1);
  printLn (join [
    "\n ** Unit test FAILED: ", info, " **\n    LHS: ", lstr,
    "\n    RHS: ", rstr, usingstr])

let utestRunner
  : all a. all b. String -> String -> (a -> String) -> (b -> String)
               -> (a -> b -> Bool) -> a -> b -> () =
  lam info. lam usingstr. lam lpp. lam rpp. lam eqfn. lam l. lam r.
  if eqfn l r then utestTestPassed ()
  else utestTestFailed info (lpp l) (rpp r) usingstr

let defaultPprint : all a. a -> String = lam. "?"
let ppBool : Bool -> String = bool2string
let ppInt : Int -> String = int2string
let ppFloat : Float -> String = float2string
let ppChar : Char -> String = showChar
let ppSeq : all a. (a -> String) -> [a] -> String = lam pp. lam s.
  join ["[", strJoin "," (map pp s), "]"]

let eqInt : Int -> Int -> Bool = eqi
let eqFloat : Float -> Float -> Bool = eqf

let utestExitOnFailure : all a. a -> a = lam t.
  if eqi (deref numFailed) 0 then
    t
  else
    printLn (join [
      "ERROR! ", ppInt (deref numPassed), " successful tests and ",
      ppInt (deref numFailed), " failed tests."
    ]);
    exit 1

mexpr

-- NOTE(larshum, 2022-12-30): Declare a tuple containing the functions that we
-- want to be included. This allows us to remove other functions that are not
-- of interest through deadcode elimination.
( utestRunner, utestExitOnFailure, defaultPprint, ppBool, ppInt, ppFloat,
ppChar, ppSeq , eqBool, eqInt , eqFloat, eqChar , eqSeq, join )
