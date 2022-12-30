include "bool.mc"
include "common.mc"
include "seq.mc"
include "string.mc"

let numFailed = ref 0

let utestTestPassed : () -> () = lam. print "."

let utestTestFailed : String -> String -> String -> String -> () =
  lam info. lam lstr. lam rstr. lam usingstr.
  modref numFailed (addi (deref numFailed) 1);
  printLn (join [
    "\n ** Unit test FAILED: ", info, "**", "\n    LHS: ", lstr,
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
let ppTensor : all a. (a -> String) -> Tensor[a] -> String = lam pp. lam t.
  tensor2string pp t

let eqInt : Int -> Int -> Bool = eqi
let eqFloat : Float -> Float -> Bool = eqf
let eqTensor : all a. (a -> a -> Bool) -> Tensor[a] -> Tensor[a] -> Bool = tensorEq
