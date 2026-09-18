include "basic-types.mc"
include "mexpr/attribute-grammar.mc"
include "common.mc"
include "seq.mc"
include "string.mc"
include "map.mc"

type ExampleSeq a = {bound : Int, extras : Int, examples : [a]}

let exampleSeqEmpty : all a. Int -> ExampleSeq a = lam bound. {bound = bound, extras = 0, examples = []}

let exampleAdd : all a. a -> ExampleSeq a -> ExampleSeq a = lam a. lam as.
  if lti (length as.examples) as.bound
  then {as with examples = snoc as.examples a}
  else {as with extras = addi 1 as.extras}

let exampleCount : all a. ExampleSeq a -> Int = lam ex.
  addi (length ex.examples) ex.extras

let examplesToShortStr : all a. (a -> String) -> ExampleSeq a -> String = lam f. lam as.
  let content = switch as.examples
    case [] then None ()
    case [ex] then Some (f ex)
    case [ex1, ex2] then Some (join [f ex1, " and ", f ex2])
    case exs ++ [ex] then Some (join [strJoin ", " (map f exs), ", and ", f ex])
    end in
  switch (as.extras, content)
  case (_, None _) then ""
  case (0, Some content) then join [" (", content, ")"]
  case (!0, Some content) then join [" (e.g., ", content, ")"]
  end

let examplesToLongStr : all a. String -> (a -> String) -> ExampleSeq a -> String = lam label. lam f. lam as.
  if null as.examples then "" else
  let f = lam ex. switch f ex
    case res & "\n    " ++ _ then res
    case res & "    " ++ _ then cons '\n' res
    case res & "   " ++ _ then concat "\n " res
    case res & "  " ++ _ then concat "\n  " res
    case res & " " ++ _ then concat "\n   " res
    case res & "" ++ _ then concat "\n    " res
    end in
  join (cons (cons ' ' label) (map f as.examples))

lang Invariant = AttributeGrammar
  sem printInvariantSummary : Attr Loc -> ()
  sem printInvariantSummary =
  | _ -> ()

  sem invariantLoc2Str : String -> Loc -> String
  sem invariantLoc2Str indent = | loc ->
    let lines = strSplit "\n" (loc2str loc) in
    let lines = match lines with [l1, l2, l3, _, _] ++ _ ++ [r1, r2, r3]
      then [l1, l2, l3, "...elided...", r1, r2, r3]
      else lines in
    join (map (concat (cons '\n' indent)) lines)

  sem checkInvariants : [Attr Loc] -> Expr -> ()
  sem checkInvariants attrs = | ast ->
    let start = wallTimeMs () in
    let res = processAst attrs ast in
    let timeMs = subf (wallTimeMs ()) start in
    printLn (join ["  Invariants: associated attributes in ", float2string timeMs, "ms."]);
    mapFoldWithKey (lam. lam. lam attr. printInvariantSummary attr) () res
end
