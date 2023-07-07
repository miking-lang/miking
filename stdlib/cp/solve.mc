-- Solves a COP using MiniZinc as backend and returns the solution.

include "ast.mc"
include "pprint.mc"
include "sys.mc"
include "json.mc"

lang COPSolve = COP + COPPrettyPrint
  syn COPVarValue =
  | COPInt {val: Int}
  | COPBool {val: Bool}
  | COPFloat {val: Float}
  | COPArray {vals: [COPVarValue]}

  -- TODO(Linnea, 2023-03-16): Include other possible results (unsatisfiable,
  -- unknown, unbounded, optimal, all solutions).
  syn COPSolverResult =
  | COPSolution {
      solution: Map Name COPVarValue,
      objective: Option COPVarValue
    }
  | COPUnsat ()
  | COPError {msg: String}

  sem solve: COPModel -> COPSolverResult
  sem solve =
  | model ->
    match pprintCOPModel model with (env, model) in
    -- Output the model to a temporary file
    let tempDir = sysTempDirMake () in
    let modelFile = sysJoinPath tempDir "model.mzn" in
    let outputFile = sysJoinPath tempDir "result.json" in
    writeFile modelFile model;
    -- Solve the model
    match sysRunCommandWithTiming [
      "minizinc",
        "--output-mode", "json",
        "-o", outputFile,
        "--output-objective",
        "--solver", "gecode",
        "--unsat-msg", "!UNSAT!",
        modelFile
      ] "" ""
    with (elapsed, {stdout = stdout, stderr = stderr, returncode = returncode}) in
    let errorStr = lam.
      strJoin "\n"
        [ "> Output file",
          if fileExists outputFile then readFile outputFile else "-- No output file --",
          "\n> Model", readFile modelFile,
          "\n> Stdout", stdout,
          "\n> Stderr", stderr,
          "\n> Returncode", int2string returncode ]
    in
    -- Read the result back
    let res =
      let unsat =
        if isPrefix eqc "!UNSAT!" stdout then true else
        if fileExists outputFile then
          -- OPT(vipa, 2023-08-16): This is inconvenient, minizinc
          -- seems to vary where it puts the unsat message, sometimes
          -- on stdout, sometimes in the output file. This means we
          -- read the file twice right now, we should refactor to
          -- avoid that. Maybe use --json-stream instead of
          -- --output-mode, and skipping --output-to-file?
          isPrefix eqc "!UNSAT!" (readFile outputFile)
        else false in
      if unsat then COPUnsat () else
      match _parseResult outputFile with Some resMap then
        -- Build a map with relevant variables
        let m: Option (Map Name COPVarValue) =
          mapFoldWithKey (lam acc. lam n. lam s.
            match acc with Some m then
              match mapLookup (cons 'z' s) resMap with Some v then
                Some (mapInsert n v m)
              else None ()
            else None ()
          ) (Some (mapEmpty nameCmp)) env.nameMap in
        match m with Some m then
          COPSolution {
            solution = m,
            -- Objective value stored as key "_objective"
            objective = mapLookup "_objective" resMap
          }
        else COPError { msg = strJoin "\n"
          ["Some variables were not found", errorStr ()]}
      else
        COPError { msg = strJoin "\n" ["Could not parse solution:", errorStr ()]}
    in
    -- Remove temporary directory and return
    sysTempDirDelete tempDir ();
    res

  sem _json2COPVarValue: JsonValue -> Option COPVarValue
  sem _json2COPVarValue =
  | v ->
    switch v
    case JsonInt i then Some (COPInt {val = i})
    case JsonFloat i then Some (COPFloat {val = i})
    case JsonBool b then Some (COPBool {val = b})
    case JsonArray a then
      let vals =
        foldl (lam acc. lam x.
          match acc with Some vals then
            match _json2COPVarValue x with Some val then Some (snoc vals val)
            else None ()
          else None ()
        ) (Some []) a
      in
      match vals with Some vals then
        Some (COPArray {vals = vals})
      else None ()
    end

  sem _parseResult: String -> Option (Map String COPVarValue)
  sem _parseResult =
  | jsonFile ->
    -- Cut out the last outputed solution
    let lastSolution: String -> Option String = lam str.
      let split = strSplit "----------" str in
      switch length split
      case 1 then None ()
      case n then
        Some (strTrim (get split (subi n 2)))
      end
    in
    utest lastSolution "
    one
    ----------
    " with Some "one" in
    utest lastSolution "
    one
    ----------
    two
    ----------
    " with Some "two" in
    utest lastSolution "
    optimal
    ----------
    ==========
    " with Some "optimal" in
    utest lastSolution "" with None () in

    -- Parse a solution in json format
    let parseSolution: String -> Option (Map String COPVarValue) = lam str.
      switch jsonParse str
      case Left (JsonObject m) then
        mapFoldWithKey (lam acc. lam k. lam v.
            match acc with Some m then
              match _json2COPVarValue v with Some v2 then
                Some (mapInsert k v2 m)
              else None ()
            else None ()
          ) (Some (mapEmpty cmpString)) m
      case _ then
        -- Incorrectly formatted solution
        None ()
      end
    in

    if fileExists jsonFile then
      match lastSolution (readFile jsonFile) with Some sol then
        parseSolution sol
      else None ()
    else None ()

end

mexpr

use COPSolve in

let cpInt_ = lam i. COPExprInt {value = i} in

utest _json2COPVarValue (JsonInt 2) with Some (COPInt {val = 2}) in
utest _json2COPVarValue (JsonArray [JsonBool true])
with Some (COPArray {vals = [COPBool {val = true}]}) in

recursive let eqCOPVarValue = lam v1. lam v2.
  switch (v1, v2)
  case (COPInt v1, COPInt v2) then eqi v1.val v2.val
  case (COPBool v1, COPBool v2) then eqBool v1.val v2.val
  case (COPArray v1, COPArray v2) then
    forAll (lam x. x) (zipWith eqCOPVarValue v1.vals v2.vals)
  end
in

let eqCOPSolverResult = lam s1. lam s2.
  switch (s1, s2)
  case (COPSolution s1, COPSolution s2) then
    if mapEq eqCOPVarValue s1.solution s2.solution then
      optionEq eqCOPVarValue s1.objective s2.objective
    else false
  case (COPError _, COPError _) then true
  case _ then false
  end
in

let eqTest = lam lhs: COPModel. lam rhs: COPSolverResult.
  if sysCommandExists "minizinc" then
    let lhs = solve lhs in
    eqCOPSolverResult lhs rhs
  else true
in

let x = nameSym "x" in

utest
  let zero = cpInt_ 0 in
  let one = cpInt_ 1 in
  [COPVarArrayDecl {
     id = x,
     domain = COPDomainIntRange {min = cpInt_ 0, max = cpInt_ 1},
     length = cpInt_ 3},
   COPConstraintDecl {constraint = COPConstraintTable {
     vars = COPExprVar {id = x},
     tuples = COPExprArray2d {array = [[zero,zero,one],[one,zero,one],[zero,zero,zero]]}}},
   COPObjectiveDecl {
     objective = COPObjectiveMinimize {
       expr = COPExprSum {expr = COPExprVar {id = x}}
     }
   }
  ]
with
  COPSolution {
    solution = mapFromSeq nameCmp [
      (x, COPArray {vals=[COPInt{val=0},COPInt{val=0},COPInt{val=0}]})],
    objective = Some (COPInt {val = 0})}
using eqTest in

utest
  [COPObjectiveDecl {
    objective = COPObjectiveMinimize {expr = COPExprVar {id = x}}}]
with COPError {msg = ""}
using eqTest in

()
