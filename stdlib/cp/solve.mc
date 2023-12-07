-- Solves a COP using MiniZinc as backend and returns the solution.

include "ast.mc"
include "pprint.mc"
include "sys.mc"
include "json.mc"

lang COPSolve = COP + COPPrettyPrint
  syn COPVarValue =
  | COPInt {val: Int}
  | COPBool {val: Bool}
  | COPArray {vals: [COPVarValue]}

  type COPSolution = {
    solution: Map Name COPVarValue,
    objective: Option COPVarValue
  }

  syn COPSolverStatus =
  | COPError {}
  | COPUnknown {}
  | COPUnbounded {}
  | COPUnsatisfiable {}
  | COPSatisfied {}
  | COPAllSolutions {}
  | COPOptimalSolution {}

  type COPSolverResult = (COPSolverStatus, [COPSolution])
  type COPSolverResultRaw = (COPSolverStatus, [Map String COPVarValue])

  type COPSolverOptions = {
    solver: String,
    timeoutMs: Int,
    allSolutions: Bool,
    solverFlags: [String]
  }

  sem solverOptionsDefault =
  | {} -> {
    solver = "gecode",
    timeoutMs = 0,
    allSolutions = false,
    solverFlags = []}

  sem solve: COPModel -> COPSolverResult
  sem solve =
  | model -> solve (solverOptionsDefault {}) model

  sem solveOptions: COPSolverOptions -> COPModel -> COPSolverResult
  sem solveOptions options =
  | model ->
    let isOpt = isOptimizationModel model in
    match pprintCOPModel model with (env, model) in
    _solveString isOpt options env.nameMap model

  -- Takes a string instead of a model, to simplify testing.
  sem _solveString: Bool -> COPSolverOptions -> Map Name String -> String -> COPSolverResult
  sem _solveString isOpt options env =
  | model ->
    -- Output the model to a temporary file
    let tempDir = sysTempDirMake () in
    let modelFile = sysJoinPath tempDir "model.mzn" in
    let outputFile = sysJoinPath tempDir "result.json" in
    writeFile modelFile model;
    -- Solve the model
    match _runSolver options modelFile outputFile with
    (_, {stdout = stdout}) in
    -- Parse the result
    match _parseAll isOpt stdout outputFile
    with (status, solutions) in
    let getSolution = lam s. _validateObjective isOpt (_solutionFromRaw env s) in
    let res = (status, map getSolution solutions) in
    -- Remove temporary directory and return
    sysTempDirDelete tempDir ();
    res

  sem _runSolver: COPSolverOptions -> String -> String -> (Float, ExecResult)
  sem _runSolver options inputFile =
  | outputFile ->
    let flags = concat
      ["--output-mode", "json",
       "-o", outputFile,
       "--output-objective",
       "--solver", options.solver,
       if options.allSolutions then "--all-solutions" else "",
       "--time-limit", int2string options.timeoutMs]
      options.solverFlags
    in
    sysRunCommandWithTiming (join [["minizinc"], flags, [inputFile]]) "" ""

  sem _json2COPVarValue: JsonValue -> Option COPVarValue
  sem _json2COPVarValue =
  | v ->
    switch v
    case JsonInt i then Some (COPInt {val = i})
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

  -- Parse all solutions from the solver output.
  sem _parseAll: Bool -> String -> String -> COPSolverResultRaw
  sem _parseAll isOpt stdout =
  | jsonFile ->
    if fileExists jsonFile then
      let str = readFile jsonFile in
      let split = strSplit "----------" str in
      switch length split
      case 1 then
        let status = _parseSolverStatus isOpt (strTrim (head split)) in
        (status, [])
      case n then
        match splitAt split (subi n 1) with (solutionsStr, [statusStr]) in
        let status = _parseSolverStatus isOpt (strTrim statusStr) in
        let solutions = map _parseOne solutionsStr in
        (status, solutions)
      end
    else
      -- If no output file, check for solver status in stdout
      let status = _parseSolverStatus isOpt (strTrim stdout) in
      (status, [])

  -- Parse one solution.
  sem _parseOne: String -> Map String COPVarValue
  sem _parseOne =
  | str ->
    switch jsonParse str
    case Left (JsonObject m) then
      mapFoldWithKey (lam acc. lam k. lam v.
          match _json2COPVarValue v with Some v2 then
            mapInsert k v2 acc
          else error (concat "Unknown json value: " (json2string v))
        ) (mapEmpty cmpString) m
    case _ then
      error (concat "Cannot parse solution: " str)
    end

  sem _parseSolverStatus: Bool -> String -> COPSolverStatus
  sem _parseSolverStatus isOpt =
  | "=====ERROR=====" -> COPError {}
  | "=====UNKNOWN=====" -> COPUnknown {}
  | "=====UNSATISFIABLE=====" -> COPUnsatisfiable {}
  | "=====UNSATorUNBOUNDED=====" -> COPUnbounded {}
  | "=====UNBOUNDED=====" -> COPUnbounded {}
  | "==========" -> if isOpt then COPOptimalSolution {} else COPAllSolutions {}
  | "" -> COPSatisfied {}
  | str ->
    error (concat "Unknown solver status string: " str)

  sem _solutionFromRaw: Map Name String -> Map String COPVarValue -> COPSolution
  sem _solutionFromRaw env =
  | resMap ->
    let m: Map Name COPVarValue =
      mapFoldWithKey (lam acc. lam n. lam s.
        match mapLookup s resMap with Some v then mapInsert n v acc
        else error (concat "Variable not found: " s)
      ) (mapEmpty nameCmp) env in
    {solution = m, objective = mapLookup "_objective" resMap}

  sem _validateObjective: Bool -> COPSolution -> COPSolution
  sem _validateObjective isOpt =
  | sols ->
    switch (isOpt, sols.objective)
    case (true, Some _) then sols
    case (false, None _) then sols
    case (true, _) then
      error "Impossible: no objective value found for optimization model"
    case (false, _) then
      error "Impossible: objective value found for satisfaction model"
    end

  sem eqCOPSolverResult r1 =
  | r2 ->
    if eqCOPSolverStatus r1.0 r2.0 then
      eqSeq eqCOPSolution r1.1 r2.1
    else false

  sem eqCOPSolverStatus s1 =
  | s2 -> _eqCOPSolverStatusH (s1, s2)

  sem _eqCOPSolverStatusH =
  | (COPError {}, COPError {}) -> true
  | (COPUnknown {}, COPUnknown {}) -> true
  | (COPUnbounded {}, COPUnbounded {}) -> true
  | (COPUnsatisfiable {}, COPUnsatisfiable {}) -> true
  | (COPSatisfied {}, COPSatisfied {}) -> true
  | (COPAllSolutions {}, COPAllSolutions {}) -> true
  | (COPOptimalSolution {}, COPOptimalSolution {}) -> true
  | _ -> false

  sem eqCOPSolution s1 =
  | s2 ->
    if mapEq eqCOPVarValue s1.solution s2.solution then
      optionEq eqCOPVarValue s1.objective s2.objective
    else false

  sem eqCOPVarValue v1 =
  | v2 -> _eqCOPVarValueH (v1, v2)

  sem _eqCOPVarValueH =
  | (COPInt v1, COPInt v2) -> eqi v1.val v2.val
  | (COPBool v1, COPBool v2) -> eqBool v1.val v2.val
  | (COPArray v1, COPArray v2) ->
    forAll (lam x. x) (zipWith eqCOPVarValue v1.vals v2.vals)

end

mexpr

use COPSolve in

let cpInt_ = lam i. COPExprInt {value = i} in

utest _json2COPVarValue (JsonInt 2) with Some (COPInt {val = 2}) in
utest _json2COPVarValue (JsonArray [JsonBool true])
with Some (COPArray {vals = [COPBool {val = true}]}) in

type TestRhs = {status: COPSolverStatus, solutions: [[(String, String)]]} in

let rhs2Result: Map Name String -> TestRhs -> COPSolverResult = lam m. lam rhs.
  -- Create inverse of name map
  let mInv: Map String Name = mapFoldWithKey (lam acc. lam k. lam v.
      mapInsert v k acc
    ) (mapEmpty cmpString) m
  in

  -- Create solution map
  let solutions: [[(String, COPVarValue)]] = map (lam s: [(String, String)].
    map (lam kv: (String, String).
      match kv with (k, v) in
      let v = optionGetOrElse (lam. error "Not a COPVarValue") (
          _json2COPVarValue (jsonParseExn v)) in
      (k, v)) s
    ) rhs.solutions
  in
  let sols: [Map Name COPVarValue] = map (lam s: [(String, COPVarValue)].
      foldl (lam acc: Map Name COPVarValue. lam kv: (String, COPVarValue).
        match kv with (k, v) in
        mapInsert (mapFindExn k mInv) v acc
      ) (mapEmpty nameCmp) s
    ) solutions
  in

  -- Read objective values
  let strSols: [Map String COPVarValue] = map (mapFromSeq cmpString) solutions in
  let objectives: [Option COPVarValue] = map (mapLookup "_objective") strSols in

  (rhs.status, map (lam t. {solution=t.0, objective=t.1}) (zip sols objectives))
in

let createEnv: [String] -> Map Name String = lam vars.
  foldl (lam acc. lam str.
    mapInsert (nameSym str) str acc) (mapEmpty nameCmp) vars
in

let eqTest =
  lam options: COPSolverOptions. lam isOpt: Bool. lam vars: [String].
  lam lhs: String. lam rhs: TestRhs.
    if sysCommandExists "minizinc" then
      let env = (createEnv vars) in
      let lhs = _solveString isOpt options env lhs in
      eqCOPSolverResult lhs (rhs2Result env rhs)
    else true
in

let eqTestOpt = eqTest (solverOptionsDefault {}) true in
let eqTestSat = eqTest (solverOptionsDefault {}) false in

let x = nameSym "x" in

-- Optimization problem
utest
"
array [1..3] of var 0..1: x;
include \"table.mzn\";
constraint table(x,[|0,0,1|1,0,1|0,0,0|]);
solve minimize sum(x);
"
with {
  status = COPOptimalSolution {},
  solutions = [[("x", "[0, 0, 0]"), ("_objective", "0")]]
} using eqTestOpt ["x", "_objective"]
in

-- Satisfaction problem
utest
"
var bool: x;
solve satisfy;
"
with {
  status = COPSatisfied {},
  solutions = [[("x", "false")]]
} using eqTestSat ["x"]
in

-- Unknown (short timeout)
utest
"
var bool: x;
solve satisfy;
"
with {
  status = COPUnknown {}, solutions = []
} using eqTest {(solverOptionsDefault {}) with timeoutMs = 1} false ["x"]
in

-- All solutions
utest
"
var bool: x;
solve satisfy;
"
with {
  status = COPAllSolutions {}, solutions = [[("x", "false")], [("x", "true")]]
} using eqTest {(solverOptionsDefault {}) with allSolutions = true} false ["x"]
in

-- Unbounded
utest
"
var int: x;
solve maximize x;
"
with {
  status = COPUnbounded {}, solutions = []
} using eqTest {(solverOptionsDefault {}) with solver = "coinbc"} false ["x"]
in

-- Unsatisfiable
utest
"
var 0..1: x;
var 1..2: y;
constraint x > y;
solve satisfy;
"
with {
  status = COPUnsatisfiable {}, solutions = []
} using eqTestSat ["x", "y"]
in


()
