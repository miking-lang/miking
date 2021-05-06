include "mexpr/decision-points.mc"
include "ext/local-search.mc"
include "common.mc"
include "ocaml/sys.mc"
include "map.mc"

type Stdin = String
type CommandLineArgs = [String]
type InputData = (CommandLineArgs, Stdin)
type Runner = InputData -> ExecResult

let _bool2string = lam b.
  if b then "true" else "false"

let _dataEmpty = [([""], "")]

-- Add assignments of decision points to argument vector
let _addToArgs = lam vals : LookupTable. lam args : CommandLineArgs.
  use MExprAst in
  -- TODO: types
  let stringVals = mapMapWithKey (lam. lam v.
    match v with TmConst {val = b} then _bool2string b
    else dprintLn v; error "The type of this value is not supported yet"
  ) vals in
  concat (mapValues stringVals) args

lang TuneHoles = HoleAst + FlattenHoles
  sem tune (run : Runner) (data : [InputData]) =
  -- Intentionally left blank

  sem time (vals : LookupTable) (runner : Runner) =
  | (args, stdin) ->
    let allArgs = _addToArgs vals args in
    let t1 = wallTimeMs () in
    let res = runner (allArgs, stdin) in
    let t2 = wallTimeMs () in
    print "Result: "; dprintLn res;
    match res.returncode with 0 then
      subf t2 t1
    else
      let msg = strJoin " "
      [ "Program returned non-zero exit code during tuning\n"
      , "command line arguments:", strJoin " " args, "\n"
      , "all command line arguments:", strJoin " " allArgs, "\n"
      , "stdin:", stdin, "\n"
      , "stdout:", res.stdout, "\n"
      , "stderr:", res.stderr, "\n"
      ] in error msg
end

--------------------------
-- Local search methods --
--------------------------

---- Settings for local search ----
---- TODO Some of these settings should be input to the framework
let _nbrIterations = 1
let _localSearchSettings = {
  printIter = lam st : SearchState v c.
    let st : SearchState v c = st in
    let inc : Solution v c = st.inc in
    print (join  ["Iter: ", int2string st.iter, "\n",
                  "Best cost: ", float2string inc.1, "\n"]),
  terminate = (lam st : SearchState v c.
    geqi st.iter _nbrIterations)
}

lang LocalSearch = TuneHoles
  sem tune (runner : Runner) (data : [InputData]) =
  | table ->
    let data = match data with [] then _dataEmpty else data in
    -- Set up initial search state
    let initSol = table in
    -- cost function = sum of execution times for all inputs
    let costF = lam lookup : LookupTable.
      foldr1 addf (map (time lookup runner) data) in
    -- comparison function: distinguish runtimes on the level of microseconds
    let cmp = lam r1. lam r2.
      roundfi (mulf 1000.0 (subf r1 r2)) in
    let startState = initSearchState (initSol, costF initSol) cmp in

    -- Set up meta heuristic
    let meta = metaHeur startState in

    -- Do the search!
    _localSearchSettings.printIter startState;
    minimize
      _localSearchSettings.terminate
      _localSearchSettings.printIter
      startState
      meta

  sem metaHeur (startSol : Solution v Float) =
  -- Intentionally left blank

end

lang MExprTune = LocalSearch
