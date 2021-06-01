include "ext/local-search.mc"
include "ocaml/sys.mc"
include "string.mc"
include "map.mc"
include "decision-points.mc"
include "tune-options.mc"
include "common.mc"

-- Performs tuning of a program with decision points.

-- Default input if program takes no input data
let _inputEmpty = [""]

----------------------------------
-- Reading/writing tuned values --
----------------------------------

let tuneFileExtension = ".tune"

let tuneFileName = lam file.
  let withoutExtension =
    match strLastIndex '.' file with Some idx then
      subsequence file 0 idx
    else file
  in concat withoutExtension tuneFileExtension

let _tuneTable2str = lam table : LookupTable.
  use MExprPrettyPrint in
  strJoin " " (map expr2str table)

let tuneDumpTable = lam file : String. lam table : LookupTable.
  let destinationFile = tuneFileName file in
  -- NOTE(Linnea, 2021-05-27): add whitespace as workaround for bug #145
  writeFile destinationFile (concat (_tuneTable2str table) " ")

let tuneReadTable = lam file : String.
  use BootParser in
  let str = readFile file in
  map (parseMExprString []) (strSplit " " (strTrim str))

------------------------------
-- Base fragment for tuning --
------------------------------
type Runner = String -> ExecResult

lang TuneBase = Holes
  sem tune (options : TuneOptions) (run : Runner) (holes : Expr)
           (file : String) =
  -- Intentionally left blank

  sem time (table : LookupTable) (runner : Runner) (file : String) =
  | args ->
    tuneDumpTable file table;
    let t1 = wallTimeMs () in
    let res : ExecResult = runner args in
    let t2 = wallTimeMs () in
    --print "Result: "; dprintLn res;
    match res.returncode with 0 then
      subf t2 t1
    else
      let msg = strJoin " "
      [ "Program returned non-zero exit code during tuning\n"
      , "decision point values:", _tuneTable2str table, "\n"
      , "command line arguments:", strJoin " " args, "\n"
      , "stdout:", res.stdout, "\n"
      , "stderr:", res.stderr, "\n"
      ] in error msg
end

--------------------------
-- Local search methods --
--------------------------

lang TuneLocalSearch = TuneBase + LocalSearchBase
  syn Assignment =
  | Table {table : LookupTable,
           holes : [Expr],
           options : TuneOptions}

  syn Cost =
  | Runtime {time : Float}

  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
             Table {holes = holes, table = table, options = options}}}
    then
      let table = map (lam h.
        match h with TmHole {hole = hole} then sample hole
        else dprintLn h; error "Expected a decision point") holes
      in [Table {table = table, holes = holes, options = options}]
    else never

  sem compare =
  | (Runtime {time = t1}, Runtime {time = t2}) ->
    roundfi (mulf 1000.0 (subf t1 t2))

  sem initMeta =

  sem debugSearch =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {iter = iter
         , inc = {assignment = Table {table = inc},
                  cost = Runtime {time = incTime}}
         , cur = {assignment = Table {table = cur},
                  cost = Runtime {time = curTime}}}
    then
      use MExprPrettyPrint in
      let incValues = map expr2str inc in
      let curValues = map expr2str cur in
      printLn (join ["Iter: ", int2string iter, "\n",
                     "Current table: ", strJoin ", " curValues, "\n",
                     "Current time: ", float2string curTime, "\n",
                     "Best time: ", float2string incTime, "\n",
                     "Best table: ", strJoin ", " incValues])

    else never

  sem tune (options : TuneOptions) (runner : Runner) (holes : [Expr])
           (file : String) =
  | table ->
    let input =
      match options.input with [] then _inputEmpty else options.input in
    -- cost function = sum of execution times over all inputs
    let costF = lam lookup : Assignment.
      match lookup with Table {table = table} then
        Runtime {time = foldr1 addf (map (time table runner file) input)}
      else never in

    -- Set up initial search state
    let startState =
      initSearchState costF (Table {table = table
                                   , holes = holes
                                   , options = options}) in

    -- When to stop the search
    let stop = lam state : SearchState.
      or state.stuck (geqi state.iter options.iters) in

    recursive let search =
      lam stop.
      lam searchState.
      lam metaState.
        (if options.debug then
          printLn "-----------------------";
          debugSearch searchState;
          debugMeta metaState;
          printLn "-----------------------"
         else ());
        if stop searchState then
          (searchState, metaState)
        else
          match minimize searchState metaState with (searchState, metaState)
          then
            search stop searchState metaState
          else never
    in

    -- Do the search!
    match search stop startState (initMeta startState)
    with (searchState, _) then
      let searchState : SearchState = searchState in
      match searchState with {inc = {assignment = Table {table = table}}}
      then table
      else never
    else never
end

lang TuneRandomWalk = TuneLocalSearch
                    + LocalSearchSelectRandomUniform
  syn MetaState =
  | Empty {}

  sem step (searchState : SearchState) =
  | Empty {} ->
    (select (neighbourhood searchState) searchState, Empty {})

  sem initMeta =
  | _ -> Empty {}
end

lang TuneSimulatedAnnealing = TuneLocalSearch
                            + LocalSearchSimulatedAnnealing
                            + LocalSearchSelectRandomUniform
  sem decay (searchState : SearchState) =
  | SimulatedAnnealing t ->
    match searchState with {cur = {assignment = Table {options = options}}} then
      let options : TuneOptions = options in
      SimulatedAnnealing {t with temp = mulf options.saDecayFactor t.temp}
    else never

  sem initMeta =
  | startState ->
    let startState : SearchState = startState in
    match startState with {cur = {assignment = Table {options = options}}} then
      let options : TuneOptions = options in
      SimulatedAnnealing {temp = options.saInitTemp}
    else never

  sem debugMeta =
  | SimulatedAnnealing {temp = temp} ->
    printLn (join ["Temperature: ", float2string temp])
end

lang TuneTabuSearch = TuneLocalSearch
                    + LocalSearchTabuSearch
                    + LocalSearchSelectRandomUniform
  syn TabuSet =
  | Tabu {tabu : [LookupTable]}

  sem isTabu =
  | (Table {table = table}, Tabu {tabu = tabu}) ->
    use MExprEq in
    match find (lam t. eqSeq eqExpr table t) tabu
    with Some _ then true else false

  sem tabuUpdate =
  | (Table {table = table, options = options}, Tabu ({tabu = tabu} & t)) ->
    let options : TuneOptions = options in
    let tabu = cons table
      (if eqi (length tabu) options.tabuSize then init tabu else tabu) in
    Tabu {t with tabu = tabu}

  sem initMeta =
  | startState ->
    let startState : SearchState = startState in
    match startState with {cur = {assignment = Table {table = table}}} then
      TabuSearch {tabu = Tabu {tabu = [table]}}
    else never

  sem debugMeta =
  | TabuSearch {tabu = Tabu {tabu = tabu}} ->
    printLn (join ["Tabu size: ", int2string (length tabu)])
end

lang MExprTune = MExpr + TuneBase

-- Entry point for tuning
let tuneEntry =
  lam args : [String].
  lam run : Runner.
  lam holes : [Expr].
  lam tuneFile : String.
  lam table : LookupTable.
    let options = parseTuneOptions tuneOptionsDefault args in

    -- Do warmup runs
    use TuneBase in
    iter (lam. map (time table run tuneFile) options.input)
      (range 0 options.warmups 1);

    -- Choose search method
    match options.method with RandomWalk {} then
      use TuneRandomWalk in tune options run holes tuneFile table
    else match options.method with SimulatedAnnealing {} then
      use TuneSimulatedAnnealing in tune options run holes tuneFile table
    else match options.method with TabuSearch {} then
      use TuneTabuSearch in tune options run holes tuneFile table
    else never
