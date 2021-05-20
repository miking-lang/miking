include "ext/local-search.mc"
include "ocaml/sys.mc"
include "map.mc"
include "decision-points.mc"
include "options.mc"
include "common.mc"

type Runner = String -> ExecResult

-- Turn on/off debug prints
let _debug = true

let _inputEmpty = [""]

-- Add assignments of decision points to argument vector
let _addToArgs = lam vals : LookupTable. lam args : CommandLineArgs.
  use MExprPrettyPrint in
  let stringVals = mapMapWithKey (lam. lam v. expr2str v) vals in
  concat args (mapValues stringVals)

lang TuneBase = Holes
  sem tune (run : Runner) (holes : Expr) =
  -- Intentionally left blank

  sem time (vals : LookupTable) (runner : Runner) =
  | args ->
    let allArgs = _addToArgs vals args in
    let t1 = wallTimeMs () in
    let res : ExecResult = runner allArgs in
    let t2 = wallTimeMs () in
    print "Result: "; dprintLn res;
    match res.returncode with 0 then
      subf t2 t1
    else
      let msg = strJoin " "
      [ "Program returned non-zero exit code during tuning\n"
      , "command line arguments:", strJoin " " args, "\n"
      , "all command line arguments:", strJoin " " allArgs, "\n"
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
           holes : [Expr]}

  syn Cost =
  | Runtime {time : Float}

  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur = {assignment = Table {holes = holes}}}
    then
      let table = mapFromList subi
        (mapi (lam i. lam h.
           match h with TmHole {hole = hole} then
             (i, sample hole)
           else dprintLn h; error "Expected decision point") holes) in
      [Table {table = table, holes = holes}]
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
                  cost = Runtime {time = time}}
         , cur = {assignment = Table {table = cur}}}
    then
      use MExprPrettyPrint in
      let incValues = map expr2str (mapValues inc) in
      let curValues = map expr2str (mapValues cur) in
      printLn (join ["Iter: ", int2string iter, "\n",
                     "Best time: ", float2string time, "\n",
                     "Current table: ", strJoin ", " curValues, "\n",
                     "Best table: ", strJoin ", " incValues])

    else never

  sem tune (runner : Runner) (holes : [Expr]) =
  | table ->
    let input =
      match tuneOptions.input with [] then _inputEmpty else tuneOptions.input in
    -- cost function = sum of execution times over all inputs
    let costF = lam lookup : Assignment.
      match lookup with Table {table = table} then
        Runtime {time = foldr1 addf (map (time table runner) input)}
      else never in

    -- Set up initial search state
    let startState =
      initSearchState costF (Table {table = table, holes = holes}) in

    -- When to stop the search
    let stop = lam state : SearchState.
      or state.stuck (geqi state.iter tuneOptions.iters) in

    recursive let search =
      lam stop.
      lam searchState.
      lam metaState.
        (if _debug then
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
    match search stop startState (initMeta table)
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
    SimulatedAnnealing {t with temp = mulf tuneOptions.saDecayFactor t.temp}

  sem initMeta =
  | _ -> SimulatedAnnealing {temp = tuneOptions.saInitTemp}

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
    match find (lam t. eqSeq eqExpr (mapValues table) (mapValues t)) tabu
    with Some _ then true else false

  sem tabuUpdate =
  | (Table {table = table}, Tabu ({tabu = tabu} & t)) ->
    let tabu = cons table
      (if eqi (length tabu) tuneOptions.tabuSize then init tabu else tabu) in
    Tabu {t with tabu = tabu}

  sem initMeta =
  | table -> TabuSearch {tabu = Tabu {tabu = [table]}}

  sem debugMeta =
  | TabuSearch {tabu = Tabu {tabu = tabu}} ->
    printLn (join ["Tabu size: ", int2string (length tabu)])
end

lang MExprTune = MExpr + TuneBase

let tuneEntry = lam run : Runner. lam holes : [Expr]. lam table : LookupTable.
  -- Do warmup runs
  use TuneBase in
  iter (lam. map (time table run) tuneOptions.input)
    (range 0 tuneOptions.warmups 1);

  -- Choose search method
  match tuneOptions.method with RandomWalk {} then
    use TuneRandomWalk in tune run holes table
  else match tuneOptions.method with SimulatedAnnealing {} then
    use TuneSimulatedAnnealing in tune run holes table
  else match tuneOptions.method with TabuSearch {} then
    use TuneTabuSearch in tune run holes table
  else never
