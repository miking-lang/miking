include "mexpr/decision-points.mc"
include "ext/local-search.mc"
include "common.mc"
include "ocaml/sys.mc"
include "map.mc"

type Stdin = String
type CommandLineArgs = [String]
type InputData = (CommandLineArgs, Stdin)
type Runner = InputData -> ExecResult

type SearchMethod
con SimulatedAnnealing : Unit -> SearchMethod
con TabuSearch         : Unit -> SearchMethod
con RandomWalk         : Unit -> SearchMethod

type TuneOptions =
{ iters : Int
, method : SearchMethod
}

let _bool2string = lam b.
  if b then "true" else "false"

let _dataEmpty = [([""], "")]

-- Turn on/off debug prints
let _debug = true

-- Add assignments of decision points to argument vector
let _addToArgs = lam vals : LookupTable. lam args : CommandLineArgs.
  use MExprAst in
  -- TODO: types
  let stringVals = mapMapWithKey (lam. lam v.
    match v with TmConst {val = CBool {val = b}} then _bool2string b
    else dprintLn v; error "The type of this value is not supported yet"
  ) vals in
  concat args (mapValues stringVals)

lang TuneBase = HoleAst + FlattenHoles
  sem tune (run : Runner) (data : [InputData]) (options : TuneOptions) =
  -- Intentionally left blank

  sem time (vals : LookupTable) (runner : Runner) =
  | (args, stdin) ->
    let allArgs = _addToArgs vals args in
    let t1 = wallTimeMs () in
    let res : ExecResult = runner (allArgs, stdin) in
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
let _expr2str = use MExprAst in lam expr.
  match expr with TmConst {val = CBool {val = b}} then
    _bool2string b
  else dprintLn expr; error "Expr type not supported yet"

lang TuneLocalSearch = TuneBase + LocalSearchBase
  syn Assignment =
  | Table {table : LookupTable}

  syn Cost =
  | Runtime {time : Float}

  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with {cur = {assignment = Table {table = table}}} then
      -- TODO: assumes Boolean decision points
      let randTable = mapMapWithKey (lam. lam v.
        if eqi 0 (randIntU 0 2) then false_ else true_) table in
      [Table {table = randTable}]
    else never

  sem compare =
  | (Runtime {time = t1}, Runtime {time = t2}) ->
    roundfi (mulf 1000.0 (subf t1 t2))

  sem initMeta =

  sem debugSearch =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {iter = iter, inc = {assignment = Table {table = table},
                              cost = Runtime {time = time}}}
    then
      let values = map _expr2str (mapValues table) in
      printLn (join ["Iter: ", int2string iter, "\n",
                     "Best time: ", float2string time, "\n",
                     "Best table: ", strJoin ", " values])

    else never

  sem tune (runner : Runner) (data : [InputData]) (options : TuneOptions) =
  | table ->
    let data = match data with [] then _dataEmpty else data in
    -- cost function = sum of execution times over all inputs
    let costF = lam lookup : Assignment.
      match lookup with Table {table = table} then
        Runtime {time = foldr1 addf (map (time table runner) data)}
      else never in

    -- Set up initial search state
    let startState = initSearchState costF (Table {table = table}) in

    -- When to stop the search
    let stop = lam state : SearchState.
      or state.stuck (geqi state.iter options.iters) in

    recursive let search =
      lam stop.
      lam searchState.
      lam metaState.
        debugSearch searchState;
        if stop searchState then
          (searchState, metaState)
        else
          match minimize searchState metaState with (searchState, metaState)
          then
            search stop searchState metaState
          else never
    in

    -- Do the search!
    search stop startState (initMeta ())
end

lang RandomWalk = TuneLocalSearch
                + LocalSearchSelectRandomUniform
  syn MetaState =
  | Empty {}

  sem step (searchState : SearchState) =
  | Empty {} ->
    (select (neighbourhood searchState) searchState, Empty {})

  sem initMeta =
  | () -> Empty {}
end

lang MExprTune = RandomWalk
