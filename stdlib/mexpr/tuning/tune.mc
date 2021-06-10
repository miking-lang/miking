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
  let str = strTrim (readFile file) in
  match str with [] then []
  else map (parseMExprString []) (strSplit " " str)

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

  sem compare =
  | (Runtime {time = t1}, Runtime {time = t2}) ->
    subf t1 t2

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
      match options.input with [] then _inputEmpty else options.input
    in

    -- cost function = sum of execution times over all inputs
    let costF : Assignment -> Cost = lam lookup : Assignment.
      match lookup with Table {table = table} then
        Runtime {time = foldr1 addf (map (time table runner file) input)}
      else error "impossible" in

    -- Comparing costs: use given precision
    let cmpF : Cost -> Cost -> Int = lam t1. lam t2.
      match (t1, t2) with (Runtime {time = t1}, Runtime {time = t2}) then
        let diff = subf t1 t2 in
        if geqf (absf diff) options.epsilonMs then roundfi diff
        else 0
      else error "impossible" in

    -- Set up initial search state
    let startState =
      initSearchState costF cmpF
        (Table {table = table
               , holes = holes
               , options = options})
    in

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
          printLn "-----------------------";
          flushStdout ()
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

-- Search strategies:
-- exhaustive search
-- tabu that doesn't get stuck all the time

-- Explore the search space exhaustively, i.e. try all combinations of all
-- decision points. The decision points are explored from left to right.
lang TuneExhaustive = TuneLocalSearch
  syn MetaState =
  | Exhaustive {prev : [Option Expr], exhausted : Bool}

  sem step (searchState : SearchState) =
  | Exhaustive ({prev = prev, exhausted = exhausted} & x) ->
    if exhausted then
      (None (), Exhaustive x)
    else match searchState with
      {cur =
         {assignment = Table {table = table, holes = holes, options = options}},
       cost = cost}
    then
      let exhausted = ref false in

      recursive let nextConfig = lam prev. lam holes.
        match holes with [] then []
        else match holes with [h] then
          match next (head prev) h with Some v then
            [Some v]
          else
            modref exhausted true; []
        else match holes with [h] ++ holes then
          match next (head prev) h with Some v then
            cons (Some v) (tail prev)
          else
            cons (next (None ()) h) (nextConfig (tail prev) holes)
        else never
      in

      let newTable =
        Table { table = map (optionGetOrElse (lam. "impossible")) prev
              , holes = holes
              , options = options
              } in
      let newPrev = nextConfig prev holes in
      ( Some {assignment = newTable, cost = cost newTable},
        Exhaustive {prev = newPrev, exhausted = deref exhausted})
    else never

  sem initMeta =
  | initState ->
    let initState : SearchState = initState in
    match initState with {cur = {assignment = Table {holes = holes}}} then
      let initVals = map (next (None ())) holes in
      utest all optionIsSome initVals with true in
      Exhaustive {prev = initVals, exhausted = false}
    else never
end

-- Explore the values of each decision point one by one, from left to right,
-- while keeping the rest fixed (to their tuned values, or their defaults if
-- they have note yet been tuned). Hence, it assumes a total independence of the
-- decision points.
lang TuneSemiExhaustive = TuneLocalSearch
  syn MetaState =
  | SemiExhaustive {curIdx : Int, lastImproved : Int, prev : Option Expr}

  sem step (searchState : SearchState) =
  | SemiExhaustive ({curIdx = i, prev = prev, lastImproved = lastImproved} & state) ->
    match searchState
    with {inc = {assignment = Table {table = table,
                                     holes = holes,
                                     options = options},
                 cost = incCost},
          cost = cost, cmp = cmp}
    then
      let return = lam i. lam prev.
        let assignment = Table {table = set table i prev, holes = holes, options = options} in
        let score = cost assignment in
        let lastImproved =
          if lti (cmp score incCost) 0 then i else lastImproved in
        ( Some {assignment = assignment, cost = score},
          SemiExhaustive {curIdx = i, prev = Some prev, lastImproved = lastImproved} )
      in

      -- Avoid repeating default config
      let nextSkipDefault =
        let h = get holes i in
        match next prev h with Some prev then
          if and (use MExprEq in eqExpr prev (default h))
                 (gti (subi i lastImproved) 0) then
            next (Some prev) h
          else Some prev
        else None ()
      in

      match nextSkipDefault with Some prev then
        return i prev
      else
        -- Current hole is exhausted, move to the next
        let i = addi i 1 in
        if eqi i (length holes) then
          -- Finished the search.
          (None (), SemiExhaustive state)
        else match next (None ()) (get holes i) with Some prev then
          return i prev
        else error "Empty value domain"
    else never

  sem initMeta =
  | _ -> SemiExhaustive
    { curIdx = 0
    , lastImproved = subi 0 1  -- to avoid running default config twice
    , prev = None ()
    }

  sem debugMeta =
  | SemiExhaustive {curIdx = i, lastImproved = j, prev = prev} ->
    printLn (join ["Exploring index: ", int2string i, "\n",
                   "Last improved at: ", int2string j, "\n",
                   "Prev: ",
                   optionMapOrElse (lam. "None")
                     (use MExprPrettyPrint in expr2str) prev])
end

lang TuneOneRandomNeighbour = TuneLocalSearch
  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
             Table {holes = holes, table = table, options = options}}}
    then
      let table = map (lam h. sample h) holes in
      iteratorFromSeq [Table {table = table, holes = holes, options = options}]
    else never
end

lang TuneManyRandomNeighbours = TuneLocalSearch
  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
             Table {holes = holes, table = table, options = options}}}
    then
      let step = lam.
        let table = map (lam h. sample h) holes in
        Some (Table {table = table, holes = holes, options = options})
      in
      iteratorInit step identity
    else never
end

lang TuneRandomWalk = TuneLocalSearch
                    + TuneOneRandomNeighbour
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
                            + TuneOneRandomNeighbour
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
                    + TuneManyRandomNeighbours
                    + LocalSearchTabuSearch
                    + LocalSearchSelectFirst
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
    let options = parseTuneOptions tuneOptionsDefault
      (filter (lam a. not (eqString "mi" a)) args) in

    -- Do warmup runs
    use TuneBase in
    iter (lam. map (time table run tuneFile) options.input)
      (range 0 options.warmups 1);

    -- Choose search method
    (match options.method with RandomWalk {} then
       use TuneRandomWalk in tune
     else match options.method with SimulatedAnnealing {} then
       use TuneSimulatedAnnealing in tune
     else match options.method with TabuSearch {} then
       use TuneTabuSearch in tune
     else match options.method with Exhaustive {} then
       use TuneExhaustive in tune
     else match options.method with SemiExhaustive {} then
       use TuneSemiExhaustive in tune
     else never) options run holes tuneFile table
