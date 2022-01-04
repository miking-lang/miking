include "ext/local-search.mc"

include "sys.mc"
include "string.mc"
include "map.mc"
include "common.mc"

include "context-expansion.mc"
include "tune-options.mc"
include "tune-file.mc"

-- Performs tuning of a context expanded program with holes.

-- Start time of search.
let tuneSearchStart = ref 0.

-- Default input if program takes no input data
let _inputEmpty = [""]

-- Return code for timeout
let _returnCodeTimeout = 124

-- Convert from ms to s
let _ms2s = lam ms. divf ms 1000.

-- Filter out duplicates
let _distinct = lam cmp. lam seq.
  setToSeq (setOfSeq cmp seq)

utest _distinct subi [1,2,1] with [1,2]

------------------------------
-- Base fragment for tuning --
------------------------------
type Runner = String -> Option Float -> (Float, ExecResult)

type TimingResult
con Success : {ms : Float} -> TimingResult
con Error : {msg : String, returncode : Int} -> TimingResult
con Timeout : {ms : Float} -> TimingResult

let _timingResult2str : TimingResult -> String = lam t.
  switch t
  case Success {ms = ms} then float2string ms
  case Error {msg = msg, returncode = returncode} then
    join [msg, "\n", concat "returncode: " (int2string returncode)]
  case Timeout {ms = ms} then join ["Timeout at ", float2string ms, " ms"]
  end

lang TuneBase = HoleAst
  sem tune (options : TuneOptions) (run : Runner) (holes : Expr)
           (file : String) (hole2idx : Map NameInfo (Map [NameInfo] Int)) =
  -- Intentionally left blank

  sem time (table : LookupTable) (runner : Runner) (file : String)
           (options : TuneOptions) (timeout : Option Float) =
  | args ->
    let timeout = if options.exitEarly then timeout else None () in
    tuneFileDumpTable file (None ()) table;
    match runner args timeout with (ms, res) then
      let res : ExecResult = res in
      let rcode = res.returncode in
      match rcode with 0 then
        Success {ms = ms}
      else if eqi rcode _returnCodeTimeout then
        Timeout {ms = ms}
      else
        let msg = strJoin " "
        [ "Program returned non-zero exit code during tuning\n"
        , "hole values:\n", _tuneTable2str table, "\n"
        , "command line arguments:", args, "\n"
        , "stdout:", res.stdout, "\n"
        , "stderr:", res.stderr
        ] in
        if options.ignoreErrors then
          Error {msg = msg, returncode = res.returncode}
        else error msg
    else never
end

--------------------------
-- Local search methods --
--------------------------

lang TuneLocalSearch = TuneBase + LocalSearchBase
  syn Assignment =
  | Table {table : LookupTable,
           start : LookupTable,
           holes : [Expr],
           options : TuneOptions,
           hole2idx : Map NameInfo (Map [NameInfo] Int)}

  syn Cost =
  | Runtime {time : TimingResult}

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
      let elapsed = subf (wallTimeMs ()) (deref tuneSearchStart) in
      printLn (join ["Iter: ", int2string iter, "\n",
                     "Current table: ", strJoin ", " curValues, "\n",
                     "Current time: ", _timingResult2str curTime, "\n",
                     "Best time: ", _timingResult2str incTime, "\n",
                     "Best table: ", strJoin ", " incValues, "\n",
                     "Elapsed ms: ", float2string elapsed
                    ])

    else never

  sem tune (options : TuneOptions) (runner : Runner) (holes : [Expr])
           (hole2idx : Map NameInfo (Map [NameInfo] Int)) (file : String) =
  | table ->
    let input =
      match options.input with [] then _inputEmpty else options.input
    in

    -- Cost function: sum of execution times over all inputs
    let costF : Option Solution -> Assignment -> Cost =
      lam inc : Option Solution. lam lookup : Assignment.
        let timeoutVal : Option Float =
          match inc with Some sol then
            let sol : Solution = sol in
            match sol with {cost = Runtime {time = time}} then
              switch time
              case Success {ms = ms} then Some ms
              case Error _ then None ()
              case Timeout _ then error "impossible"
              end
            else never
          else None ()
        in
        match lookup with Table {table = table} then
          let f = lam t1. lam t2.
            switch (t1, t2)
            case (Success {ms = ms1}, Success {ms = ms2}) then addf ms1 ms2
            case ((Error e, _) | (_, Error e)) then Error e
            end
          in
          Runtime {time = foldr1 f (map (time table runner file options timeoutVal) input)}
        else error "impossible" in

    -- Comparing costs: negative if 't1' is better than 't2'
    let cmpF : Cost -> Cost -> Int = lam t1. lam t2.
      match (t1, t2) with (Runtime {time = t1}, Runtime {time = t2}) then
        switch (t1, t2)
        case (Success {ms = ms1}, Success {ms = ms2}) then
          let diff = subf ms1 ms2 in
          if geqf (absf diff) options.epsilonMs then roundfi diff
          else 0
        case (Success {ms = ms}, Error _ | Timeout _) then roundfi (subf 0. ms)
        case (Error _, Error _) then 0
        case (Error _, Success {ms = ms}) then roundfi ms
        case (Error _, Timeout _) then 0
        case (Timeout _, Timeout _) then 0
        case (Timeout _, Error _) then 0
        case (Timeout _, Success {ms = ms}) then roundfi ms
        end
      else error "impossible" in

    -- When to stop the search
    let stopCond = lam niters. lam timeoutMs : Option Float. lam state : SearchState.
      if state.stuck then true
      else if geqi state.iter niters then true
      else match timeoutMs with Some timeout then
        let elapsed = subf (wallTimeMs ()) (deref tuneSearchStart) in
        if geqf elapsed timeout then true else false
      else false
    in

    let normalStop = stopCond options.iters options.timeoutMs in

    let warmupStop = stopCond options.warmups (None ()) in

    recursive let search =
      lam stop.
      lam searchState.
      lam metaState.
      lam iter.
        (if options.verbose then
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
            search stop searchState metaState (addi iter 1)
          else never
    in

    -- Set up initial search state. Repeat the computation n times, where n is
    -- the number of warmup runs, because the cost function is applied once per
    -- setup.
    let mkStartState = lam.
      initSearchState costF cmpF
        (Table { table = table
               , start = table
               , holes = holes
               , options = options
               , hole2idx = hole2idx
               })
    in
    iter mkStartState (make options.warmups ());
    let beforeStartState = wallTimeMs () in
    let startState = mkStartState () in
    let afterStartState = wallTimeMs () in

    -- Timestamp of start of search (including time to create the start state)
    let startOfSearch = lam.
      subf (wallTimeMs ()) (subf afterStartState beforeStartState)
    in

    -- Do warmup runs and throw away results
    modref tuneSearchStart (startOfSearch ());
    (if options.verbose then
       printLn "----------------------- WARMUP RUNS -----------------------"
       else ());
    search warmupStop startState (initMeta startState) 0;
    (if options.verbose then
       printLn "-----------------------------------------------------------"
       else ());

    -- Do the search!
    modref tuneSearchStart (startOfSearch ());
    match search normalStop startState (initMeta startState) 0
    with (searchState, _) then
      let searchState : SearchState = searchState in
      match searchState with {inc = {assignment = Table {table = table}}}
      then table
      else never
    else never
end

-- Explore the search space exhaustively, i.e. try all combinations of all
-- holes. The holes are explored from left to right.
lang TuneExhaustive = TuneLocalSearch
  syn MetaState =
  | Exhaustive {prev : [Option Expr], exhausted : Bool}

  sem step (searchState : SearchState) =
  | Exhaustive ({prev = prev, exhausted = exhausted} & x) ->
    if exhausted then
      (None (), Exhaustive x)
    else match searchState with
      {cur =
         {assignment = Table ({table = table, holes = holes} & t)},
       cost = cost,
       inc = inc}
    then
      let exhausted = ref false in
      let options : TuneOptions = t.options in
      let stepSize = options.stepSize in

      recursive let nextConfig = lam prev. lam holes.
        match holes with [] then []
        else match holes with [h] then
          match next (head prev) stepSize h with Some v then
            [Some v]
          else
            modref exhausted true; []
        else match holes with [h] ++ holes then
          match next (head prev) stepSize h with Some v then
            cons (Some v) (tail prev)
          else
            cons (next (None ()) stepSize h) (nextConfig (tail prev) holes)
        else never
      in

      let newTable =
        Table {t with table = map (optionGetOrElse (lam. "impossible")) prev}
      in
      let newPrev = nextConfig prev holes in
      ( Some {assignment = newTable, cost = cost (Some inc) newTable},
        Exhaustive {prev = newPrev, exhausted = deref exhausted})
    else never

  sem initMeta =
  | initState ->
    let initState : SearchState = initState in
    match initState with {cur = {assignment = Table {holes = holes}}} then
      let initVals = map (next (None ()) 1) holes in
      utest forAll optionIsSome initVals with true in
      Exhaustive {prev = initVals, exhausted = false}
    else never
end

-- Explore the values of each hole one by one, from left to right,
-- while keeping the rest fixed (to their tuned values, or their defaults if
-- they have note yet been tuned). Hence, it assumes a total independence of the
-- holes.
lang TuneSemiExhaustive = TuneLocalSearch
  syn MetaState =
  | SemiExhaustive {curIdx : Int, lastImproved : Int, prev : Option Expr}

  sem step (searchState : SearchState) =
  | SemiExhaustive ({curIdx = i, prev = prev, lastImproved = lastImproved} & state) ->
    match searchState
    with {inc = {assignment = Table ({table = table, start = start, holes = holes} & t),
                 cost = incCost},
          cost = cost, cmp = cmp}
    then
      let options : TuneOptions = t.options in
      let stepSize = options.stepSize in

      let return = lam i. lam prev.
        let assignment = Table {t with table = set table i prev} in
        let score = cost (Some searchState.inc) assignment in
        let lastImproved =
          if lti (cmp score incCost) 0 then i else lastImproved in
        ( Some {assignment = assignment, cost = score},
          SemiExhaustive {curIdx = i, prev = Some prev, lastImproved = lastImproved} )
      in

      recursive let nextSkipStart = lam prev. lam i.
        if eqi i (length holes) then
          -- Finished the search
          (None (), SemiExhaustive state)
        else
          let prev = next prev stepSize (get holes i) in
          match prev with Some v then
          -- Skip start value, already explored
          if (use MExprEq in eqExpr v (get start i)) then
            nextSkipStart prev i
          else
            return i v
        else match prev with None () then
          -- Current hole is exhausted, move to the next
          nextSkipStart (None ()) (addi i 1)
        else never
      in
      nextSkipStart prev i

    else never

  sem initMeta =
  | _ -> SemiExhaustive
    { curIdx = 0
    , lastImproved = subi 0 1
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

lang TuneOneRandomNeighbourModifyOne = TuneLocalSearch
  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
             Table ({holes = holes, table = table} & t)}}
    then
      let table =
        switch randIndex table
        case None () then table
        case Some i then
          let randHole = get holes i in
          let modifiedHole = sample randHole in
          set table i modifiedHole
        end
      in iteratorFromSeq [Table {t with table = table}]
    else never
end

lang TuneOneRandomNeighbourModifyAll = TuneLocalSearch
  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
             Table ({holes = holes, table = table} & t)}}
    then
      let table = map (lam h. sample h) holes in
      iteratorFromSeq [Table {t with table = table}]
    else never
end

lang TuneManyRandomNeighboursModifyAll = TuneLocalSearch
  sem neighbourhood =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with {cur =
           {assignment =
           Table ({holes = holes, table = table} & t)}}
    then
      let step = lam.
        let table = map (lam h. sample h) holes in
        Some (Table {t with table = table})
      in
      iteratorInit step identity
    else never
end

lang TuneRandomWalk = TuneLocalSearch
                    + TuneOneRandomNeighbourModifyAll
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
                            + TuneOneRandomNeighbourModifyOne
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
                    + TuneManyRandomNeighboursModifyAll
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


let _binarySearch = lam lower : Int. lam mid : Int. lam upper : Int. lam curCost : a. lam cost : Int -> a. lam cmp : a -> a -> Int.
  -- Avoid applying cost function on the same value twice
  let memoized = mapInsert mid curCost (mapEmpty subi) in

  recursive let work = lam mem : Map Int a. lam lower : Int. lam mid : Int. lam upper : Int. lam curCost : a.
    if eqi lower upper then (curCost, mid)
    else
      let lowPoint = divi (addi lower mid) 2 in
      let highPoint = ceilfi (divf (int2float (addi upper mid)) 2.) in

      match
        if eqi lowPoint mid then (curCost, mem)
        else match mapLookup lowPoint mem with Some v then (v, mem)
        else
          let c = cost lowPoint in
          (c, mapInsert lowPoint c mem)
      with (lowCost, mem) then match
        if eqi highPoint mid then (curCost, mem)
        else match mapLookup highPoint mem with Some v then (v, mem)
        else
          let c = cost highPoint in
          (c, mapInsert highPoint c mem)
      with (highCost, mem) then
        -- lower is better, recurse
        if lti (cmp lowCost curCost) 0 then
          work mem lower lowPoint mid lowCost
        -- higher is better, recurse
        else if lti (cmp highCost curCost) 0 then
          work mem mid highPoint upper highCost
        -- none is better, end
          else (curCost, mid)
      else never else never
  in work memoized lower mid upper curCost

utest _binarySearch 1 1 1 0 (lam x. x) subi with (0, 1)
utest _binarySearch 1 2 3 2 (lam x. x) subi with (1, 1)
utest _binarySearch 1 2 3 (negi 2) (lam x. negi x) subi with (negi 3, 3)
utest _binarySearch 1 1 2 1 (lam x. x) subi with (1, 1)
utest _binarySearch 1 3 10 9 (lam x. muli x x) subi with (1, 1)

lang TuneBinarySearch = TuneLocalSearch
   syn MetaState =
   | BS {curIdx : Int}

   sem initMeta =
   | _ ->
     BS {curIdx = 0}

   sem step (searchState : SearchState) =
   | BS ({curIdx = curIdx} & t) ->
     match searchState with {cur = {assignment = Table ({table = table, holes = holes} & a), cost = curCost}, cost = costF, cmp = cmpF, inc = inc}
     then
       if eqi curIdx (length holes) then (None (), BS t) else
       let h = get holes curIdx in
       let lowerUpper = use MExprHoles in
                        match h with TmHole {inner = HIntRange {min = min, max = max}}
                        then (min, max)
                        else dprintLn h; error "Binary search only supported for IntRange"
       in
       let curExpr = get table curIdx in
       let curVal = match curExpr with TmConst {val = CInt {val = i}} then i else error "impossible" in

       let assignmentWithVal = lam v : Int.
         Table {a with table = set a.table curIdx (int_ v)}
       in
       let costFromVal = lam v : Int.
         costF (Some inc) (assignmentWithVal v)
       in

       match _binarySearch lowerUpper.0 curVal lowerUpper.1 curCost costFromVal cmpF
       with (bestCost, bestVal)
       then (Some {assignment = assignmentWithVal bestVal, cost = bestCost},
             BS {t with curIdx = addi curIdx 1})
       else never
     else never

  sem debugMeta =
  | BS {curIdx = i} ->
    printLn (join ["Next index to explore: ", int2string i, "\n"])

end

lang MExprTune = MExpr + TuneBase

-- Entry point for tuning
let tuneEntry =
  lam binary : String.
  lam options : TuneOptions.
  lam tuneFile : String.
  lam env : CallCtxEnv.
  lam table : LookupTable.

    -- Set the random seed?
    (match options.seed with Some seed then randSetSeed seed else ());

    let holes : [Expr] = env.idx2hole in
    let hole2idx : Map NameInfo (Map [NameInfo] Int) = env.hole2idx in

    -- Runs the program with a given command-line input and optional timeout
    let runner = lam input : String. lam timeoutMs : Option Float.
        sysRunCommandWithTimingTimeout (optionMap _ms2s timeoutMs) [binary] input "."
    in

    -- Choose search method
    (switch options.method
     case RandomWalk {} then use TuneRandomWalk in tune
     case SimulatedAnnealing {} then use TuneSimulatedAnnealing in tune
     case TabuSearch {} then use TuneTabuSearch in tune
     case Exhaustive {} then use TuneExhaustive in tune
     case SemiExhaustive {} then use TuneSemiExhaustive in tune
     case BinarySearch {} then use TuneBinarySearch in tune
     end)
     options runner holes hole2idx tuneFile table
