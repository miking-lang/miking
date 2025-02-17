include "ext/local-search.mc"

include "sys.mc"
include "string.mc"
include "map.mc"
include "common.mc"

include "context-expansion.mc"
include "tune-options.mc"
include "tune-file.mc"
include "search-space.mc"
include "database.mc"
include "tune-stats.mc"

-- Included for testing
include "mexpr/shallow-patterns.mc"
include "ocaml/mcore.mc"
include "ocaml/pprint.mc"

-- Performs tuning of a context expanded program with holes.

-- Start time of search.
let tuneSearchStart = ref 0.

------------------------------
-- Base fragment for tuning --
------------------------------

type Runner = String -> Option Float -> (Float, ExecResult)

type TimingResult
con Success : {ms : Float} -> TimingResult
con Error : {msg : String, returncode : Int} -> TimingResult
con Timeout : {ms : Float} -> TimingResult

lang TuneBase = HoleAst
  sem tune : String -> TuneOptions -> CallCtxEnv -> DependencyGraph
           -> InstrumentedResult -> ContextExpanded -> Expr -> LookupTable
  sem tune binary options env dep inst exp =
  | ast ->
    -- Set the random seed?
    (match options.seed with Some seed then randSetSeed seed else ());

    let holes : [Expr] = env.idx2hole in
    let hole2idx : Map NameInfo (Map [NameInfo] Int) = env.hole2idx in

    let ms2s = lam ms. divf ms 1000. in

    -- Runs the program with a given command-line input and optional timeout
    let runner = lam input : String. lam timeoutMs : Option Float.
      sysRunCommandWithTimingTimeout (optionMap ms2s timeoutMs) [binary, input] "" "."
    in

    let cleanup = lam.
      exp.cleanup ();
      inst.cleanup ()
    in

    _tune options runner env dep inst exp.tempFile cleanup exp.table ast

  sem _tune : TuneOptions -> Runner -> CallCtxEnv -> DependencyGraph
            -> InstrumentedResult -> String -> (() -> ()) -> LookupTable -> Expr
            -> LookupTable

  sem measure (env: CallCtxEnv) (table: LookupTable) (runner: Runner)
              (file: String) (options: TuneOptions) (timeout: Option Float)
              (onFailure: () -> ()) =
  | args ->
    let timeout = if options.exitEarly then timeout else None () in
    tuneFileDumpTable file env table false;
    match runner args timeout with (ms, res) then
      let res : ExecResult = res in
      let rcode = res.returncode in
      match rcode with 0 then
        Success {ms = ms}
      else if eqi rcode 124 then
        Timeout {ms = ms}
      else
        let msg = strJoin " "
        [ "Program returned non-zero exit code during tuning\n"
        , "hole values:\n", _tuneTable2str env table, "\n"
        , "command line arguments:", args, "\n"
        , "stdout:", res.stdout, "\n"
        , "stderr:", res.stderr
        ] in
        if options.ignoreErrors then
          Error {msg = msg, returncode = res.returncode}
        else
          onFailure ();
          error msg
    else never

  sem programInput =
  | options ->
    let options : TuneOptions = options in
    let input =
      match options.args with [] then [""] else options.args
    in
    input
end

--------------------------------
-- Local search base fragment --
--------------------------------

lang TuneLocalSearch = TuneBase + LocalSearchBase
  syn LSData =

  sem initMeta : LSData -> SearchMethod -> MetaState

  sem debugSearch : SearchState -> ()

  sem debugMeta : MetaState -> ()

  sem updateSearchState : SearchState -> SearchState

  -- Default master search loop
  sem search (options : TuneOptions) (stop : SearchState -> Bool) (state : SearchState) =
  | meta ->
    let iter = state.iter in
    let printState = lam header. lam state. lam meta.
      if options.verbose then
        printLn header;
        debugSearch state;
        debugMeta meta;
        printLn (make (length header) '-')
       else ()
    in
    (if eqi iter 0 then
      printState "----- Initial state -----" state meta
     else ());

    if stop state then
      printState "----- Final state -----" state meta;
      (state, meta)
    else match minimize state meta with (state, meta) in
      let state = updateSearchState state in
      printState "            " state meta;
      search options stop state meta

  -- When to stop the search
  sem stopCond (maxIters : Int) (timeoutMs : Option Float) =
  | state ->
    let state : SearchState = state in
    if state.stuck then true
    else if geqi state.iter maxIters then true
    else match timeoutMs with Some timeout then
      let elapsed = subf (wallTimeMs ()) (deref tuneSearchStart) in
      geqf elapsed timeout
    else stopCondState state

  -- Additional stop condition based on search state
  sem stopCondState : SearchState -> Bool

  -- By default, the default table is also the initial table.
  sem initialTable (defaultTable : LookupTable) =
  | _ -> defaultTable

  -- By default, the search space is not reduced
  sem reduceSearchSpace
  : (Option Solution -> Assignment -> Cost) -> Expr -> LSData -> LSData
  sem reduceSearchSpace costF t =
  | d -> d

  -- Check if the search space is empty
  sem emptySearchSpace =
  | _ -> false

  -- Entry point for tuning
  sem _tune (options : TuneOptions) (run : Runner) (env : CallCtxEnv)
           (dep : DependencyGraph) (inst : InstrumentedResult)
           (tuneFile : String) (onFailure : () -> ()) (defaultTable: LookupTable) =
  | t ->
    match _tuneDebug options run env dep inst tuneFile onFailure defaultTable t
    with (table, _) in table

  -- Like 'tune', but also returns the final search state (for testing)
  sem _tuneDebug (options : TuneOptions) (run : Runner) (env : CallCtxEnv)
                 (dep : DependencyGraph) (inst : InstrumentedResult)
                 (tuneFile : String) (onFailure : () -> ())
                 (defaultTable : LookupTable) =
  | t ->
    -- Nothing to tune?
    if null defaultTable then ([], None ()) else

    let data = initData options run env dep inst t in
    let costF : Option Solution -> Assignment -> Cost =
      costFun run tuneFile options (programInput options) data onFailure
    in
    let data = reduceSearchSpace costF t data in
    if emptySearchSpace data then
      (if options.verbose then
         printLn "Empty search space detected, tuning will use the default configuration for the program holes.";
         print "Default table: ";
         printLn (strJoin " " (map expr2str defaultTable))
       else ());
       (defaultTable, None ())
    else
      let meta = initMeta data options.method in
      let initTable = initialTable defaultTable meta in

      -- Warmup runs
      match warmupInit costF initTable data options with (initTime, startState) in
      let startState = updateSearchState startState in
      warmupSearch initTime options meta startState;

      -- Do the search!
      let stop = stopCond options.iters options.timeoutMs in
      modref tuneSearchStart (subf (wallTimeMs ()) initTime);
      match search options stop startState meta
      with (searchState, _) in
      (optimalLookupTable searchState, Some searchState)

  sem initData : TuneOptions -> Runner -> CallCtxEnv -> DependencyGraph
               -> InstrumentedResult -> Expr -> LSData

  sem costFun : Runner -> String -> TuneOptions -> [String] -> LSData
              -> (() -> ()) -> (Option Solution) -> Assignment -> Cost

  sem cmpCost : Cost -> Cost -> Int

  sem mkStartState : (Option Solution -> Assignment -> Cost) -> LookupTable -> LSData
                   -> SearchState

  sem warmupInit (costF : Option Solution -> Assignment -> Cost)
                 (table : LookupTable) (data : LSData) =
  | options ->
    let options : TuneOptions = options in
    let normalStop = stopCond options.iters options.timeoutMs in
    let warmupStop = stopCond options.warmups options.timeoutMs in

    -- Set up initial search state. Repeat the computation of the initial cost n
    -- times, where n is the number of warmup runs, because the cost function is
    -- applied once per setup.
    map (mkStartState costF table) (make options.warmups data);
    -- Warmed up and ready, create the actual start state
    let beforeStartState = wallTimeMs () in
    let startState = mkStartState costF table data in
    let afterStartState = wallTimeMs () in

    (subf afterStartState beforeStartState, startState)

  sem warmupSearch (initTime : Float) (options : TuneOptions) (meta : MetaState) =
  | startState ->
    let normalStop = stopCond options.iters options.timeoutMs in
    let warmupStop = stopCond options.warmups options.timeoutMs in

    -- Do warmup runs and throw away results
    modref tuneSearchStart (subf (wallTimeMs ()) initTime);
    (if options.verbose then
       printLn "----------------------- WARMUP RUNS -----------------------"
     else ());
    search options warmupStop startState meta;
    (if options.verbose then
      printLn "-----------------------------------------------------------"
     else ())

  sem optimalLookupTable : SearchState -> LookupTable
end

-----------------------------
-- Dependency-aware tuning --
-----------------------------

lang TuneDep = TuneLocalSearch + Database + TuneStats
  syn LSData =
  | TuneData { options : TuneOptions, run : Runner, env : CallCtxEnv,
               dep : DependencyGraph, inst : InstrumentedResult,
               database : Database, searchSpace : SearchSpaceSize }

  syn Assignment =
  | Table { table : LookupTable }

  syn Cost =
  | Runtime { time : TimingResult, profiles : [String] }

  sem debugSearch =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState
    with { iter = iter
         , inc = {assignment = Table {table = inc},
                  cost = Runtime {time = incTime}}
         , cur = {assignment = Table {table = cur},
                  cost = Runtime {time = curTime}}
         , data = Some (TuneData { searchSpace = space, database = db })
         }
    then
      let elapsed = subf (wallTimeMs ()) (deref tuneSearchStart) in
      -- OPT(Linnea, 2022-02-08): Increase % incrementally
      let entries = databaseCount db in
      let exploredReduced = divf (int2float entries) space.sizeReduced in
      let exploredTotal = divf (int2float entries) space.sizeTotal in
      match optimalAssignment searchState with (table, ms) in
      let table = map expr2str table in
      let cur = map expr2str cur in

      printLn (join ["Iteration: ", int2string iter, "\n",
                     "Elapsed: ", float2string elapsed, " ms \n",
                     "Just evaluated: ", strJoin ", " cur, "\n",
                     "Best table: ", strJoin ", " table, "\n",
                     "Estimated cost: ", float2string ms, " ms \n",
                     "# assignments explored: ", int2string entries, "\n",
                     "% of total search space explored: ", float2string (mulf 100. exploredTotal), "\n",
                     "% of reduced search space explored: ", float2string (mulf 100. exploredReduced)
                    ])

    else never

  sem initData (options : TuneOptions) (run : Runner) (env : CallCtxEnv)
               (dep : DependencyGraph) (instrumentedResult : InstrumentedResult) =
  | t ->
    -- Compute size of the search space
    let searchSpace =
      use SearchSpace in
      searchSpaceSize options.stepSize env dep
    in
    -- Initialize database
    -- NOTE: uses the total number of measuring points (including dead ones).
    -- The reason is that the database collects profiling data, which will
    -- include data from _all_ measuring points.
    let database = databaseEmpty dep.offset dep.nbrMeas in

    (if options.printStats then
       printLn (tuneStats options dep searchSpace env t)
     else ());

    TuneData {
      options = options,
      run = run,
      env = env,
      dep = dep,
      inst = instrumentedResult,
      database = database,
      searchSpace = searchSpace
    }

  sem reduceSearchSpace costF t =
  | TuneData d ->
    -- Do a number of measurement with randomized tables
    let data =
      if gtf d.options.reduceDependencies 0. then
        let nbrRandRuns = 10 in
        let profiles = foldl (lam acc. lam.
            let randomTable: [Expr] = map (sample d.options.stepSize) d.env.idx2hole in
            match costF (None ()) (Table { table = randomTable }) with Runtime r in
            concat acc r.profiles
          ) [] (create nbrRandRuns (lam i. i))
        in
        let profile: InstrumentationProfile = getProfile profiles in
        match profile with {ids= ids, nbrRuns= nbrRuns, totalMs= totalMs} in
        let idRuns: [(Int,Int)] = zip ids nbrRuns in
        let idRunsTotalMs: [(Int,Int,Float)] =
            zipWith (lam x1: (Int,Int). lam x2: Float.
              (x1.0, x1.1, x2)
          ) idRuns totalMs
        in
        let sorted = sort (lam t1: (Int, Int, Float). lam t2: (Int, Int, Float).
          cmpfApprox 0. t1.2 t2.2) idRunsTotalMs
        in

        -- Print the result
        (if d.options.printStats then
          printLn (tuneStatsTime sorted)
         else ());

        -- Collect those id's that are below the threshold. Multiply by nbrRuns so
        -- that we are considering the mean.
        let threshold = mulf d.options.reduceDependencies (int2float nbrRandRuns) in
        let idsToRemove = foldl (lam acc. lam t: (Int,Int,Float).
            if ltf (subf t.2 threshold) 0. then cons t.0 acc
            else acc
          ) [] sorted
        in
        -- Remove the corresponding nodes from the dependency graph
        let graph = foldl (lam acc. lam id.
            graphRemoveVertex id acc
          ) d.dep.graph idsToRemove
        in
        let dep = {d.dep with graph = graph} in
        -- Mark the removed measuring points as not alive
        let alive = foldl (lam acc. lam id.
            setRemove id acc
          ) d.dep.alive idsToRemove
        in
        let dep = {d.dep with alive = alive} in
        -- Re-initialize the data from the updated graph
        initData d.options d.run d.env dep d.inst t
      else TuneData d
    in
    data

  -- Check if the search space is empty
  sem emptySearchSpace =
  | TuneData d ->
    eqf d.searchSpace.sizeReduced 0.

  sem getProfile =
  | profiles ->
    let mergeProfiles = lam p1: InstrumentationProfile. lam p2: InstrumentationProfile.
      match (p1, p2) with
        ( {ids= ids1, nbrRuns= nbrRuns1, totalMs= totalMs1}
        , {ids= ids2, nbrRuns= nbrRuns2, totalMs= totalMs2}
        ) in
      utest eqSeq eqi ids1 ids2 with true in
      let ids = ids1 in
      let nbrRuns = zipWith addi nbrRuns1 nbrRuns2 in
      let totalMs = zipWith addf totalMs1 totalMs2 in
      {ids=ids, nbrRuns=nbrRuns, totalMs=totalMs}
    in
    let profiles = map readProfile profiles in
    let profile = foldl1 mergeProfiles profiles in
    profile

  -- Add a table to the data base, and return the updated search state.
  sem addToDatabase (searchState: SearchState) (profiles: [String]) =
  | Table { table = table } ->
    match searchState with {data = Some (TuneData d)} in
    let profile = getProfile profiles in
    let newDb = databaseAddRun table profile d.dep.offset d.database in
    { searchState with data = Some (TuneData {d with database = newDb}) }

  sem updateSearchState =
  | state ->
    let state : SearchState = state in
    -- Update search state with database
    match state with {cur = {assignment = a, cost  = Runtime {profiles = strs}}} then
      addToDatabase state strs a
    else error "Unexpected search state"

  -- Check for exhausted search space
  sem stopCondState =
  | state ->
    let state : SearchState = state in
    match state with {data = Some (TuneData {database = db, searchSpace = ss})}
    then geqf (int2float (databaseCount db)) ss.sizeReduced
    else error "Expected tune data"

  sem costFun (run : Runner) (tuneFile : String) (options : TuneOptions)
              (input : [String]) (data : LSData) (onFailure : () -> ())
              (inc : Option Solution) =
  | Table { table = table } ->
    match data with TuneData {inst = inst, env = env} in
    let f = lam i. measure env table run tuneFile options (None ()) onFailure i in
    match foldl (lam acc: (Float, [String]). lam inp.
        match acc with (ms, strs) in
        match f inp with Success {ms = ms2} then
          let s = readFile inst.fileName in
          (addf ms ms2, snoc strs s)
        else error "Program had errors"
      ) (0., []) input
    with (totalMs, profiles) in
    Runtime {time = Success {ms = totalMs}, profiles = profiles}

  -- Disable comparison (optimality is computed from database)
  sem cmpCost (cost : Cost) =
  | _ -> 0

  sem mkStartState (costF : Option Solution -> Assignment -> Cost)
                   (table : LookupTable) =
  | TuneData d ->
    let a = (Table { table = table }) in
    let cost = costF (None ()) a in
    initSearchStateData costF cmpCost (TuneData d) {assignment=a, cost=cost}

  sem optimalAssignment =
  | searchState ->
    let searchState : SearchState = searchState in
    match searchState with
      {data = Some (TuneData { database = db, options = opt, dep = dep,
                               searchSpace = ss })}
    then
      databaseOptimal 0.0 dep ss db
    else error "Expected tune data"

  sem optimalLookupTable =
  | searchState ->
    match optimalAssignment searchState with (table, _) in table
end

lang TuneDepExhaustive = TuneDep + SearchSpace
  syn MetaState =
  | MetaExhaustive { tables : DataFrame (Option Expr) }

  sem initMeta data =
  | Exhaustive {} ->
    match data with TuneData d in
    let df: DataFrame (Option Expr) = searchSpaceExhaustive d.options.stepSize d.env d.dep in
    -- If the first row contains a None (), it means that hole is not connected
    -- to a measuring point. Set those to the default value.
    let row0 = mapi (lam i. lam v.
        match v with Some _ then v
        else Some (default (get d.env.idx2hole i))
      ) (head df.data)
    in
    let df = dataFrameSetRow 0 row0 df in
    MetaExhaustive {tables = df}

  sem initialTable (defaultTable : LookupTable) =
  | MetaExhaustive {tables = tables} ->
    let res =
    mapi (lam i. lam v.
      match v with Some v then v
      -- If first value is None (), then the hole affects no measuring point.
      -- Use default value instead.
      else get defaultTable i
    ) (head tables.data)
    in
    res

  sem step (searchState : SearchState) =
  | MetaExhaustive { tables = tables } ->
    match searchState with { iter = iter, cost = cost, data = data } in
    match data with Some (TuneData {env = env, options = options}) then
      let row = iter in
      if lti row (dataFrameLength tables) then
        let r : [Option Expr] = dataFrameGetRow row tables in
        -- TODO(Linnea, 2022-02-08): What is the best value to fill a bubble
        -- with?
        let t = mapi (lam i. lam o.
          match o with Some e then e
          else match o with None () then
            -- For now, pick the default value
            default (get env.idx2hole i)
          else never) r
        in
        let a = Table {table = t} in
        ( Some {assignment = a, cost = cost (None ()) a}
        , MetaExhaustive {tables = tables} )
      else ( None(), MetaExhaustive {tables = tables} )
    else error "Expected tune data"
end

lang MExprTune = MExpr + TuneDepExhaustive end

lang TestLang =
  MExprTune + GraphColoring + MExprHoleCFA + DependencyAnalysis +
  NestedMeasuringPoints + ContextExpand + Instrumentation +
  BootParser + MExprSym + MExprPrettyPrint + MExprEval + MExprTypeCheck +
  MExprLowerNestedPatterns + MCoreCompileLang
end

mexpr

use TestLang in

-- Enable debug prints
let debug = false in
-- Enable tests that depend on timing of runs
let timeSensitive = false in

let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in

let test : Bool -> Bool -> TuneOptions -> Expr -> (LookupTable, Option SearchState) =
  lam debug. lam full. lam options: TuneOptions. lam expr.
    -- Use small ANF first, needed for context expansion
    let tANFSmall = use HoleANF in normalizeTerm expr in

    -- Do graph coloring to get context information (throw away the AST).
    match colorCallGraph [] tANFSmall with (env, _) in

    -- Apply full ANF
    let tANF = use HoleANFAll in normalizeTerm tANFSmall in

    -- Perform dependency analysis
    match
      if full then assumeFullDependency env tANF
      else
        -- Perform CFA
        let graphData = graphDataInit env in
        let cfaRes : CFAGraph = holeCfa graphData tANF in
        let cfaRes : CFAGraph = analyzeNested env cfaRes tANF in
        (analyzeDependency env cfaRes tANF, tANF)
    with (dep, ast) in

    -- Do instrumentation
    match instrument env dep ast with (instrumented, ast) in

    -- Context expansion
    match contextExpand env ast with (exp, ast) in

    -- Transformations should produce an AST that type checks
    let ast = typeCheck ast in

    -- Run pattern lowering
    let ast = lowerAll ast in

    -- Strip annotations before compiling
    let ast = stripTuneAnnotations ast in

    -- Compile the program
    let compileOCaml = lam libs. lam clibs. lam ocamlProg.
      let opt = {optimize = true, libraries = libs, cLibraries = clibs} in
      ocamlCompileWithConfig opt ocamlProg
    in
    let cunit: CompileResult = compileMCore ast (mkEmptyHooks compileOCaml) in

    -- Run the program
    let runner = lam input : String. lam timeoutMs : Option Float.
      let t1 = wallTimeMs () in
      let res: ExecResult = cunit.run "" [input] in
      let t2 = wallTimeMs () in
      (subf t2 t1, res)
    in

    -- Run tuning
    let cleanup = lam.
      exp.cleanup ();
      instrumented.cleanup ();
      cunit.cleanup ()
    in
    let res = _tuneDebug options runner env dep instrumented exp.tempFile cleanup exp.table ast in
    cleanup ();
    res
in

type TestResult = {
  finalTable : [Expr],
  nbrRuns : Int
} in

let eqTable = lam t1 : [Expr]. lam t2 : [Expr].
  use MExprEq in
  eqSeq eqExpr t1 t2
in

let eqTest = lam lhs: (LookupTable, Option SearchState). lam rhs : TestResult.
  match lhs with (lookupTable, searchState) in
  match searchState with None () then
    match rhs with {nbrRuns = 0} then true
    else error "fail"
  else match searchState with Some s in
  let s : SearchState = s in
  match s with {data = Some (TuneData {database = db})} then
  match db with Database {runs = runs, tables = tables} then

    let tableEq =
      if timeSensitive then
        eqTable lookupTable rhs.finalTable
      else true
    in

    let runsEq = eqi (length tables.data) rhs.nbrRuns in

    forAll (lam x. x) [
      tableEq,
      runsEq
    ]
  else error "expected database"
  else error "expected tune data"
in

let opt = {{tuneOptionsDefault with verbose = debug}
                               with printStats = debug} in

-- No holes
let t = parse
"
sleepMs 1
"
in

utest test debug false opt t with {
  finalTable = [],
  nbrRuns = 0
} using eqTest in

-- Empty search space due to reduction. Should do 0 runs and use the default
-- table.
let t = parse
"
let h = hole (IntRange {default = 1, min = 1, max = 3}) in
if eqi h 1 then () else sleepMs 100
"
in

let opt = {opt with method = Exhaustive ()} in

utest test debug false {opt with reduceDependencies = 200.} t with {
  finalTable = [int_ 1],
  nbrRuns = 0
} using eqTest in

-- One measuring point filtered out due to reduction.
let t = parse
"
let h1 = hole (IntRange {default = 1, min = 1, max = 3}) in
let m1 = if eqi h1 1 then 1 else 2 in
let h2 = hole (Boolean {default = true}) in
if h2 then sleepMs 100 else sleepMs 200
"
in

let opt = {opt with method = Exhaustive ()} in

utest test true false {opt with reduceDependencies = 20.} t with {
  finalTable = [int_ 1, true_],
  nbrRuns = 2
} using eqTest in

-- No measuring points for some holes
let t = parse
"
let h1 = hole (Boolean {default = true}) in
let h2 = hole (Boolean {default = true}) in
let m = if h2 then sleepMs 100 else sleepMs 0 in
m
" in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [true_, false_],
  nbrRuns = 2
} using eqTest in

-- No measuring points for any holes
let t = parse
"
let h = hole (Boolean {default = true}) in
h
" in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [true_],
  nbrRuns = 0
} using eqTest in


-- The three following tests check that each of the hole values (1, 2, and 3)
-- are found.
let t = parse
"
let h = hole (IntRange {default = 1, min = 1, max = 3}) in
if eqi h 1 then () else sleepMs 100
"
in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [int_ 1],
  nbrRuns = 3
} using eqTest in


let t = parse
"
let h = hole (IntRange {default = 1, min = 1, max = 3}) in
if eqi h 2 then () else sleepMs 100
"
in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [int_ 2],
  nbrRuns = 3
} using eqTest in


let t = parse
"
let h = hole (IntRange {default = 1, min = 1, max = 3}) in
if eqi h 3 then () else sleepMs 100
"
in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [int_ 3],
  nbrRuns = 3
} using eqTest in


-- Two holes, independent.
let t = parse
"
let h1 = hole (IntRange {default = 10, min = 10, max = 300}) in
let h2 = hole (IntRange {default = 10, min = 10, max = 300}) in
sleepMs h1;
sleepMs h2
"
in

let opt = {{tuneOptionsDefault with stepSize = 290}
                               with verbose = debug} in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [int_ 10, int_ 10],
  nbrRuns = 2
} using eqTest in

-- Three holes, partially dependent.
let t = parse
"
let h1 = hole (IntRange {default = 10, min = 10, max = 300}) in
let h2 = hole (IntRange {default = 10, min = 10, max = 300}) in
let h3 = hole (IntRange {default = 10, min = 10, max = 300}) in
sleepMs h1;
sleepMs (addi h2 h3)
"
in

let opt = {{tuneOptionsDefault with stepSize = 290}
                               with verbose = debug} in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [int_ 10, int_ 10, int_ 10],
  nbrRuns = 4
} using eqTest in

-- Four holes, example from the paper
let t = parse
"
let h1 = hole (Boolean {default = true}) in
let h2 = hole (Boolean {default = true}) in
let h3 = hole (Boolean {default = true}) in
let h4 = hole (Boolean {default = true}) in
let m1 =
  switch (h1, h2)
  case (false, false) then 700
  case (false, true) then 200
  case (true, false) then 300
  case (true, true) then 600
  end
in
let m2 =
  switch (h2, h3)
  case (false, false) then 500
  case (true, false) then 400
  case (false, true) then 600
  case (true, true) then 300
  end
in
let m3 =
  switch h4
  case false then 100
  case true then 200
  end
in
sleepMs m1;
sleepMs m2;
sleepMs m3
"
in

utest test debug false {opt with method = Exhaustive ()} t with {
  finalTable = [false_, true_, true_, false_],
  nbrRuns = 4
} using eqTest in

-- Input arguments
let t = parse
"
let h = hole (Boolean {default = true}) in
let a = get argv 1 in
if h then
  if eqi (length a) 3 then sleepMs 300
  else ()
else sleepMs 100
" in

utest test debug true {opt with args = ["arg"]} t with {
  finalTable = [false_],
  nbrRuns = 2
} using eqTest in

utest test debug true {opt with args = ["a"]} t with {
  finalTable = [true_],
  nbrRuns = 2
} using eqTest in

utest test debug true {opt with args = ["a","arg"]} t with {
  finalTable = [false_],
  nbrRuns = 2
} using eqTest in

-- No dependency analysis
let t = parse
"
let h = hole (Boolean {default = true}) in
if h then sleepMs 100 else ()
" in

utest test debug true opt t with {
  finalTable = [false_],
  nbrRuns = 2
} using eqTest in

-- Independence annotation
let t = parse
"
let h = hole (Boolean {default = true}) in
let hh = independent h h in
if hh then sleepMs 100 else ()
" in

utest test debug false opt t with {
  finalTable = [],
  nbrRuns = 0
} using eqTest in

()
