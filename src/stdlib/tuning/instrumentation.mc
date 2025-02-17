-- Performs instrumentation of a program with holes.
--
-- The input is the call context environment and the dependency graph, and the
-- output is an instrumented program where each measuring point has been wrapped
-- in time measurements. Upon running the instrumented program, a CSV file with
-- the three columns 'id', 'nbrRuns', and 'totalMs' is outputted, where:
-- * 'id' is the identifier of the measuring points (as defined in dependency
-- * graph);
-- * 'nbrRuns' is the number of times the measuring point was executed; and
-- * 'totalMs' is the total time in ms spent in the measuring point.

include "ast.mc"
include "dependency-analysis.mc"
include "data-frame.mc"
include "tail-positions.mc"

include "common.mc"
include "set.mc"
include "sys.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/utils.mc"

type InstrumentedResult = {
  -- The filename to where the profiling data is written
  fileName : String,

  -- Cleanup function for removing all temporary files
  cleanup : () -> ()
}

let _instrumentationHeader = "id,nbrRuns,totalMs"

lang Instrumentation = MExprAst + HoleAst + TailPositions
  sem tailPositionBaseCase =
  | TmHole _ -> true
  | TmIndependent t ->
    tailPositionBaseCase t.lhs

  sem instrument (env : CallCtxEnv) (graph : DependencyGraph) =
  | t ->
    -- Create header
    match instrumentHeader (graph.nbrMeas, graph.offset)
    with (header, str2name) in
    -- Create footer
    let tempDir = sysTempDirMake () in
    let fileName = sysJoinPath tempDir ".profile" in
    match instrumentFooter fileName str2name graph.offset with (footer, dumpToFile) in
    -- Instrument the program
    let expr = instrumentH env graph str2name t in

    -- Put together the final AST
    let ast =
      bindall_
      [ header
      , bindSemi_ expr footer
      , appf2_ (nvar_ dumpToFile) (nvar_ (str2name "log")) (nvar_ (str2name "lock"))
      ]
    in
    let res = {fileName = fileName, cleanup = lam. sysTempDirDelete tempDir (); ()} in
    (res, ast)

  sem idExpr (info: Info) (ident: Name) (graph: DependencyGraph) (env: CallCtxEnv) (tree: PTree NameInfo) =
  | ids ->
    match ids with [id] then int_ id
    else match ids with [_] ++ _ then
      let incVarName = mapFindExn (mapFindExn ident graph.meas2fun) env.fun2inc in
      let lookup = lam i. int_ i in
      contextExpansionLookupCallCtx lookup tree incVarName env
    else errorSingle [info] "Measuring point without id"

  -- Recursive helper for instrument
  sem instrumentH (env : CallCtxEnv) (graph : DependencyGraph) (str2name : String -> Name) =
  | TmRecLets r ->
    let lets : [Name] = map (lam b: RecLetBinding. b.ident) r.bindings in
    match lets with [] then instrumentH env graph str2name r.inexpr
    else
      -- Identify a reclet by the ident of its first binding
      let reclet = head lets in
      -- Find the set of measuring points with a tail call within a reclet
      let acc: [Int] = [] in
      let ids: [Int] = [] in
      let baseCase = lam acc. lam ids. lam expr. expr in
      let tailCall = lam acc. lam ids. lam expr.
        if not (null ids) then
          -- Found a tail call within a measuring point
          (concat ids acc, expr)
        else (acc, expr)
      in
      let letexpr = lam ids. lam expr.
        -- Check if a let expression is a measuring point
        let ids =
          if not (null ids) then ids
          else
            match expr with TmLet t in
            match mapLookup t.ident graph.measuringPoints with Some tree then
              prefixTreeGetIds tree []
            else []
        in
        (ids, lam x. x)
      in
      match tailPositionsReclet baseCase tailCall letexpr ids acc (TmRecLets r) with
      (tailCalls, _) in
      let tailCallsSet = setOfSeq subi tailCalls in
      let tailCalls = setToSeq tailCallsSet in

      -- Instrument the reclet
      let acc = () in
      let ids = [] in
      let baseCase = lam. lam. lam expr.
        instrumentBaseCase tailCalls str2name expr
      in
      let tailCall = lam acc. lam ids. lam expr.
        -- Instrument a tail call: do nothing!
        (acc, expr)
      in
      let acquireLock = str2name "acquireLock" in
      let releaseLock = str2name "releaseLock" in
      let letexpr = lam ids. lam expr.
        -- Check if a let expression is a measuring point
        if not (null ids) then (ids, lam x. x) else
        match expr with TmLet t in
        match mapLookup t.ident graph.measuringPoints with Some tree then
          -- Found measuring point
          let ids = prefixTreeGetIds tree [] in
          let id = idExpr (infoTm expr) t.ident graph env tree ids in
          -- Contains a tail call?
          if setMem (head ids) tailCallsSet then
            -- Yes, acquire lock. The lock is released in a base case.
            (ids, lam e. bindSemi_ (app_ (nvar_ acquireLock) id) e)
          else
            -- No, acquire and release lock directly after.
            let f = lam e.
              match e with TmLet t in
              let expr = TmLet {t with inexpr = uunit_} in
              let i = nameSym "iid" in
              let semi = nameSym "" in
              bindall_
              [ nulet_ i id
              , nulet_ semi (app_ (nvar_ acquireLock) (nvar_ i))
              , expr
              , nulet_ semi (app_ (nvar_ releaseLock) (nvar_ i))
              , t.inexpr
              ]
            in (ids, f)
        else ([], lam x. x)
      in
      match tailPositionsReclet baseCase tailCall letexpr ids acc (TmRecLets r)
      with (_, TmRecLets r) in
      TmRecLets {r with inexpr = instrumentH env graph str2name r.inexpr}

  | TmLet t ->
    match mapLookup t.ident graph.measuringPoints with Some tree then
      let ids = prefixTreeGetIds tree [] in
      let expr = TmLet {t with inexpr = uunit_} in
      let id = idExpr (infoTm (TmLet t)) t.ident graph env tree ids in
      instrumentPoint env graph str2name expr t.inexpr id
    else smap_Expr_Expr (instrumentH env graph str2name) (TmLet t)
  | t -> smap_Expr_Expr (instrumentH env graph str2name) t


  sem instrumentBaseCase (ids: [Int]) (str2name: String -> Name) =
  | TmLet t ->
    -- Instrument a base case: Release locks of _all_ measuring points that
    -- have tail-recursive calls.
    let expr = TmLet {t with inexpr = uunit_} in
    let releaseExpr =
      if null ids then uunit_ else
      let releaseLock = str2name "releaseLock" in
      foldr1 bindSemi_ (map (lam id. app_ (nvar_ releaseLock) (int_ id)) ids)
    in
    let semi = nameSym "" in
    bindall_
    [ expr
    , nulet_ semi releaseExpr
    , t.inexpr
    ]

  -- Insert instrumentation code around a measuring point. Assumes that the
  -- point does not contain any tail calls.
  sem instrumentPoint (env : CallCtxEnv) (graph : DependencyGraph)
        (str2name : String -> Name) (expr : Expr) (inexpr : Expr) =
  | id ->
    let i = nameSym "iid" in
    let semi = nameSym "" in
    bindall_
    [ nulet_ i id
    , nulet_ semi (app_ (nvar_ (str2name "acquireLock")) (nvar_ i))
    , expr
    , nulet_ semi (app_ (nvar_ (str2name "releaseLock")) (nvar_ i))
    , instrumentH env graph str2name inexpr
    ]

  sem instrumentHeader =
  | (size, offset) ->
    let str = join
    [ "let log = tensorCreateDense [", int2string size, "] (lam is. (0, 0.0)) in\n"
    , "let s = tensorCreateDense [", int2string size, "] (lam is. 0.0) in\n"
    , "let lock = ref 0 in\n"
    , "let recordTime = lam id. lam s. lam e.
         let idx = subi id ", int2string offset, " in
         match tensorGetExn log [idx] with (nbrRuns, totalMs) in
         let res = (addi nbrRuns 1, addf totalMs (subf e s)) in
         tensorSetExn log [idx] res
       in\n"
    , "let acquireLock = lam id.
         if eqi (deref lock) 0 then
           let idx = subi id ", int2string offset, "in
           tensorSetExn s [idx] (wallTimeMs ());
           modref lock id
         else ()
       in\n"
    , "let releaseLock = lam id.
         if eqi (deref lock) id then
           let idx = subi id ", int2string offset, "in
           recordTime id (tensorGetExn s [idx]) (wallTimeMs ());
           modref lock 0
         else ()
       in\n"
    , "()\n"
    ] in
    let ex = use BootParser in parseMExprStringKeywordsExn [] str in
    let str2name = lam str.
      use MExprFindSym in
      match findName str ex with Some n then n
      else error (concat str " not found in instrumentation header")
    in
    let nameMap : Map String Name = mapFromSeq cmpString
      (map (lam str. (str, str2name str))
        [ "log"
        , "acquireLock"
        , "releaseLock"
        , "lock"
        ])
    in
    let lookupFun : String -> Name = lam str.
      match mapLookup str nameMap with Some n then n
      else error (concat str " not found in instrumentation header")
    in
    (ex, lookupFun)

  -- Write to file
  sem instrumentFooter (fileName : String) (str2name : String -> Name) =
  | offset ->
    let str = join
    [ "
      -- For displaying profiling data
      let int2string = lam n.
        recursive
        let int2string_rechelper = lam n.
          if lti n 10
          then [int2char (addi n (char2int '0'))]
          else
            let d = [int2char (addi (modi n 10) (char2int '0'))] in
            concat (int2string_rechelper (divi n 10)) d
        in
        if lti n 0
        then cons '-' (int2string_rechelper (negi n))
        else int2string_rechelper n
      in

      -- Join
      let join = lam seqs. foldl concat [] seqs in

      -- Tensor operations
      let _prod = foldl muli 1 in

      let linearToCartesianIndex = lam shape. lam k.
        let f = lam d. lam kidx.
          match kidx with (k, idx) then
            (divi k d, cons (modi k d) idx)
          else never
        in
        let r : (Int, [Int]) = foldr f (k, []) shape in
        r.1
      in

      let tensorSize : all a. Tensor[a] -> Int =
        lam t. _prod (tensorShape t)
      in

      let tensorFoldliSlice
        : all a. all b. (b -> Int -> Tensor[a] -> b) -> b -> Tensor[a] -> b =
        lam f. lam acc. lam t1.
        let accr = ref acc in
        tensorIterSlice
          (lam i. lam t.
            let acc = f (deref accr) i t in
            modref accr acc)
          t1;
        deref accr
      in

      let tensorFoldi : all a. all b. (b -> [Int] -> a -> b) -> b -> Tensor[a] -> b =
        lam f. lam acc. lam t.
        let shape = tensorShape t in
        let t = tensorReshapeExn t [tensorSize t] in
        tensorFoldliSlice
          (lam acc. lam i. lam t.
            f acc (linearToCartesianIndex shape i) (tensorGetExn t []))
          acc t
      in"
    , "-- Dump the log to file
      let dumpLog = lam log. lam lock.
        let str = \"", _instrumentationHeader, "\\n\" in
        let offset = ", int2string offset, " in\n"
    , " let str =
        tensorFoldi (lam acc. lam i. lam x.
          match x with (nbrRuns, totalMs) in
          match i with [i] in
          let acc = concat acc (join
            [ int2string (addi offset i), \",\"
            , int2string nbrRuns, \",\"
            , float2string totalMs, \",\"
            ])
          in
          concat acc \"\\n\"
        ) str log
        in
        -- Check that the 'lock' variable is freed
        (if neqi (deref lock) 0 then error (concat (\"WARN: lock is not free \") (int2string (deref lock)))
         else ());
        writeFile \"", fileName, "\" (concat str \"\\n\")
      in"
    , "()\n"
    ] in
    let ex = use BootParser in parseMExprStringKeywordsExn [] str in
    let fun = use MExprFindSym in
      match findName "dumpLog" ex with Some n then n else error "impossible" in
    (ex, fun)

  -- Reads the profiled result after the instrumented program has been run.
  type InstrumentationProfile = {ids: [Int], nbrRuns: [Int], totalMs: [Float]}
  sem readProfile =
  | str ->
    let rows = strSplit "\n" (strTrim str) in
    let header = head rows in
    if eqString header _instrumentationHeader then
      let df = foldl (lam acc. lam r.
        let r = strSplit "," r in
        dataFrameAddRow r acc
      ) (dataFrameFromSeq [] 4) (tail rows)
      in
      { ids = map (lam x. string2int (head x)) (dataFrameSlice [0] df)
      , nbrRuns = map (lam x. string2int (head x)) (dataFrameSlice [1] df)
      , totalMs = map (lam x. string2float (head x)) (dataFrameSlice [2] df)
      }
    else error (join [ "Mismatch in expected and actual header of profile: \n"
                     , "got ", header
                     , "expected ", _instrumentationHeader
                     ])

end

lang TestLang = Instrumentation + GraphColoring + MExprHoleCFA + ContextExpand +
                NestedMeasuringPoints + DependencyAnalysis +
                BootParser + MExprSym + MExprPrettyPrint + MExprANFAll +
                MExprEval + MExprTypeCheck
end

mexpr

use TestLang in

let debug = false in
let epsilon = 20.0 in
let epsilonEnabled = false in

let debugPrintLn = lam debug.
  if debug then printLn else lam. ()
in

let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in

type TestResult = {
  data : [{ point : (String,[String]),
            nbrRuns : Int,
            totalMs : Float
          }],
  epsilon : Float
} in

let resolveId
  : all k. (String, [String]) -> Map k (PTree NameInfo) -> (k -> String) -> Int =
  lam point : (String, [String]). lam m : Map k (PTree NameInfo). lam keyToStr : k -> String.
    let strMap = mapFoldWithKey (lam acc. lam k : k. lam v.
        mapInsert (keyToStr k) v acc
      ) (mapEmpty cmpString) m
    in
    let tree = mapFindExn point.0 strMap in
    let binds : [(Int,[NameInfo])] = prefixTreeBindings tree in
    let strBinds = map (lam b : (Int, [NameInfo]).
      (map nameInfoGetStr b.1, b.0)
    ) binds in
    assocLookupOrElse {eq=eqSeq eqString}
      (lam. error (concat "Path missing: " (strJoin " " point.1)))
      (reverse point.1) strBinds
in

let test = lam debug. lam full: Bool. lam table : [((String,[String]),Expr)]. lam expr.
  debugPrintLn debug "\n-------- ORIGINAL PROGRAM --------";
  debugPrintLn debug (expr2str expr);

  -- Use small ANF first, needed for context expansion
  let tANFSmall = use MExprHoles in normalizeTerm expr in

  -- Do graph coloring to get context information
  match colorCallGraph [] tANFSmall with (env, ast) in

  -- Initialize the graph data
  let graphData = graphDataInit env in
  debugPrintLn debug "\n-------- COLORED PROGRAM --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Apply full ANF
  let tANF = normalizeTerm ast in
  debugPrintLn debug "\n-------- ANF --------";
  debugPrintLn debug (expr2str tANF);
  debugPrintLn debug "";

  -- Perform CFA
  let cfaRes : CFAGraph = holeCfa graphData tANF in

  -- Analyze nested
  let cfaRes : CFAGraph = analyzeNested env cfaRes tANF in

  -- Perform dependency analysis
  match
    if full then assumeFullDependency env tANF
    else (analyzeDependency env cfaRes tANF, tANF)
  with (dep, ast) in

  -- Do instrumentation
  match instrument env dep ast with (res, ast) in
  debugPrintLn debug "\n-------- INSTRUMENTED PROGRAM --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Context expansion with lookup table
  let tableMap : Map Int Expr = foldl (
    lam acc. lam t : ((String,[String]),Expr).
      let id = resolveId t.0 env.contexts nameInfoGetStr in
      let intExpr = int_ (toInt t.1 (get env.idx2hole id)) in
      mapInsert id intExpr acc
    ) (mapEmpty subi) table in
  let lookupTable = mapValues tableMap in
  let ast = insert env lookupTable ast in
  debugPrintLn debug "\n-------- CONTEXT EXPANSION --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Transformations should produce an AST that type checks
  let ast = symbolize ast in
  let ast = typeCheck ast in

  -- Evaluate the program
  eval (evalCtxEmpty ()) ast;

  -- Read the profiled data
  let logStr = readFile res.fileName in
  debugPrintLn debug "\n-------- LOGGED RESULTS --------";
  debugPrintLn debug logStr;
  debugPrintLn debug "";

  -- Return the log as a map
  match readProfile logStr
  with {ids = ids, nbrRuns = ns, totalMs = totalS} in
  let log : Map Int (Int, Float) = foldl (lam acc. lam i.
      let id = get ids i in
      let runsS = get ns i in
      let totalS = get totalS i in
      mapInsert id (runsS,totalS) acc
    ) (mapEmpty subi) (create (length ids) (lam i. i))
  in

  -- Clean up temporary files
  res.cleanup ();

  (log, env, dep)
in

let eqTest = lam lhs. lam rhs : TestResult.
  match lhs with (log, env, graph) in
  let env : CallCtxEnv = env in
  let graph : DependencyGraph = graph in
  let res : [Bool] = map (
    lam d : {point : (String,[String]), nbrRuns : Int, totalMs : Float}.
      let id : Int = resolveId d.point graph.measuringPoints nameGetStr in
      match mapLookup id log with Some (nbrRunsReal, totalMsReal) then
        if eqi d.nbrRuns nbrRunsReal then
          if not epsilonEnabled then true else
          -- Allow one epsilon of error for each run
          let margin = mulf (int2float nbrRunsReal) rhs.epsilon in
          if eqfApprox margin totalMsReal d.totalMs then true
          else error (join
          [ "Total time mismatch: got "
          , float2string totalMsReal, " (self) and "
          , ", expected "
          , float2string d.totalMs, " (self) and "
          ]
          )
        else
          error (join
            [ "Number of runs do not match: got "
            , int2string nbrRunsReal, " runs"
            , ", expected ", int2string d.nbrRuns
            , " for id ", int2string id
            , " with name ", d.point.0
            , " and path ", strJoin " " d.point.1
            ])
      else error (concat "Unknown id: " (int2string id))
  ) rhs.data
  in forAll (lam x. x) res
in

-- Global hole
let t = parse
"
let foo = lam x.
  let h = hole (IntRange {default = 200, min = 1, max = 200}) in
  let a = sleepMs h in
  let b = sleepMs h in
  (a,b)
in
let bar = lam x. lam y.
  let h1 = hole (Boolean {default = true}) in
  let c = if h1 then 1 else 2 in
  c
in
foo ()
" in

utest test debug false [(("h", []), int_ 50), (("h1", []), true_)] t with {
  data = [ {point = ("a",[]), nbrRuns = 1, totalMs = 50.0}
         , {point = ("b",[]), nbrRuns = 1, totalMs = 50.0}
         , {point = ("c",[]), nbrRuns = 0, totalMs = 0.}
         ],
  epsilon = epsilon
}
using eqTest in

-- Tail calls
let t = parse
"
let h = hole (IntRange {default = 0, min = 0, max = 10}) in
recursive
let g = lam x.
  f x 1
let f = lam x. lam y.
  let fMatch =
    if eqi x 0 then 0
    else f (subi x 1) y
  in fMatch
let silly = lam x.
  let sillyMatch =
    if eqi x 42 then silly x
    else true
  in sillyMatch
let fakeRecursive = lam x.
  let fakeMatch =
    if eqi x 0 then baseCase 10
    else if eqi x 2 then baseCase 30
    else baseCase 100
  in
  fakeMatch
let baseCase = lam x.
  sleepMs x
in
f h 1;
g h;
silly h;
fakeRecursive h
" in

utest test debug false [(("h", []), int_ 2)] t with {
  data = [ {point = ("fMatch",[]), nbrRuns = 2, totalMs = 0.0}
         , {point = ("sillyMatch",[]), nbrRuns = 1, totalMs = 0.0}
         , {point = ("fakeMatch",[]), nbrRuns = 1, totalMs = 30.0}
         ],
  epsilon = epsilon
}
using eqTest in

-- Tail calls with nested reclets
let t = parse
"
let h = hole (IntRange {default = 0, min = 0, max = 10}) in
recursive
let f = lam x. lam y.
  recursive let inner = lam x.
    let matchInner =
      if eqi x 42 then inner 1
      -- Will not be seen as a tail-recursive call
      else if eqi x 43 then f 1 2
      else sleepMs 10; 2
    in matchInner
  in
  inner x;
  let matchF =
    if eqi x 0 then 0
    else
      sleepMs 20;
      f (subi x 1) y
  in
  matchF
in
f h 1
" in

utest test debug false [(("h", []), int_ 2)] t with {
  data = [ -- (20 + 10) + (20 + 10) + 10
           {point = ("matchF",[]), nbrRuns =3, totalMs= 70.}
           -- Has only one run because the other two are nested within matchF
         , {point = ("matchInner",[]), nbrRuns =1, totalMs = 10.}
         ],
  epsilon = epsilon
}
using eqTest in

-- Recursive let followed by other stuff
let t = parse
"
let h = hole (Boolean {default = true}) in
recursive let f = lam x. x
in
let m = if h then sleepMs 25 else () in
()
" in

utest test debug false [(("h", []), true_)] t with {
  data = [ {point = ("m",[]), nbrRuns =1, totalMs= 25.}
         ],
  epsilon = epsilon
}
using eqTest in

-- Context-sensitive, but only one context
let t = parse
"
let f1 = lam x.
  let h = hole (IntRange {default = 200, min = 1, max = 200, depth = 3}) in
  let m = sleepMs h in
  m
in
let f2 = lam x.
  let a = f1 x in
  a
in
let f3 = lam x. lam y.
  let c = f2 x in
  c
in
let f4 = lam x.
  let d = f3 x 2 in
  d
in
f4 ()
" in

utest test debug false [(("h", ["d", "c", "a"]), int_ 40)] t with {
  data = [ {point = ("m", ["d", "c", "a"]), nbrRuns = 1, totalMs = 40.0} ],
  epsilon = epsilon
}
using eqTest in

-- Context-sensitive, several contexts
let t = parse
"
let f1 = lam x.
  let h = hole (IntRange {default = 300, min = 1, max = 500, depth = 2}) in
  h
in
let f2 = lam x.
  let a = f1 x in
  let b = f1 x in
  let c = addi a b in
  let cc = sleepMs c in
  c
in
let f3 = lam f.
  f 1
in
let f4 = lam.
  let d = f2 1 in
  let e = f2 1 in
  let f = addi d e in
  let g = sleepMs f in
  ()
in
let f5 = lam.
  let i = f2 1 in
  i
in
f4 ();
f5 ();
f5 ()
" in

let table =
[ ( ("h", ["d","a"]), int_ 20)
, ( ("h", ["d","b"]), int_ 40)
, ( ("h", ["e","a"]), int_ 60)
, ( ("h", ["e","b"]), int_ 80)
, ( ("h", ["i","a"]), int_ 30)
, ( ("h", ["i","b"]), int_ 50)
]
in
utest test debug false table t with {
  data =
  [ {point = ("cc", ["d"]), nbrRuns = 1, totalMs = 60.0}
  , {point = ("cc", ["e"]), nbrRuns = 1, totalMs = 140.0}
  , {point = ("cc", ["i"]), nbrRuns = 2, totalMs = 160.0}
  , {point = ("g", []), nbrRuns = 1, totalMs = 200.0}
  ],
  epsilon = epsilon
} using eqTest in


-- Context-sensitive, longer contexts
let t = parse
"
let f1 = lam x.
  let h = hole (IntRange {default = 0, depth = 3, min = 0, max = 40}) in
  let m = sleepMs h in
  m
in
let f2 = lam x.
  let a = f1 x in
  a
in
let f3 = lam x. lam y.
  let c = f2 x in
  c
in
let f4 = lam x.
  let d = f3 x 2 in
  d
in
let f5 = lam x.
  let e = f3 x 2 in
  e
in
f4 ();
f4 ();
f5 ()
" in

let table =
[ ( ("h", ["d","c","a"]), int_ 30 )
, ( ("h", ["e","c","a"]), int_ 40 )
] in
utest test debug false table t with {
  data =
  [ {point = ("m", ["d", "c", "a"]), nbrRuns = 2, totalMs = 60.0}
  , {point = ("m", ["e", "c", "a"]), nbrRuns = 1, totalMs = 40.0}
  ],
  epsilon = epsilon
} using eqTest in

-- Tests with full dependency
let t = parse
"
let f1 = lam x.
  let h = hole (IntRange {default = 0, depth = 2, min = 0, max = 100}) in
  h
in
let f2 = lam x.
  let a = f1 x in
  let b = f1 x in
  let c = addi a b in
  let cc = sleepMs c in
  c
in
let f3 = lam f.
  f 1
in
let d = f2 1 in
let e = f2 1 in
let f = addi d e in
let g = sleepMs f in
()
" in

let table =
[ ( ("h", ["d","a"]), int_ 20)
, ( ("h", ["d","b"]), int_ 20)
, ( ("h", ["e","a"]), int_ 20)
, ( ("h", ["e","b"]), int_ 20)
] in
utest test debug true table t with {
  data =
  [ {point = ("m", []), nbrRuns = 1, totalMs = 160.0} ],
  -- Use larger epsilon since total execution time is measured
  epsilon = mulf 3.0 epsilon
} using eqTest in


-- Nested points
let t = parse
"
let f1 = lam x.
  let h1 = hole (IntRange {default = 1, min = 0, max = 500}) in
  let m0 = sleepMs h1 in
  ()
in
let h2 = hole (Boolean {default = true}) in
let m1 = if h2 then f1 () else () in
f1 ()
" in

let table =
[ ( ("h1", []), int_ 200)
, ( ("h2", []), true_)
] in
utest test debug false table t with {
  data =
  [ {point = ("m1", []), nbrRuns = 1, totalMs = 200.0}
  , {point = ("m0", []), nbrRuns = 1, totalMs = 200.0}
  ],
  epsilon = epsilon
} using eqTest in


-- Recursive function without tail calls
let t = parse
"
recursive let foo = lam x.
  let h = hole (IntRange {default = 100, min = 1, max = 200}) in
  let m1 = sleepMs h in
  let y = addi x 1 in
  sleepMs 100;
  let m2 = sleepMs h in
  let m3 = if eqi h 0 then sleepMs 100 else () in
  if eqi x 3 then x else foo y
in

foo 1
" in

let table =
[ ( ("h", []), int_ 100 )
] in
utest test debug false table t with {
  data =
  [ {point = ("m1", []), nbrRuns = 3, totalMs = 300.0}
  , {point = ("m2", []), nbrRuns = 3, totalMs = 300.0}
  , {point = ("m3", []), nbrRuns = 3, totalMs = 0.0}
  ],
  epsilon = epsilon
} using eqTest in


-- Tail call, but not within a measuring point
let t = parse
"
recursive let foo = lam x.
  let h = hole (IntRange {default = 100, min = 1, max = 200}) in
  let m1 = sleepMs h in
  let y = addi x 1 in
  sleepMs 100;
  let m2 = if eqi x h then 1 else foo y in
  m2
in

foo 98
" in

let table =
[ ( ("h", []), int_ 100 )
] in
utest test debug false table t with {
  data =
  [ {point = ("m1", []), nbrRuns = 1, totalMs = 100.0}
  , {point = ("m2", []), nbrRuns = 1, totalMs = 400.0}
  ],
  epsilon = epsilon
} using eqTest in


-- Mutual recursion
let t = parse
"
recursive
  let bar = lam x.
    let m1 = if x then foo x else 2 in
    m1
  let foo = lam x.
    let m2 = if x then 1 else 2 in
    m2
in
let h = hole (Boolean {default = true}) in
bar h;
foo h
" in

let table =
[ ( ("h", []), true_ )
] in
utest test debug false table t with {
  data =
  [ {point = ("m1", []), nbrRuns = 1, totalMs = 0.0}
  , {point = ("m2", []), nbrRuns = 1, totalMs = 0.0}
  ],
  epsilon = epsilon
} using eqTest in

()
