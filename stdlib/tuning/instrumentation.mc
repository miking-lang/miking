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

include "common.mc"
include "set.mc"
include "sys.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"

type InstrumentedResult = {
  -- The filename to where the profiling data is written
  fileName : String,

  -- Cleanup function for removing temporary all files
  cleanup : Unit -> Unit
}

lang Instrumentation = LetAst
  sem instrument (env : CallCtxEnv) (graph : DependencyGraph) =
  | t ->
    -- Create header
    match instrumentHeader (graph.nbrMeas, graph.offset)
    with (header, logName, funName) in
    -- Create footer
    let tempDir = sysTempDirMake () in
    let fileName = sysJoinPath tempDir ".profile" in
    match instrumentFooter fileName graph.offset with (footer, dumpToFile) in
    -- Instrument the program
    let expr = instrumentH env graph funName t in

    -- Put together the final AST
    let ast =
      bindall_
      [ header
      , bindSemi_ expr footer
      , app_ (nvar_ dumpToFile) (nvar_ logName)
      ]
    in
    let res = {fileName = fileName, cleanup = sysTempDirDelete tempDir} in
    (res, ast)

  -- Recursive helper for instrument
  sem instrumentH (env : CallCtxEnv) (graph : DependencyGraph) (funName : Name) =
  | TmLet ({ident = ident} & t) ->
    match mapLookup ident graph.measuringPoints with Some tree then
      let ids = prefixTreeGetIds tree [] in
      let expr = TmLet {t with inexpr = uunit_} in
      -- One or several contexts?
      match ids with [id] then
        instrumentPoint env graph funName expr t.inexpr (int_ id)
      else match ids with [_] ++ _ in
        let incVarName = mapFindExn (mapFindExn ident graph.meas2fun) env.fun2inc in
        let lookup = lam i. int_ i in
        let idExpr = contextExpansionLookupCallCtx lookup tree incVarName env in
        instrumentPoint env graph funName expr t.inexpr idExpr
    else smap_Expr_Expr (instrumentH env graph funName) (TmLet t)
  | t -> smap_Expr_Expr (instrumentH env graph funName) t

  -- Insert instrumentation code around a measuring point
  sem instrumentPoint (env : CallCtxEnv) (graph : DependencyGraph)
        (funName : Name) (expr : Expr) (inexpr : Expr) =
  | idExpr ->
    let startName = nameSym "s" in
    let endName = nameSym "e" in
    bindall_
    [ nulet_ startName (wallTimeMs_ uunit_)
    , expr
    , nulet_ endName (wallTimeMs_ uunit_)
    , nulet_ (nameSym "") (
        appf3_ (nvar_ funName) idExpr
          (nvar_ startName) (nvar_ endName))
    , instrumentH env graph funName inexpr
    ]

  sem instrumentHeader =
  | (size, offset) ->
    let str = join
    [ "let log = tensorCreateDense [", int2string size, "] (lam is. (0, 0.0)) in\n"
    , "let record = lam id. lam startTime. lam endTime.\n"
    , "  let idx = subi id ", int2string offset, "in \n"
    , "  match tensorGetExn log [idx] with (nbrRuns, totalTime) in\n"
    , "  tensorSetExn log [idx] (addi nbrRuns 1, addf totalTime (subf endTime startTime))\n"
    , "in ()\n"
    ] in
    let ex = use BootParser in parseMExprString [] str in
    let log = match findName "log" ex with Some n then n else "impossible" in
    let fun = match findName "record" ex with Some n then n else "impossible" in
    (ex, log, fun)

  -- Write to file
  sem instrumentFooter (fileName : String) =
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
      let linearToCartesianIndex = lam shape. lam k.
        let f = lam d. lam kidx.
          match kidx with (k, idx) then
            (divi k d, cons (modi k d) idx)
          else never
        in
        let r : (Int, [Int]) = foldr f (k, []) shape in
        r.1
      in

      let tensorSize : Tensor[a] -> Int =
        lam t. foldl muli 1 (tensorShape t)
      in

      let tensorFoldliSlice
        : (b -> Int -> Tensor[a] -> b) -> b -> Tensor[a] -> b =
        lam f. lam acc. lam t1.
        let accr = ref acc in
        tensorIterSlice
          (lam i. lam t.
            let acc = f (deref accr) i t in
            modref accr acc)
          t1;
        deref accr
      in

      let tensorFoldi : (b -> [Int] -> a -> b) -> b -> Tensor[a] -> b =
        lam f. lam acc. lam t.
        let shape = tensorShape t in
        let t = tensorReshapeExn t [tensorSize t] in
        tensorFoldliSlice
          (lam acc. lam i. lam t.
            f acc (linearToCartesianIndex shape i) (tensorGetExn t []))
          acc t
      in

      -- Dump the log to file
      let dumpLog = lam log.
        let str = \"id,nbrRuns,totalMs\\n\" in
        let offset = ", int2string offset, " in\n"
    , " let str =
        tensorFoldi (lam acc. lam i. lam x.
          match x with (nbrRuns, totalTime) in
          match i with [i] in
          let acc = concat acc (join
            [ int2string (addi offset i), \",\"
            , int2string nbrRuns, \",\"
            , float2string totalTime
            ])
          in
          concat acc \"\\n\"
        ) str log
        in
        writeFile \"", fileName, "\" (concat str \"\\n\")"
    , "in ()\n"
    ] in
    let ex = use BootParser in parseMExprString [] str in
    let fun = match findName "dumpLog" ex with Some n then n else "impossible" in
    (ex, fun)


end

lang TestLang = Instrumentation + GraphColoring + MExprHoleCFA + ContextExpand +
                DependencyAnalysis + BootParser + MExprSym + MExprPrettyPrint +
                MExprEval

mexpr

use TestLang in

let debug = false in
let epsilon = 10.0 in

let debugPrintLn = lam debug.
  if debug then printLn else lam x. x
in

let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

type TestResult = {
  data : [{point : (String,[String]), nbrRuns : Int, totalTime : Float}],
  epsilon : Float
} in

let resolveId =
  lam point : (String, [String]). lam m : Map k (PTree NameInfo). lam keyToStr : k -> String.
    let strMap = mapFoldWithKey (lam acc. lam k : Name. lam v.
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

let test = lam debug. lam table : [((String,[String]),Expr)]. lam expr.
  debugPrintLn debug "\n-------- ORIGINAL PROGRAM --------";
  debugPrintLn debug (expr2str expr);

  -- Use small ANF first, needed for context expansion
  let tANFSmall = use MExprHoles in normalizeTerm expr in

  -- Do graph coloring to get context information
  match colorCallGraph [] tANFSmall with (env, ast) in

  -- Initialize the graph data
  let graphData = graphDataFromEnv env in
  debugPrintLn debug "\n-------- COLORED PROGRAM --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Apply full ANF
  let tANF = normalizeTerm ast in
  debugPrintLn debug "\n-------- ANF --------";
  debugPrintLn debug (expr2str tANF);
  debugPrintLn debug "";

  -- Perform CFA
  let cfaRes : CFAGraph = cfaData graphData tANF in

  -- Perform dependency analysis
  let dep : DependencyGraph = analyzeDependency env cfaRes tANF in

  -- Do instrumentation
  match instrument env dep tANF with (res, ast) in
  debugPrintLn debug "\n-------- INSTRUMENTED PROGRAM --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Context expansion with lookup table
  let tableMap : Map Int Expr = foldl (
    lam acc. lam t : ((String,[String]),Expr).
      let id = resolveId t.0 env.contexts nameInfoGetStr in
      mapInsert id t.1 acc
    ) (mapEmpty subi) table in
  let lookupTable = mapValues tableMap in
  let ast = insert env lookupTable ast in
  debugPrintLn debug "\n-------- CONTEXT EXPANSION --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Evaluate the program
  eval { env = mapEmpty nameCmp } ast;

  -- Read the profiled data
  let logStr = readFile res.fileName in
  debugPrintLn debug "\n-------- LOGGED RESULTS --------";
  debugPrintLn debug logStr;
  debugPrintLn debug "";

  -- Return the log as a map
  let rows = tail (strSplit "\n" logStr) in
  let log : Map Int (Int,Float) = foldl (
    lam acc. lam row.
      match row with "" then acc
      else match strSplit "," row with [id,nbrRuns,totalMs] then
        mapInsert (string2int id) (string2int nbrRuns, string2float totalMs) acc
      else error (concat "Unexpectedly formatted row: " row)
    ) (mapEmpty subi) rows
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
    lam d : {point : (String,[String]), nbrRuns : Int, totalTime : Float}.
      let id : Int = resolveId d.point graph.measuringPoints nameGetStr in
      match mapLookup id log with Some (nbrRunsReal, totalTimeReal) then
        if eqi d.nbrRuns nbrRunsReal then
          -- Allow one epsilon of error for each run
          let margin = mulf (int2float nbrRunsReal) rhs.epsilon in
          if eqfApprox margin totalTimeReal d.totalTime then true
          else error (join
          [ "Total time mismatch: got ", float2string totalTimeReal
          , ", expected ", float2string d.totalTime
          ]
          )
        else
          error (join
            [ "Number of runs do not match: got ", int2string nbrRunsReal
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

utest test debug [(("h", []), int_ 50), (("h1", []), true_)] t with {
  data = [ {point = ("a",[]), nbrRuns = 1, totalTime = 50.0}
         , {point = ("b",[]), nbrRuns = 1, totalTime = 50.0}
         , {point = ("c",[]), nbrRuns = 0, totalTime = 0.}
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

utest test debug [(("h", ["d", "c", "a"]), int_ 40)] t with {
  data = [ {point = ("m", ["d", "c", "a"]), nbrRuns = 1, totalTime = 40.0} ],
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
utest test debug table t with {
  data =
  [ {point = ("cc", ["d"]), nbrRuns = 1, totalTime = 60.0}
  , {point = ("cc", ["e"]), nbrRuns = 1, totalTime = 140.0}
  , {point = ("cc", ["i"]), nbrRuns = 2, totalTime = 160.0}
  , {point = ("g", []), nbrRuns = 1, totalTime = 200.0}
  ],
  epsilon = epsilon
} using eqTest in


-- Context-sensitive, longer contexts
let t = parse
"
let f1 = lam x.
  let h = hole (Boolean {default = true, depth = 3}) in
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
utest test debug table t with {
  data =
  [ {point = ("m", ["d", "c", "a"]), nbrRuns = 2, totalTime = 60.0}
  , {point = ("m", ["e", "c", "a"]), nbrRuns = 1, totalTime = 40.0}
  ],
  epsilon = epsilon
} using eqTest in

()
