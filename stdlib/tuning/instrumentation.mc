-- input:
-- Map Name (Set (Name, Set Int))
-- Expr -> set of  (hole, set of contexts)

-- probably also prefix tree for producing switch statements

-- CallCtxEnv for id:s

-- TODO:
-- Log is an array with nbrMeasPoints elements
-- Each entry is a tuple (nbrCalls,totalTime) spent in that measuring point
-- The measuring points are indexed with offset nbrHoles (store offset in dep?)
-- In the end, the log is written to a file
-- The instrumentation returns both this file name and the instrumented program
-- Format of the file is CSV?
-- index,nbrCalls,totalTime
-- The tests should read the file and check some values

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
    match instrumentHeader (graph.nbrMeas, graph.offset)
    with (header, logName, funName) in
    let tempDir = sysTempDirMake () in
    let fileName = sysJoinPath tempDir ".profile" in
    match instrumentFooter fileName graph.offset with (footer, dumpToFile) in
    let expr = instrumentH env graph funName t in
    let ast =
      bindall_
      [ header
      , bindSemi_ (instrumentH env graph funName t) footer
      , app_ (nvar_ dumpToFile) (nvar_ logName)
      ]
    in
    --let ast = bindKeepLast_ (instrumentH env graph funName t) footer in
    let res = {fileName = fileName, cleanup = lam. sysTempDirDelete tempDir} in
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

-- TODO
-- read profile result
-- provide context and value in table

use TestLang in

let debug = true in

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

let test = lam debug. lam table. lam expr.
  debugPrintLn debug "\n-------- ORIGINAL PROGRAM --------";
  debugPrintLn debug (expr2str expr);

  -- Use small ANF first, needed for context expansion
  let tANFSmall = use MExprHoles in normalizeTerm expr in

  -- Do graph coloring to get context information (throw away the AST).
  match colorCallGraph [] tANFSmall with (env, _) in

  -- Initialize the graph data
  let graphData = graphDataFromEnv env in

  -- Apply full ANF
  let tANF = normalizeTerm tANFSmall in

  -- Perform CFA
  let cfaRes : CFAGraph = cfaData graphData tANF in

  -- Perform dependency analysis
  let dep : DependencyGraph = analyzeDependency env cfaRes tANF in

  -- Do instrumentation
  match instrument env dep expr with (res, ast) in
  debugPrintLn debug "\n-------- INSTRUMENTED PROGRAM --------";
  debugPrintLn debug (expr2str ast);
  debugPrintLn debug "";

  -- Context expansion with lookup table
  let ast = insert env table ast in
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

let resolvePoint = lam point : (String, [String]). lam graph : DependencyGraph.
  let strMap = mapFoldWithKey (lam acc. lam k : Name. lam v.
      mapInsert (nameGetStr k) v acc
    ) (mapEmpty cmpString) graph.measuringPoints
  in
  let tree = mapFindExn point.0 strMap in
  let binds : [(Int,[NameInfo])] = prefixTreeBindings tree in
  let strBinds = map (lam b : (Int, [NameInfo]).
    (map nameInfoGetStr b.1, b.0)
  ) binds in
  assocLookupOrElse {eq=eqSeq eqString}
    (lam. error (concat "Path missing: " (strJoin " " point.1)))
    point.1 strBinds
in

let eqTest = lam lhs. lam rhs : TestResult.
  match lhs with (log, env, graph) in
  let env : CallCtxEnv = env in
  let graph : DependencyGraph = graph in
  let res : [Bool] = map (
    lam d : {point : (String,[String]), nbrRuns : Int, totalTime : Float}.
      let id : Int = resolvePoint d.point graph in
      match mapLookup id log with Some (nbrRunsReal, totalTimeReal) then
        if eqi d.nbrRuns nbrRunsReal then
          if eqfApprox rhs.epsilon totalTimeReal d.totalTime then true
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
            ])
      else error (concat "Unknown id: " (int2string id))
  ) rhs.data
  in forAll (lam x. x) res
in

-- Global hole
let t = parse
"
let foo = lam x.
  let h = hole (IntRange {default = 1, min = 1, max = 1}) in
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

utest test debug [int_ 200, true_] t with {
  data = [ {point = ("a",[]), nbrRuns = 1, totalTime = 200.0}
         , {point = ("b",[]), nbrRuns = 1, totalTime = 200.0}
         , {point = ("c",[]), nbrRuns = 0, totalTime = 0.}
         ],
  epsilon = 10.0
}
using eqTest in

-- -- Context-sensitive, but only one context
-- let t = parse
-- "
-- let f1 = lam x.
--   let h = hole (Boolean {default = true, depth = 3}) in
--   let m = sleepMs h in
--   m
-- in
-- let f2 = lam x.
--   let a = f1 x in
--   a
-- in
-- let f3 = lam x. lam y.
--   let c = f2 x in
--   c
-- in
-- let f4 = lam x.
--   let d = f3 x 2 in
--   d
-- in
-- f4 ()
-- " in

-- utest test debug t with () in

-- -- Context-sensitive, several contexts
-- let t = parse
-- "
-- let f1 = lam x.
--   let h = hole (Boolean {default = true, depth = 2}) in
--   h
-- in
-- let f2 = lam x.
--   let a = f1 x in
--   let b = f1 x in
--   let c = addi a b in
--   let cc = sleepMs c in
--   c
-- in
-- let f3 = lam f.
--   f 1
-- in
-- let d = f2 1 in
-- let e = f2 1 in
-- let f = addi d e in
-- let g = sleepMs f in
-- let i = f3 f2 in
-- ()
-- " in

-- utest test debug t with () in

-- -- Context-sensitive, longer contexts
-- let t = parse
-- "
-- let f1 = lam x.
--   let h = hole (Boolean {default = true, depth = 3}) in
--   let m = sleepMs h in
--   m
-- in
-- let f2 = lam x.
--   let a = f1 x in
--   a
-- in
-- let f3 = lam x. lam y.
--   let c = f2 x in
--   c
-- in
-- let f4 = lam x.
--   let d = f3 x 2 in
--   let e = f3 x 2 in
--   d
-- in
-- f4 ()
-- " in

-- utest test debug t with () in

()
