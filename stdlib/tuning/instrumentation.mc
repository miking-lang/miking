-- input:
-- Map Name (Set (Name, Set Int))
-- Expr -> set of  (hole, set of contexts)

-- probably also prefix tree for producing switch statements

-- CallCtxEnv for id:s

include "ast.mc"
include "dependency-analysis.mc"

include "common.mc"
include "set.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"
include "mexpr/keyword-maker.mc"

let _instrumentationHeaderStr =
"
let log = ref [] in
let record = lam id. lam startTime. lam endTime.
  modref log (cons (id,startTime,endTime) (deref log))
in
()
"

let _instrumentationHeader =
  use BootParser in
  parseMExprString [] _instrumentationHeaderStr

let _instrumentationLogName =
  match findName "log" _instrumentationHeader with Some n then n
  else error "impossible"

let _instrumentationRecordName =
  match findName "record" _instrumentationHeader with Some n then n
  else error "impossible"

lang Instrumentation = LetAst
  sem instrumentH (env : CallCtxEnv) (graph : DependencyGraph) (expr : Expr)
                  (inexpr : Expr) =
  | idExpr ->
    let startName = nameSym "s" in
    let endName = nameSym "e" in
    bindall_
    [ nulet_ startName (wallTimeMs_ uunit_)
    , expr
    , nulet_ endName (wallTimeMs_ uunit_)
    , nulet_ (nameSym "") (
        appf3_ (nvar_ _instrumentationRecordName) idExpr
          (nvar_ startName) (nvar_ endName))
    , instrument env graph inexpr
    ]

  sem instrument (env : CallCtxEnv) (graph : DependencyGraph) =
  | TmLet ({ident = ident} & t) ->
    match mapLookup ident graph.measuringPoints with Some tree then
      let ids = prefixTreeGetIds tree [] in
      let expr = TmLet {t with inexpr = uunit_} in
      -- One or several contexts?
      match ids with [id] then
        instrumentH env graph expr t.inexpr (int_ id)
      else match ids with [_] ++ _ in
        let incVarName = mapFindExn (mapFindExn ident graph.meas2fun) env.fun2inc in
        let lookup = lam i. int_ i in
        let idExpr = contextExpansionLookupCallCtx lookup tree incVarName env in
        instrumentH env graph expr t.inexpr idExpr
    else smap_Expr_Expr (instrument env graph) (TmLet t)
  | t -> smap_Expr_Expr (instrument env graph) t

end

lang TestLang = Instrumentation + GraphColoring + MExprHoleCFA +
                DependencyAnalysis + BootParser + MExprSym + MExprPrettyPrint

mexpr

use TestLang in

let debug = false in

let debugPrintLn = lam debug.
  if debug then printLn else lam x. x
in

let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

let test = lam debug. lam expr.
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
  let res = instrument env dep expr in
  debugPrintLn debug "\n-------- INSTRUMENTED PROGRAM --------";
  debugPrintLn debug (expr2str res);
  debugPrintLn debug "";
  ()
in

-- Global hole
let t = parse
"
let foo = lam x.
  let h = hole (Boolean {default = true}) in
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

utest test debug t with () in

-- Context-sensitive, but only one context
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
f4 ()
" in

utest test debug t with () in

-- Context-sensitive, several contexts
let t = parse
"
let f1 = lam x.
  let h = hole (Boolean {default = true, depth = 2}) in
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
let i = f3 f2 in
()
" in

utest test debug t with () in

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
  let e = f3 x 2 in
  d
in
f4 ()
" in

utest test debug t with () in

()
