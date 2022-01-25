include "mexpr/mexpr.mc"
include "mexpr/pprint.mc"
include "mexpr/eq.mc"
include "mexpr/utesttrans.mc"
include "mexpr/anf.mc"
include "mexpr/ast-builder.mc"

include "sys.mc"
include "digraph.mc"

include "graph-coloring.mc"

-- Implements context expansion for a program with holes.

type LookupTable = [Expr]

type ContextExpanded =
{ ast : Expr             -- The context-expanded AST
, table : LookupTable    -- The initial lookup table
, tempDir : String       -- The temporary directory
, tempFile : String      -- The file from which hole values are read
, cleanup : Unit -> Unit -- Removes all temporary files from the disk
, env : CallCtxEnv       -- Call context environment
}

-- Generate code for looking up a value of a hole depending on its call history
let _lookupCallCtx
  : (Int -> Expr) -> NameInfo -> Name -> CallCtxEnv -> Expr =
  lam lookup. lam holeId. lam incVarName. lam env : CallCtxEnv.
    use MExprAst in
    let tree : PTree NameInfo = mapFindExn holeId env.contexts in
    recursive let work : NameInfo -> [PTree NameInfo] -> [NameInfo] -> Expr =
      lam incVarName. lam children. lam acc.
        let children = mapValues children in
        match children with [] then never_
        else
          let tmpName = nameSym "tmp" in
          let branches = foldl (lam cases: ([Expr], [Expr]). lam c.
            match c with Leaf _ then
              (cons (lookup (callCtxHole2Idx holeId acc env)) cases.0, cases.1)
            else match c with Node {root = root, children = cs} then
              let root : NameInfo = root in
              let iv = callCtxLbl2Inc root.0 env in
              let count = callCtxLbl2Count root.0 env in
              let branch =
                  (matchex_ (nvar_ tmpName) (pint_ count)
                            (work iv cs (cons root acc)))
              in (cases.0, cons branch cases.1)
            else never
          ) ([], []) children in
          switch branches
          case (([def], []) | ([], [TmMatch {thn = def}])) then def
          case (defaultCase, matches) then
            let default = switch defaultCase
              case [] then never_
              case [default] then default
              case _ then error "expected at most one default case"
              end
            in
            bind_
              (nulet_ tmpName (callCtxReadIncomingVar incVarName env))
              (matchall_ (snoc matches default))
          end
    in
    match tree with Node {children = children} then
      let res = work incVarName children [] in
      res
    else error "sentinel node missing"

-- Fragment for transforming a program with holes.
lang ContextExpand = HoleAst
  -- 'contextExpand public t' eliminates all holes in the expression 't' and and
  --  replace them by lookups in a static table.
  sem contextExpand (env : CallCtxEnv) =
  | t ->
    let lookup = lam i. tensorGetExn_ tyunknown_ (nvar_ _table) (seq_ [int_ i]) in
    let ast = _contextExpandWithLookup env lookup t in
    let tempDir = sysTempDirMake () in
    let tuneFile = sysJoinPath tempDir ".tune" in
    let ast = _wrapReadFile env tuneFile ast in
    { ast = ast
    , table = _initAssignments env
    , tempDir = tempDir
    , tempFile = tuneFile
    , cleanup = sysTempDirDelete tempDir
    , env = env
    }

  -- 'insert public table t' replaces the holes in expression 't' by the values
  -- in 'table'
  sem insert (env : CallCtxEnv) (table : LookupTable) =
  | t -> _contextExpandWithLookup env (lam i. get table i) t

  sem _contextExpandWithLookup (env : CallCtxEnv) (lookup : Int -> Expr) =
  -- Hole: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
    let lookupGlobal = lam info.
      lookup (callCtxHole2Idx (ident, info) [] env)
    in
    let body =
      if eqi depth 0 then lookupGlobal t.info
      else
        let funDefined = callCtxHole2Fun (ident, t.info) env in
        if nameInfoEq funDefined callGraphTop then
          -- Context-sensitive hole on top-level: handle as a global hole
          lookupGlobal t.info
        else
          let iv = callCtxFun2Inc funDefined.0 env in
          let res = _lookupCallCtx lookup (ident, t.info) iv env in
          res
    in TmLet {{t with body = body}
                 with inexpr = _contextExpandWithLookup env lookup t.inexpr}

  | tm ->
    smap_Expr_Expr (_contextExpandWithLookup env lookup) tm

  -- Find the initial mapping from holes to values
  sem _initAssignments =
  | env ->
    let env : CallCtxEnv = env in
    map (lam h. default h) env.idx2hole

  sem _wrapReadFile (env : CallCtxEnv) (tuneFile : String) =
  | tm ->
    use BootParser in
    let impl = parseMExprString [] "
    let or: Bool -> Bool -> Bool =
      lam a. lam b. if a then true else b in

    let zipWith = lam f. lam seq1. lam seq2.
      recursive let work = lam a. lam s1. lam s2.
        if or (null s1) (null s2) then a
        else
          work (snoc a (f (head s1) (head s2))) (tail s1) (tail s2)
        in
        work [] seq1 seq2
    in

    let eqSeq = lam eq : (a -> b -> Bool). lam s1 : [a]. lam s2 : [b].
      recursive let work = lam s1. lam s2.
        match (s1, s2) with ([h1] ++ t1, [h2] ++ t2) then
          if eq h1 h2 then work t1 t2
          else false
        else true
      in
      let n1 = length s1 in
      let n2 = length s2 in
      let ndiff = subi n1 n2 in
      if eqi ndiff 0 then work s1 s2
      else false
    in

    let eqString = eqSeq eqc in

    let join = lam seqs. foldl concat [] seqs in

    let eqStringSlice = lam s1. lam s2. lam o2. lam n2.
      recursive let work = lam i.
        if eqi i n2 then true
        else if eqc (get s1 i) (get s2 (addi o2 i)) then work (addi i 1)
        else false
      in
      if eqi (length s1) n2 then
      work 0
      else false
    in

    -- Splits s on delim
    let strSplit = lam delim. lam s.
      let n = length s in
      let m = length delim in
      recursive let work = lam acc. lam lastMatch. lam i.
        if lti (subi n m) i then
          snoc acc (subsequence s lastMatch n)
        else if eqStringSlice delim s i m then
          let nexti = addi i m in
          work (snoc acc (subsequence s lastMatch (subi i lastMatch))) nexti nexti
        else
          work acc lastMatch (addi i 1)
      in
      if null delim then [s]
      else work [] 0 0
    in

    let string2bool = lam s : String.
      match s with \"true\" then true
      else match s with \"false\" then false
      else error (join [\"Cannot be converted to Bool: \'\", s, \"\'\"])
    in

    recursive let any = lam p. lam seq.
      if null seq
      then false
      else if p (head seq) then true else any p (tail seq)
    in

    let isWhitespace = lam c. any (eqc c) [' ', '\n', '\t', '\r'] in

    let strTrim = lam s.
      recursive
      let strTrim_init = lam s.
        if null s then s
        else if isWhitespace (head s)
        then strTrim_init (tail s)
        else s
      in reverse (strTrim_init (reverse (strTrim_init s)))
    in

    let string2int = lam s.
      recursive
      let string2int_rechelper = lam s.
        let len = length s in
        let last = subi len 1 in
        if eqi len 0
        then 0
        else
          let lsd = subi (char2int (get s last)) (char2int '0') in
          let rest = muli 10 (string2int_rechelper (subsequence s 0 last)) in
          addi rest lsd
      in
      match s with [] then 0 else
      if eqc '-' (head s)
      then negi (string2int_rechelper (tail s))
      else string2int_rechelper s
    in

    let seq2Tensor = lam seq.
      let t = tensorCreateDense [length seq] (lam is. get seq (get is 0)) in
      t
    in

    ()
    " in

    use MExprSym in
    let impl = symbolize impl in

    let getName : String -> Expr -> Name = lam s. lam expr.
      match findName s expr with Some n then n
      else error (concat "not found: " s) in

    let zipWithName = getName "zipWith" impl in
    let string2boolName = getName "string2bool" impl in
    let string2intName = getName "string2int" impl in
    let strSplitName = getName "strSplit" impl in
    let strTrimName = getName "strTrim" impl in
    let seq2TensorName = getName "seq2Tensor" impl in

    let convertFuns = map (lam h.
      match h with TmHole {ty = TyBool _} then string2boolName
      else match h with TmHole {ty = TyInt _} then string2intName
      else error "Unsupported type"
    ) env.idx2hole in

    let x = nameSym "x" in
    let y = nameSym "y" in
    let doConvert = nulam_ x (nulam_ y (app_ (nvar_ x) (nvar_ y))) in

    let fileContent = nameSym "fileContent" in
    let strVals = nameSym "strVals" in
    let i = nameSym "i" in
    let p = nameSym "p" in
    let nbr = nameSym "n" in
    bindall_
    [ impl
    -- Parse tune file
    , nulet_ fileContent (readFile_ (str_ tuneFile))
    , nulet_ strVals (appf2_ (nvar_ strSplitName) (str_ "\n")
        (app_ (nvar_ strTrimName) (nvar_ fileContent)))
    , nulet_ nbr (app_ (nvar_ string2intName) (head_ (nvar_ strVals)))
    , nulet_ strVals (subsequence_ (nvar_ strVals) (int_ 1) (nvar_ nbr))
    , let x = nameSym "x" in
      nulet_ strVals (map_ (nulam_ x
        (get_ (appf2_ (nvar_ strSplitName) (str_ ": ") (nvar_ x)) (int_ 1)))
        (nvar_ strVals))
    -- Convert strings into values
    , nulet_ _table
      (appf3_ (nvar_ zipWithName) doConvert
        (seq_ (map nvar_ convertFuns)) (nvar_ strVals))
    -- Convert table into a tensor (for constant-time lookups)
    , nulet_ _table (app_ (nvar_ seq2TensorName) (nvar_ _table))
    , tm
    ]
end

lang MExprHoles = HoleAst + GraphColoring + ContextExpand + MExprSym + MExprANF
end

lang HolesPrettyPrint = MExprHoles + MExprPrettyPrint
end

lang TestLang = BootParser + HolesPrettyPrint + MExprEq
end

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

let debug = false in
let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

--let test : Bool -> Expr -> Map String (Map [String] Expr) -> Expr =
let test : Bool -> Expr -> [( String, [( [String], Expr )] )] -> Expr =
  lam debug: Bool. lam ast: Expr. lam lookupMap: Map String (Map [String] Expr).
    (if debug then
       printLn "-------- BEFORE ANF --------";
       printLn (expr2str ast)
     else ());

    -- Do the analysis
    let ast = anf ast in
    (if debug then
       printLn "-------- AFTER ANF --------";
       printLn (expr2str ast)
     else ());
    match colorCallGraph [] ast with (env, ast) in
    let res = contextExpand env ast in
    (if debug then
       printLn "-------- AFTER CONTEXT EXPANSION --------";
       printLn (expr2str res.ast)
     else ());

    -- Convert map to lookup table, use default for no value provided
    let lookupMap : [(String, Map [String] Expr)] = map (lam t : (String, [([String],Expr)]).
      (t.0, mapFromSeq (seqCmp cmpString) t.1)) lookupMap in
    let lookupMap : Map String (Map [String] Expr) = mapFromSeq cmpString lookupMap in

    let lookupTable : Map Int Expr =
      mapFoldWithKey (lam acc: Map Int Expr. lam name: NameInfo. lam pathMap: Map [NameInfo] Int.
        match mapLookup (nameInfoGetStr name) lookupMap with Some strMap then
          mapFoldWithKey (lam acc: Map Int Expr. lam path: [NameInfo]. lam i: Int.
            let strPath = map nameInfoGetStr path in
            match mapLookup strPath strMap with Some expr then
              mapInsert i expr acc
            else acc
          ) acc pathMap
        else acc)
      (mapFromSeq subi (mapi (lam i. lam e. (i,e)) res.table))
      env.hole2idx
    in
    let lookupTable : LookupTable = mapValues lookupTable in

    -- Evaluate the program using the lookup table
    let dumpTable = lam table : LookupTable.
      use MExprPrettyPrint in
      let rows = mapi (lam i. lam expr.
        join [int2string i, ": ", expr2str expr]) table in
      let rows = cons (int2string (length table)) rows in
      let str = strJoin "\n" (concat rows ["="]) in
      writeFile res.tempFile str
    in
    dumpTable lookupTable;
    use MExprEval in
    let s = expr2str (eval { env = mapEmpty nameCmp } res.ast) in

    -- Clean up and return result
    res.cleanup ();
    s
in

let trimWhiteSpace = lam s.
  filter (compose not isWhitespace) s
in

utest trimWhiteSpace " \n s  a\t" with "sa" in

let eqTest = lam str1. lam str2.
  eqString (trimWhiteSpace str1) (trimWhiteSpace str2)
in

-- Global hole
let t = parse
"
let f = lam.
  let h = hole (Boolean {default = true}) in
  h
in
f ()
" in

utest test debug t [("h", [([], false_)])] with "false" using eqTest in


-- Context-sensitive hole
let t = parse
"
let a = lam.
  let h = hole (IntRange {default = 0, min = 0, max = 1, depth = 2}) in
  h
in
recursive let b = lam x. lam y.
  if x then
    if y then
      let l1 = b true false in l1
    else
      let l2 = a y in l2
  else
    let l3 = a y in l3
in
let c = lam x.
  let l4 = b x false in l4
in
[ let l5 = b true false in l5
, let l6 = b true true in l6
, let l7 = c true in l7
, let l8 = c false in l8
, let l9 = b false false in l9
]
" in

utest test debug t
[ ("h", [ (["l5", "l2"], int_ 1)
        , (["l1", "l2"], int_ 2)
        , (["l4", "l2"], int_ 3)
        , (["l4", "l3"], int_ 4)
        , (["l9", "l3"], int_ 5)
        ])
]
with "[1,2,3,4,5]" using eqTest in


-- Top-level context-sensitive hole
let t = parse
"
let h = hole (Boolean {default = true, depth = 1}) in
h
" in

utest test debug t
[ ("h", [ ([], false_) ])

] with "false" using eqTest in


-- Indirect function call. For now, the context of the latest call will be
-- assumed.
let t = parse
"
let f = lam x.
  let h = hole (IntRange {depth = 1, default = 10, min = 0, max = 10}) in
  addi x h
in
let a = f 1 in
map f [1,2,3]
" in

utest test debug t
[ ("h", [ (["a"], int_ 1) ]) ]
with "[2,3,4]" using eqTest in

()
