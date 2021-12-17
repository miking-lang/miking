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
    -- TODO: handle case when hole is on top level. check fun2hole
    let body =
      if eqi depth 0 then
        lookup (callCtxHole2Idx (ident, t.info) [] env)
      else
        -- print "env = "; dprintLn env;
        -- dprintLn (mapBindings env.hole2fun);
        -- print "key = "; dprintLn ident;
        let funDefined = callCtxHole2Fun (ident, t.info) env in
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

lang HolesPrettyPrint = MExprHoles + MExprPrettyPrint

lang TestLang = BootParser + HolesPrettyPrint + MExprEq

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

-- TODO: rewrite tests to parse a string
-- write a test with top-level statement

let debug = false in
let parse = lam str.
  let ast = parseMExprString holeKeywords str in
  let ast = makeKeywords [] ast in
  symbolize ast
in

let debugPrint = lam ast. lam pub.
  if debug then
    printLn "----- BEFORE ANF -----\n";
    printLn (expr2str ast);
    let ast = anf ast in
    printLn "\n----- AFTER ANF -----\n";
    printLn (expr2str ast);
    match colorCallGraph pub ast with (env, ast) in
    match contextExpand env ast with {ast = ast} in
    printLn "\n----- AFTER TRANSFORMATION -----\n";
    printLn (expr2str ast);
    ()
  else ()
in

-- let funA = lam.
--   let h = hole 0 2 in
--   h
-- in
-- let funB = lam x. lam y.
--   if x then
--      (if y then
--         funB z false
--       else funA y)
--   else funA y
-- in
-- let funC = lam x. funB x false
-- in ()
let funA = nameSym "funA" in
let funB = nameSym "funB" in
let funC = nameSym "funC" in
let funD = nameSym "funD" in
let callBA1 = nameSym "callBA1" in
let callBA2 = nameSym "callBA2" in
let callBB = nameSym "callBB" in
let callCB = nameSym "callCB" in
let h = nameSym "h" in
let ast = bindall_ [ nulet_ funA (ulam_ ""
                        (bind_ (nulet_ h (holeIntRange_ (int_ 0) 2 0 1))
                               (nvar_ h)))
                    , nureclets_add funB
                        (ulam_ "xB"
                          (ulam_ "y" (if_ (var_ "xB")
                                          (if_ (var_ "y")
                                               (bind_ (nulet_ callBB (appf2_ (nvar_ funB) true_ false_))
                                                      (nvar_ callBB))
                                               (bind_ (nulet_ callBA1 (app_ (nvar_ funA) (var_ "xB")))
                                                      (nvar_ callBA1)))
                                          (bind_ (nulet_ callBA2 (app_ (nvar_ funA) (var_ "y")))
                                                 (nvar_ callBA2)))))
                        reclets_empty
                    , nulet_ funC (ulam_ "xC"
                        (bind_ (nulet_ callCB (appf2_ (nvar_ funB) (var_ "xC") false_))
                               (nvar_ callCB)))
                   ]
in
debugPrint ast [(funB, NoInfo ()), (funC, NoInfo ())];
let ast = anf ast in

match colorCallGraph [(funB, NoInfo ()), (funC, NoInfo ())] ast with (env, ast) in
match contextExpand env ast with
  {ast = flatAst, table = table, tempFile = tempFile, cleanup = cleanup, env = env}
in

let dumpTable = lam table : LookupTable.
  use MExprPrettyPrint in
  let rows = mapi (lam i. lam expr.
    join [int2string i, ": ", expr2str expr]) table in
  let rows = cons (int2string (length table)) rows in
  let str = strJoin "\n" (concat rows ["="]) in
  writeFile tempFile str
in

let evalWithTable = lam table : LookupTable. lam ast : Expr. lam ext : Expr.
  let astExt = bind_ ast ext in
  dumpTable table;
  (if debug then
     printLn "\n----- AFTER TEST TRANSFORMATION -----\n";
     printLn (expr2str astExt)
   else ());
  use MExprEval in
  eval { env = mapEmpty nameCmp } astExt
in

let idxs = mapi (lam i. lam. i) table in
let table = mapi (lam i. lam. int_ (addi 1 i)) idxs in
let insertedAst = insert env table ast in

let eval = evalWithTable table in

-- Path 1: B (1)-> A
let extAst = appf2_ (nvar_ funB) true_ false_ in
utest eval flatAst extAst with int_ 1 using eqExpr in
utest eval insertedAst extAst with int_ 1 using eqExpr in

-- Path 2: B -> B (1)-> A
let extAst = appf2_ (nvar_ funB) true_ true_ in
utest eval flatAst extAst with int_ 2 using eqExpr in
utest eval insertedAst extAst with int_ 2 using eqExpr in

-- Path 3: C -> B (1)-> A
let extAst = app_ (nvar_ funC) true_ in
utest eval flatAst extAst with int_ 3 using eqExpr in
utest eval insertedAst extAst with int_ 3 using eqExpr in

-- Path 6: C -> B (2)-> A
let extAst = app_ (nvar_ funC) false_ in
utest eval flatAst extAst with int_ 6 using eqExpr in
utest eval insertedAst extAst with int_ 6 using eqExpr in

-- Path 4: B (2)-> A
let extAst = appf2_ (nvar_ funB) false_ false_ in
utest eval flatAst extAst with int_ 4 using eqExpr in
utest eval insertedAst extAst with int_ 4 using eqExpr in

-- Path 4 again
let extAst = bind_
  (nulet_ (nameSym "") (app_ (nvar_ funC) false_))
  (appf2_ (nvar_ funB) false_ false_) in
utest eval flatAst extAst with int_ 4 using eqExpr in
utest eval insertedAst extAst with int_ 4 using eqExpr in

-- Path 5: B -> B (2)-> A
-- unreachable

cleanup ()
