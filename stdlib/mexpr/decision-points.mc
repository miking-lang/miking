include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"
include "anf.mc"
include "name.mc"

-- This file contains implementations related to decision points. In particular,
-- it implements:
-- * A language fragment for decision points (HoleAst)
-- * An algorithm for AST -> call graph conversion (Ast2CallGraph fragment)
-- * Program transformations for programs with decision points (HolyCallGraph)

let _top = nameSym "top"

let _projName = nameSym "x"
let _head = lam s. get_ s (int_ 0)
let _tail = lam s. ntupleproj_ _projName 1 (splitat_ s (int_ 1))
let _null = lam s. eqi_ (int_ 0) (length_ s)

let _drecordproj = use MExprAst in
  lam key. lam r.
  nrecordproj_ _projName key r

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

let _getSym = lam n.
  (optionGetOrElse
    (lam. error "Expected symbol")
    (nameGetSym n))

lang HoleAst
  syn Expr =
  | TmHole {startGuess : Expr,
            depth : Int}

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmHole h -> TmHole h

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmHole h -> acc
end

lang HolePrettyPrint = HoleAst + TypePrettyPrint
  sem isAtomic =
  | TmHole _ -> false

  sem pprintCode (indent : Int) (env : SymEnv) =
  | TmHole h ->
    match pprintCode indent env h.startGuess with (env1, startStr) then
      match pprintCode indent env1 h.depth with (env2, depthStr) then
        (env2,
           join ["Hole (", strJoin ", " [startStr, depthStr],")"])
      else never
    else never
end

lang HoleANF = HoleAst + ANF
  sem isValue =
  | TmHole _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmHole {startGuess = startGuess, depth = depth} ->
    k (TmHole {startGuess = normalizeTerm startGuess, depth = depth})
end

let hole_ = use HoleAst in
  lam startGuess. lam depth.
  TmHole {startGuess = startGuess, depth = depth}

-- Create a call graph from an AST.
-- * Vertices (identifier names) are functions f defined as: let f = lam. ...
-- * There is an edge between f1 and f2 iff f1 calls f2: let f1 = lam. ... (f2 a)
-- * "top" is the top of the graph (i.e., no incoming edges)

type CallGraph = DiGraph Name Symbol

let _handleLetVertex = use LamAst in
  lam letexpr. lam f.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

let _handleLetEdge = use LamAst in
  lam letexpr. lam f. lam g. lam prev.
    match letexpr.body with TmLam lm
    then f g letexpr.ident lm.body
    else f g prev letexpr.body

let _handleApps = use AppAst in use VarAst in
  lam id. lam f. lam prev. lam g. lam app.
    recursive let appHelper = lam g. lam app.
      match app with TmApp {lhs = TmVar v, rhs = rhs} then
        let resLhs =
          if digraphHasVertex v.ident g then
            digraphAddEdge prev v.ident id g
          else g
        in f resLhs prev rhs
      else match app with TmApp ({lhs = TmApp a, rhs = rhs}) then
        let resLhs = appHelper g (TmApp a) in
        f resLhs prev rhs
      else match app with TmApp a then
        f (f g prev a.lhs) prev a.rhs
      else never
  in appHelper g app

-- Complexity (I think): O(|V|*|F|), as we visit each node exactly once and each
-- time potentially perform a graph union operation, which we assume has
-- complexity O(|F|). V is the set of nodes in the AST and F is the set of nodes
-- in the call graph (i.e. set of functions in the AST).
lang Ast2CallGraph = LetAst + LamAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex _top (digraphEmpty _eqn eqsym) in
    let g = digraphAddVertices (_findVertices arg) gempty in
    _findEdges g _top arg

  sem _findVertices =
  | TmLet t ->
    let res_body = _handleLetVertex t _findVertices
    in concat res_body (_findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam a. lam b. concat a (_handleLetVertex b _findVertices))
            [] t.bindings
    in concat res (_findVertices t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr _findVertices tm)

  sem _findEdges (cg : CallGraph) (prev : Name) =
  | TmLet ({body = TmApp a} & t) ->
    let id = _getSym t.ident in
    let resBody = _handleApps id _findEdges prev cg t.body in
    _findEdges resBody prev t.inexpr

  | TmLet ({body = TmLam lm} & t) ->
    let resBody = _findEdges cg t.ident lm.body in
    _findEdges resBody prev t.inexpr

  | TmRecLets t ->
    let res =
      foldl (lam g. lam b. digraphUnion g (_handleLetEdge b _findEdges g prev))
            cg t.bindings
    in _findEdges res prev t.inexpr

  | tm ->
    sfold_Expr_Expr digraphUnion cg (smap_Expr_Expr (_findEdges cg prev) tm)
end

-- Variable names to be used in transformed program
let _callCtx = nameSym "callCtx"
let _lookupTable = nameSym "lookupTable"
let _lookup = nameSym "lookup"
let _maxDepth = nameSym "maxDepth"
let _addCall = nameSym "addCall"
let _filter = nameSym "filter"
let _max = nameSym "max"
let _isPrefix = nameSym "isPrefix"
let _isSuffix = nameSym "isSuffix"

let _handleAppsCallCtx = use AppAst in use VarAst in
  lam f. lam p. lam id. lam prev. lam app.
    recursive let appHelper = lam app.
      match app with TmApp {lhs = TmVar v, rhs = rhs} then
        if p v.ident then
          let isRecCall = _eqn prev v.ident in
          let newCallCtx =
            if isRecCall then (nvar_ _callCtx)
            else appf2_ (nvar_ _addCall) (nvar_ _callCtx) id
          in
          app_ (app_ (TmVar v) newCallCtx)
               (f p prev rhs)
        else app
      else match app with TmApp {lhs = TmApp a, rhs = rhs} then
        let resLhs = appHelper (TmApp a) in
        app_ resLhs (f p prev rhs)
      else match app with TmApp a then
        app_ (f p prev a.lhs) (f p prev a.rhs)
      else never
    in appHelper app

lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + SymbAst
  sem transform (publicFns : [Name]) =
  | tm ->
    let callGraph = toCallGraph tm in

    -- Check if identifier is a function in the call graph
    let isVertex = lam ident.
      optionIsSome (find (_eqn ident) (digraphVertices callGraph)) in

    -- Check if identifier is a public function
    let isPublic = lam ident.
      optionIsSome (find (_eqn ident) publicFns) in

    -- Renaming function for public functions
    let renamePub = lam ident.
      let nameStr = nameGetStr ident in
      let newNameStr = concat nameStr "Pr" in
      nameNoSym newNameStr in

    -- Replacer function for public functions
    let makePubDummy = lam funName. lam tm.
      recursive let work = lam tm. lam acc.
        match tm with TmLam t then
          TmLam {t with body=work t.body (snoc acc t.ident)}
        else
          foldl
            (lam a. lam x. app_ a (nvar_ x))
            (app_ (nvar_ (renamePub funName))
            (nvar_ _callCtx)) acc
      in work tm []
    in
    -- Extract dummy functions from the AST, to replace public functions
    let dummies = _extract isPublic makePubDummy tm in
    let defDummies = match dummies with [] then unit_ else bindall_ dummies in

    -- Transform program to use call context
    let trans = _transformCallCtx isVertex _top tm in

    -- Rename public functions
    let transRenamed = _renameIdents isPublic renamePub trans in

    -- Define initial call context
    let defCallCtx = nulet_ _callCtx (seq_ []) in

    -- Define initial lookup table
    let lookupTable = _initLookupTable (cons _top publicFns) callGraph tm in
    -- AST-ify the lookup table
    let defLookupTable =
      nulet_ _lookupTable
        (seq_ (map (lam r. record_ [("id", r.id), ("path", seq_ (map symb_ r.path)), ("value", r.value)]) lookupTable))
    in

    -- Compute maximum depth of the decision points
    let maxDepth =
      match lookupTable with [] then 0
      else
        maxOrElse (lam. error "Expected non-empty lookup table")
                  subi
                  (map (lam r. length r.path) lookupTable)
    in
    let defMaxDepth = nulet_ _maxDepth (int_ maxDepth) in

    -- AST-ify filter
    -- recursive let filter = lam p. lam s.
    --   if (eqi 0 (length s)) then []
    --   else if p (head s) then
    --     let f = filter p (tail s)
    --     in cons (head s) f
    --   else (filter p (tail s))
    -- in
    let filter =
      -- Local variables
      let p = nameSym "p" in
      let s = nameSym "s" in
      let f = nameSym "f" in
      nureclets_add _filter
        (nulam_ p (nulam_ s
          (if_ (_null (nvar_ s))
               (seq_ [])
               (if_ (app_ (nvar_ p) (_head (nvar_ s)))
                    (bind_ (nulet_ f (appf2_ (nvar_ _filter) (nvar_ p) (_tail (nvar_ s))))
                           (cons_ (_head (nvar_ s)) (nvar_ f)))
                    (appf2_ (nvar_ _filter) (nvar_ p) (_tail (nvar_ s)))))))
      reclets_empty
    in

    -- AST-ify max (for a non-empty list)
    -- nlet max = lam cmp. lam seq.
    --   recursive let work = lam e. lam seq.
    --     if null seq then e
    --     else
    --       let h = head seq in
    --       let t = tail seq in
    --       if lti h e then work e t else work h t
    --    in
    --    work (head seq) (tail seq)
    let max =
      let cmp = nameSym "cmp" in
      let seq = nameSym "seq" in
      let work = nameSym "work" in
      let e = nameSym "e" in
      let h = nameNoSym "h" in
      let t = nameNoSym "t" in
      nulet_ _max
        (nulam_ cmp (
          (nulam_ seq
          (bindall_ [(nureclets_add work
                       (nulam_ e (nulam_ seq
                         (if_ (_null (nvar_ seq))
                           (nvar_ e)
                           (bindall_ [nulet_ h (_head (nvar_ seq)),
                                      nulet_ t (_tail (nvar_ seq)),
                                      if_ (lti_ (appf2_ (nvar_ cmp) (nvar_ h) (nvar_ e)) (int_ 0))
                                          (appf2_ (nvar_ work) (nvar_ e) (nvar_ t))
                                          (appf2_ (nvar_ work) (nvar_ h) (nvar_ t))]) )))
                     reclets_empty),
                     appf2_ (nvar_ work) (_head (nvar_ seq)) (_tail (nvar_ seq))]))))
    in

    -- AST-ify isPrefix
    -- recursive let isPrefix = lam eq. lam s1. lam s2.
    --   if null s1 then true
    --   else if null s2 then false
    --   else if (eq (head s1) (head s2)) then (isPrefix eq (tail s1) (tail s2))
    --   else false
    -- in
    let isPrefix =
      let eq = nameSym "eq" in
      let s1 = nameSym "s1" in
      let s2 = nameSym "s2" in
      nureclets_add _isPrefix (
      (nulam_ eq (nulam_ s1 (nulam_ s2
        (if_ (_null (nvar_ s1))
             (true_)
             (if_ (_null (nvar_ s2))
                  (false_)
                  (if_ (appf2_ (nvar_ eq) (_head (nvar_ s1)) (_head (nvar_ s2)))
                       (appf3_ (nvar_ _isPrefix) (nvar_ eq) (_tail (nvar_ s1)) (_tail (nvar_ s2)) )
                       (false_))) )))))
      reclets_empty
    in

    -- AST-ify isSuffix
    -- let isSuffix = lam eq. lam s1. lam s2.
    --     isPrefix eq (reverse s1) (reverse s2)
    -- in
    let isSuffix =
      let eq = nameSym "eq" in
      let s1 = nameSym "s1" in
      let s2 = nameSym "s2" in
      nulet_ _isSuffix
        (nulam_ eq (nulam_ s1 (nulam_ s2
          (appf3_ (nvar_ _isPrefix)
                  (nvar_ eq)
                  (reverse_ (nvar_ s1))
                  (reverse_ (nvar_ s2)))))) in

    -- Lookup the value for a decision point in a given call context
    -- let lookup = lam callCtx. lam id.
    --   let entries = filter (lam t. eqsym t.0 id) lookupTable in
    --   let entriesSuffix = filter (lam t. isSuffix eqi t.1 callCtx) entries in
    --   let cmp = lam t1. lam t2. subi (length t1.1) (length t2.1) in
    --   max cmp entriesSuffix
    -- in
    let lookup =
      let id = nameSym "id" in
      let entries = nameSym "entries" in
      let entriesSuffix = nameSym "entriesSuffix" in
      let entriesLongestSuffix = nameSym "entriesLongestSuffix" in
      let eqsym = nameSym "eqsym" in
      let cmp = nameSym "cmp" in
      let y = nameSym "y" in
      let t = nameSym "t" in
      let x = nameSym "x" in
      let t1 = nameSym "t1" in
      let t2 = nameSym "t2" in
      nulet_ _lookup
        (nulam_ _callCtx (nulam_ id
        (bindall_ [
          nulet_ entries (
              appf2_ (nvar_ _filter)
                     (nulam_ t (eqsym_ (nvar_ id) (_drecordproj "id" (nvar_ t))))
                     (nvar_ _lookupTable)),
          nulet_ eqsym (nulam_ x (nulam_ y (eqsym_ (nvar_ x) (nvar_ y)))),
          nulet_ entriesSuffix
               (appf2_ (nvar_ _filter)
                       (nulam_ t (appf3_ (nvar_ _isSuffix) (nvar_ eqsym) (_drecordproj "path" (nvar_ t)) (nvar_ _callCtx)))
                       (nvar_ entries)),
          nulet_ cmp
            (nulam_ t1 (nulam_ t2
              (subi_
                 (length_ (_drecordproj "path" (nvar_ t1)))
                 (length_ (_drecordproj "path" (nvar_ t2)))))),
          nulet_ entriesLongestSuffix (appf2_ (nvar_ _max) (nvar_ cmp) (nvar_ entriesSuffix)),
          _drecordproj "value" (nvar_ entriesLongestSuffix)])))
    in
    let defLookup = bindall_ [isPrefix, isSuffix, max, filter, lookup] in

    -- Add a function call to the call context:
    -- let addCall = lam callCtx. lam lbl.
    --   if gti (length callCtx) maxDepth then
    --     snoc (tail callCtx) lbl
    --   else
    --     snoc callCtx lbl
    let defAddCall =
      let lbl = nameSym "lbl" in
      nulet_ _addCall (
        nulam_ _callCtx (nulam_ lbl (
          if_ (eqi_ (nvar_ _maxDepth) (int_ 0)) (nvar_ _callCtx)
            (if_ (lti_ (length_ (nvar_ _callCtx)) (nvar_ _maxDepth))
              (snoc_ (nvar_ _callCtx) (nvar_ lbl))
              (snoc_ (_tail (nvar_ _callCtx)) (nvar_ lbl))) )))
    in

    -- Put all the pieces together
    bindall_ [defLookupTable,
              defCallCtx,
              defMaxDepth,
              defAddCall,
              defLookup,
              defDummies,
              transRenamed]

  -- Extract expressions from the body of identifiers using extractor.
  -- Consider identifier for which p is true.
  sem _extract (p : String -> Bool)
              (extractor : String -> Expr -> Expr) =
  | TmLet ({body = TmLam lm} & t) ->
    let res =
      if p t.ident then
        let newBody = extractor t.ident t.body in
        [TmLet {{t with body = newBody} with inexpr=unit_}]
      else []
    in concat res (_extract p extractor t.inexpr)

  | TmRecLets t ->
    let handleLet = lam le.
      if p le.ident then
        match le.body with TmLam lm then
          let newBody = extractor le.ident le.body in
          [{le with body=newBody}]
        else
          error (strJoin "" ["Expected identifier ",
                             le.ident,
                             " to define a lambda."])
      else []
    in
    let binds =
      foldl (lam acc. lam b. concat acc (handleLet b)) [] t.bindings
    in concat [TmRecLets {{t with inexpr=unit_} with bindings=binds}]
              (_extract p extractor t.inexpr)

  | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (_extract p extractor) tm)

  -- Rename identifiers for which p is true, with renaming function rf
  sem _renameIdents (p : String -> Bool) (rf : String -> String) =
  | TmLet ({body = TmLam lm} & t) ->
    let newIdent =
      if p t.ident then
        rf t.ident
      else
        t.ident
    in TmLet {{{t with ident = newIdent}
                with body = _renameIdents p rf t.body}
                with inexpr = _renameIdents p rf t.inexpr}

  | TmRecLets t ->
    let handleLet = lam le.
      -- Defines a public function
      if p le.ident then
        match le.body with TmLam lm then
          let newIdent = rf le.ident in
          let newBody = _renameIdents p rf le.body in
          {{le with ident=newIdent} with body=newBody}
        else
          error (strJoin "" ["Identifier ",
                             le.ident,
                             " expected to refer to a function."])
      else le
    in TmRecLets {{t with bindings = map handleLet t.bindings}
                   with inexpr = _renameIdents p rf t.inexpr}

  | TmVar v ->
    if p v.ident then
      TmVar {v with ident = rf v.ident}
    else TmVar v

  | tm -> smap_Expr_Expr (_renameIdents p rf) tm

  -- Transform program to use call context.
  -- Considers only identifiers for which p is true.
  sem _transformCallCtx (p : Name -> Bool) (prev : Name) =
  -- Add call context as extra argument in function definitions
  | TmLet ({body = TmLam lm} & t) ->
    if p t.ident then
      let newBody =
        nulam_ _callCtx
               (TmLam {lm with body = _transformCallCtx p t.ident lm.body})
      in TmLet {{t with body = newBody}
                 with inexpr = _transformCallCtx p prev t.inexpr}
    else TmLet {t with inexpr = _transformCallCtx p prev t.inexpr}

  | TmRecLets t ->
    let handleLetExpr = lam le.
      if p le.ident then
        match le.body with TmLam lm then
          let newBody =
            nulam_ _callCtx
              (TmLam {lm with body = _transformCallCtx p le.ident lm.body})
          in {le with body = newBody}
        else
          error "Expected letexpr to have a TmLam in its body"
      else le
    in
    let binds = foldl (lam a. lam b. cons (handleLetExpr b) a) [] t.bindings in
    TmRecLets {{t with bindings = binds}
                with inexpr = _transformCallCtx p prev t.inexpr}
   -- Insert call context as extra argument in function calls (not recursive ones)
  | TmLet ({body = TmApp a} & t) ->
    let id = symb_ (_getSym t.ident) in
    let resBody = _handleAppsCallCtx _transformCallCtx p id prev (TmApp a) in
    TmLet {{t with body = resBody}
            with inexpr = _transformCallCtx p prev t.inexpr}
  -- Replace holes with lookups
  | TmLet ({body = TmHole h} & t) ->
    let id = symb_ (_getSym t.ident) in
    let lookupHole = app_ (app_ (nvar_ _lookup) (nvar_ _callCtx)) id in
    TmLet {{t with body = lookupHole}
            with inexpr = _transformCallCtx p prev t.inexpr}

  | tm -> smap_Expr_Expr (_transformCallCtx p prev) tm

  -- Initialise lookup table as a list of triples (id, path, startGuess)
  sem _initLookupTable (publicFns : [Name]) (g : CallGraph) =
  | tm ->
    let holeInfo = _holeInfo tm in
    let zip = zipWith (lam a. lam b. (a, b)) in
    foldl
      (lam acc. lam t.
         let fun = t.fun in
         let hole = t.hole in
         let depth =
           match hole.depth with TmConst {val = CInt n} then n.val
           else error "Depth must be a constant integer"
         in
         let paths = eqPaths g fun depth publicFns in
         let idPathValInfo =
           map (lam path. {id=t.id, path=path, value=hole.startGuess})
               paths
         in concat acc idPathValInfo)
      [] holeInfo

  -- Return a list of records with keys (function name, hole, id) for all holes
  sem _holeInfo =
  | tm -> _holeInfo2 _top tm

  sem _holeInfo2 (prev : Name) =
  | TmLet ({body = TmHole h} & t) ->
    let id = _getSym t.ident in
    concat [{fun=prev, hole=h, id=symb_ id}]
           (_holeInfo2 prev t.inexpr)

  | TmLet ({body = TmLam lm} & t) ->
    let resBody = _holeInfo2 t.ident lm.body in
    concat resBody (_holeInfo2 prev t.inexpr)

  | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (_holeInfo2 prev) tm)
end

-- TODO(dlunde,2020-09-29): Why does the include order matter here? If I place
-- MExprPrettyPrint first, I get a pattern matching error.
lang PPrintLang = MExprPrettyPrint + HolePrettyPrint

lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

-- Enable/disable printing
let printEnabled = false in
let print = if printEnabled then print else lam x. x in

-- Enable/disable eval
let evalEnabled = false in
let evalE = lam expr. lam expected.
  if evalEnabled then eval {env = []} expr else expected in

-- Prettyprinting
let pprint = lam ast.
  print "\n\n";
  print (expr2str ast);
  print "\n\n" in ();

-- Perform transform tests
let dprintTransform = lam ast.
  -- Symbolize
  let ast = symbolize ast in
  let anfast = anf ast in
  -- Label applications
  print "\n-------------- BEFORE ANF --------------";
  pprint ast;
  print "-------------- AFTER ANF --------------";
  pprint anfast;
  print "-------------- AFTER TRANSFORMATION --------------";
  let ast = transform [] anfast in
  pprint ast;
  print "-------------- END OF TRANSFORMED AST --------------";
  ast
in
let testTransform = lam r.
  let tast = dprintTransform r.ast in
  utest evalE tast r.expected with r.expected in ()
in

-- Perform call graph tests
let callGraphTests = lam ast. lam strVs. lam strEdgs.
  -- Convert to graph with string nodes
  let toStr = lam ng.
    digraphAddEdges
      (map (lam t. (nameGetStr t.0, nameGetStr t.1, t.2)) (digraphEdges ng))
      (digraphAddVertices (map nameGetStr (digraphVertices ng))
                          (digraphEmpty eqString eqsym))
  in
  let g = toCallGraph ast in
  let sg = toStr g in

  utest setEqual eqString strVs (digraphVertices sg) with true in

  let es = digraphEdges sg in
  utest length es with length strEdgs in
  map (lam t. (utest digraphIsSuccessor t.1 t.0 sg with true in ())) strEdgs
in
let testCallgraph = lam r.
  callGraphTests (anf r.ast) r.vs r.calls
in

-- 1
let constant = {
  ast = int_ 1,
  expected = int_ 1,
  vs = ["top"],
  calls = []
} in

-- let foo = lam x. x in ()
let identity = {
  ast = ulet_ "foo" (ulam_ "x" (var_ "x")),
  expected = unit_,
  vs = ["top", "foo"],
  calls = []
} in

-- let foo = lam x. x in
-- let bar = lam x. foo x in ()
let funCall = {
  ast = bind_ (ulet_ "foo" (ulam_ "x" (var_ "x")))
              (ulet_ "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))),
  expected = unit_,
  vs = ["top", "foo", "bar"],
  calls = [("bar", "foo")]
} in

-- let foo = lam x. x in
-- let bar = lam x. addi (foo x) (foo x) in
-- bar 1
let ast =
  bindall_ [identity.ast,
            ulet_ "bar" (ulam_ "x" (addi_ (app_ (var_ "foo") (var_ "x"))
                                         (app_ (var_ "foo") (var_ "x")))),
            (app_ (var_ "bar") (int_ 1))] in
let callSameFunctionTwice = {
  ast = ast,
  expected = int_ 2,
  vs = ["top", "foo", "bar"],
  calls = [("top", "bar"), ("bar", "foo"), ("bar", "foo")]
} in

--let foo = lam x. lam y. addi x y in
--foo 1 2
let twoArgs = {
  ast = bind_
          (ulet_ "foo"
            (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
          (appf2_ (var_ "foo") (int_ 1) (int_ 2)),
  expected = int_ 3,
  vs = ["top", "foo"],
  calls = [("top", "foo")]
} in

-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let b = 3 in
--     addi (bar b) a
-- in ()
let innerFun = {
  ast = ulet_ "foo" (ulam_ "a" (ulam_ "b" (
          let bar = ulet_ "bar" (ulam_ "x"
                         (addi_ (var_ "b") (var_ "x"))) in
          let babar = ulet_ "b" (int_ 3) in
          bind_ bar (
          bind_ babar (
            addi_ (app_ (var_ "bar")
                        (var_ "b"))
                  (var_ "a")))))),
  expected = unit_,
  vs = ["top", "foo", "bar"],
  calls = [("foo", "bar")]
} in

-- let foo = lam x. x in
-- let a = foo 1 in
-- a
let letWithFunCall = {
  ast = let foo = ulet_ "foo" (ulam_ "x" (var_ "x")) in
        let a = ulet_ "a" (app_ (var_ "foo") (int_ 1)) in
        bind_ (bind_ foo a) (var_ "a"),
  expected = int_ 1,
  vs = ["top", "foo"],
  calls = [("top", "foo")]
} in

-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
-- factorial 4
let factorial = {
  ast = bind_
    (ureclets_add "factorial"
           (lam_ "n" (TyInt {})
                 (if_ (eqi_ (var_ "n") (int_ 0))
                      (int_ 1)
                      (muli_ (var_ "n")
                             (app_ (var_ "factorial")
                                   (subi_ (var_ "n")
                                          (int_ 1))))))
     reclets_empty)
    (app_ (var_ "factorial") (int_ 2)),
  expected = int_ 2,
  vs = ["top", "factorial"],
  calls = [("top", "factorial"), ("factorial", "factorial")]
} in

-- recursive
--     let even = lam x.
--         if eqi x 0
--         then true
--         else odd (subi x 1)
--     let odd = lam x.
--         if eqi x 1
--         then true
--         else even (subi x 1)
-- in even 4
let evenOdd ={
  ast = bind_
    (ureclets_add "even" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 0))
                                       (true_)
                                       (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
    (ureclets_add "odd" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 1))
                                      (true_)
                                      (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
     reclets_empty))
    (app_ (var_ "even") (int_ 2)),
  expected = true_,
  vs = ["top", "even", "odd"],
  calls = [("top", "even"), ("even", "odd"), ("odd", "even")]
} in

-- let bar = lam y. y in
-- let foo = lam f. lam x. f x in -- cannot see that foo calls bar
-- foo bar 1
let hiddenCall = {
  ast = bindall_ [
          ulet_ "bar" (ulam_ "y" (var_ "y")),
          ulet_ "foo" (ulam_ "f" (ulam_ "x" (app_ (var_ "f") (var_ "x")))),
          appf2_ (var_ "foo") (var_ "bar") (int_ 1)],
  expected = int_ 1,
  vs = ["top", "foo", "bar"],
  calls = [("top", "foo")]
} in

-- let foo = lam x. lam y.
--   if (<hole>) then x
--   else let d = <hole> in addi x d
-- in foo 42 3
let hole1 = {
  ast =
    bind_
      (ulet_ "foo"
           (ulam_ "x" (ulam_ "y" (if_ ((hole_ true_ (int_ 2))) (var_ "x")
                           (bind_ (ulet_ "d" (hole_ (int_ 1) (int_ 2)))
                                  (addi_ (var_ "x") (var_ "d")))))))
      (appf2_ (var_ "foo") (int_ 42) (int_ 3)),
  expected = int_ 42,
  vs = ["top", "foo"],
  calls = [("top", "foo")]
} in

--let foo = lam x.
--          let d1 = <hole> in
--          let bar = lam y.
--                      let d2 = <hole> in
--                      addi d1 (addi d2 y) in
--          bar 1
--in foo 1
let hole2 = {
  ast =
    bind_
      (ulet_ "foo"
        (ulam_ "x" (bind_
          ((bind_ (ulet_ "d1" (hole_ (int_ 1) (int_ 2)))
             (ulet_ "bar"
               (ulam_ "y" (bind_ (ulet_ "d2" (hole_ (int_ 3) (int_ 2)))
                                 (addi_  (var_ "d1") (addi_ (var_ "d2") (var_ "y"))))))))
          (app_ (var_ "bar") (int_ 1)))
        ))
      (app_ (var_ "foo") (int_ 1)),
   expected = int_ 5,
   vs = ["top", "foo", "bar"],
   calls = [("top", "foo"), ("foo", "bar")]
} in

-- let bar = lam x.
--   let h = TmHole {depth = 2, startGuess = true} in
--   if h then x else (addi x 1)
-- in
-- recursive let foo = lam x.
--   if eqi x 1 then
--     foo 2
--   else
--     bar x
-- in
-- let b1 = bar 1 in
-- let b2 = bar 2 in
-- foo 1
let hole3 = {
  ast = bindall_ [ulet_ "bar" (ulam_ "x"
                    (bind_ (ulet_ "h" (hole_ true_ (int_ 2)))
                           (if_ (var_ "h")
                                (var_ "x")
                                (addi_ (var_ "x") (int_ 1))))),
                  ureclets_add
                    "foo" (ulam_ "x"
                      (if_ (eqi_ (var_ "x") (int_ 1))
                           (app_ (var_ "foo") (int_ 2))
                           (app_ (var_ "bar") (var_ "x"))))
                  reclets_empty,
                  ulet_ "b1" (app_ (var_ "bar") (int_ 1)),
                  ulet_ "b2" (app_ (var_ "bar") (int_ 2)),
                  app_ (var_ "foo") (int_ 1)],
  expected = int_ 2,
  vs = ["top", "bar", "foo"],
  calls = [("top", "foo"), ("top", "bar"), ("top", "bar"), ("foo", "foo"), ("foo", "bar")]
} in

let allTests = [
    hole1
  , hole2
  , hole3
  , constant
  , identity
  , funCall
  , callSameFunctionTwice
  , innerFun
  , letWithFunCall
  , factorial
  , evenOdd
  , hiddenCall
] in

let tTests = [hole1, hole2, hole3] in
let cgTests = allTests in

map testTransform tTests;
map testCallgraph cgTests;

()
