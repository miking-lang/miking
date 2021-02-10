include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"
include "anf.mc"
include "name.mc"
include "hashmap.mc"
include "eq.mc"

-- This file contains implementations related to decision points.

-- TODO: version with table as input (no need to recompile)

let _getSym = lam n.
  optionGetOrElse
    (lam _. error "Expected symbol")
    (nameGetSym n)

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

let _nameHash = lam n.
  sym2hash (_getSym n)

let _nameMapInit : [a] -> (a -> Name) -> (a -> v) -> Hashmap Name v =
  lam items. lam toKey. lam toVal.
    foldl (lam acc. lam i.
             hashmapInsert {eq = _eqn, hashfn = _nameHash} (toKey i) (toVal i) acc)
      hashmapEmpty
      items

-------------------------
-- Call graph creation --
-------------------------

-- NOTE(Linnea, 2021-02-03): the call graph creation algorithm assumes that the
-- AST is symbolized and in ANF.

-- The type of the call graph. Vertices are names of function identifiers, edges
-- are names of application nodes.
type CallGraph = DiGraph Name Name

-- The top of the call graph, has no incoming edges.
let _callGraphTop = nameSym "top"

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

-- NOTE(Linnea, 2021-02-03): Complexity O(|V|*|F|), as we visit each node
-- exactly once and each time potentially perform a graph union operation, which
-- we assume has complexity O(|F|). V is the set of nodes in the AST and F is
-- the set of nodes in the call graph (i.e. set of functions in the AST).
lang Ast2CallGraph = LetAst + LamAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex _callGraphTop (digraphEmpty _eqn _eqn) in
    let g = digraphAddVertices (_findVertices arg) gempty in
    _findEdges g _callGraphTop arg

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
    let resBody = _handleApps t.ident _findEdges prev cg t.body in
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

--------------------------------------------
-- Language fragments for decision points --
--------------------------------------------

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
    match pprintCode indent env h.startGuess with (env, startStr) then
      (env,
         join ["hole ", startStr, " ", int2string h.depth])
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

------------------------------
-- Call context information --
------------------------------

-- Maintains call context information necessary for program transformations.
-- This information is static and is computed once for each program.
type CallCtxInfo = {

  -- Call graph of the program. Functions are nodes, function calls are edges.
  callGraph: CallGraph,

  -- List of public functions of the program (possible entry points in the call
  -- graph)
  publicFns: [Name],

  -- Maps names of functions to the name of its incoming variable. The incoming
  -- variables keep track of the execution path during runtime.
  fun2inc: Hashmap Name Name,

  -- Maps edge labels in the call graph to the incoming variable name of its
  -- from-node.
  lbl2inc: Hashmap Name Name,

  -- Each node in the call graph assigns a per-node unique integer to each
  -- incoming edge. This map maps an edge to the count value of its destination
  -- node.
  lbl2count: Hashmap Name Int

}

-- Create a new name from a prefix string and name.
let _newNameFromStr : Str -> Name -> Name = lam prefix. lam name.
  nameSym (concat prefix (nameGetStr name))
-- Get the name of the incoming variable from a name.
let _incVarFromName = _newNameFromStr "inc_"

-- Compute the call context info from a program.
let callCtxInit : [Name] -> CallGraph -> Expr -> CallCtxInfo =
  lam publicFns. lam callGraph. lam tm.
    let fun2inc =
      _nameMapInit (digraphVertices callGraph) identity _incVarFromName
    in
    let lbl2inc =
      _nameMapInit (digraphEdges callGraph)
        (lam e. match e with (_, _, lbl) then lbl else never)
        (lam e.
           match e with (from, _, _) then
             optionGetOrElse (lam _. error "Internal error: lookup failed")
               (hashmapLookup {eq = _eqn, hashfn = _nameHash} from fun2inc)
           else never)
    in
    let lbl2count =
      foldl (lam acc. lam funName.
               let incomingEdges = digraphEdgesTo funName callGraph in
               match foldl (lam acc. lam e.
                              match e with (_, _, lbl) then
                                match acc with (hm, i) then
                                  (hashmapInsert {eq = _eqn, hashfn = _nameHash}
                                     lbl i hm,
                                   addi i 1)
                                else never
                              else never)
                           (acc, 1)
                           incomingEdges
               with (hm, _) then hm
               else never)
            hashmapEmpty
            (digraphVertices callGraph)
    in
    { callGraph = callGraph, fun2inc = fun2inc, lbl2inc = lbl2inc,
      lbl2count = lbl2count, publicFns = publicFns }

-- Returns the binding of a function name, or None () if the name is not a node
-- in the call graph.
let callCtxFunLookup : Name -> CallCtxInfo -> Option Name = lam name. lam info.
  match info with { fun2inc = fun2inc } then
    hashmapLookup {eq = _eqn, hashfn = _nameHash} name fun2inc
  else never

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxFun2Inc : Name -> CallCtxInfo -> Name = lam name. lam info.
  optionGetOrElse (lam _. error "fun2inc lookup failed")
                  (callCtxFunLookup name info)

-- Get the incoming variable name of an edge label, giving an error if the edge
-- is not part of the call graph.
let callCtxLbl2Inc : Name -> CallCtxInfo -> Name = lam lbl. lam info.
  match info with { lbl2inc = lbl2inc } then
    optionGetOrElse (lam _. error "lbl2inc lookup failed")
                    (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                   lbl lbl2inc)
  else never

-- Get the count of an edge label, giving an error if the edge is not part of
-- the call graph.
let callCtxLbl2Count : Name -> CallCtxInfo -> Int = lam lbl. lam info.
  match info with { lbl2count = lbl2count } then
    optionGetOrElse (lam _. error "lbl2count lookup failed")
                    (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                   lbl lbl2count)
  else never

-- Get all the incoming variable names of the program.
let callCtxIncVarNames : CallCtxInfo -> [Name] = lam info.
  match info with { fun2inc = fun2inc } then
    hashmapValues {eq = _eqn, hashfn = _nameHash} fun2inc
  else never

-- Lookup the internal name of a public function.
let callCtxPubLookup : Name -> CallCtxInfo -> Option Name = lam name. lam info.
  match info with { pub2internal = pub2internal } then
    hashmapLookup {eq = _eqn, hashfn = _nameHash} name pub2internal
  else never

-----------------------------
-- Program transformations --
-----------------------------

-- The initial value of an incoming variable.
let _incUndef = 0
-- Get the name of a forwarding call variable from a name.
let _fwdVarFromName = _newNameFromStr "fwd_"
-- Get the name of a private function from a name.
let _privFunFromName = _newNameFromStr "pri_"

-- Get the leftmost node (callee function) in a nested application node. Returns
-- optionally the variable name if the leftmost node is a variable, otherwise
-- None ().
let _appGetCallee : Expr -> Option Name = use AppAst in use VarAst in lam tm.
  recursive let work = lam app.
    match app with TmApp {lhs = TmVar v} then
      Some v.ident
    else match app with TmApp {lhs = TmApp a} then
      work (TmApp a)
    else None ()
  in work tm

let _x = nameSym "x"
let _y = nameSym "y"
utest _appGetCallee (appf3_ (nvar_ _x) true_ (nvar_ _y) (int_ 4)) with Some _x
utest _appGetCallee (addi_ (nvar_ _x) (int_ 3)) with None ()

-- Set the leftmost node (callee function) to a given name in a nested
-- application.
let _appSetCallee : Expr -> Name -> Expr = use AppAst in use VarAst in
  lam tm. lam callee.
    recursive let work : Expr -> Expr = lam app.
      match app with TmApp ({lhs = TmVar v} & a) then
        TmApp {a with lhs = TmVar {v with ident = callee}}
      else match app with TmApp ({lhs = TmApp a} & t) then
        TmApp {t with lhs = work (TmApp a)}
      else error "Expected an application"
    in work tm

let _x = nameSym "x"
let _y = nameSym "y"
utest _appSetCallee
      (appf2_ (nvar_ _x) (nvar_ _y) (int_ 4)) _y
with  (appf2_ (nvar_ _y) (nvar_ _y) (int_ 4))

-- Replace the innermost body in a nested lambda expression by the result of a
-- function that operates on the list of arguments of the lambda.
let _lamWithBody : ([Name] -> Expr) -> Expr -> Expr = use FunAst in
  lam f. lam tm.
    recursive let work : [Name] -> Expr -> Expr = lam acc. lam tm.
      match tm with TmLam ({ body = TmLam lm, ident = ident } & t) then
        TmLam {t with body = work (snoc acc ident) (TmLam lm)}
      else match tm with TmLam ({ ident = ident } & t) then
        TmLam {t with body = f (snoc acc ident)}
      else error "Expected a lambda expression"
    in work [] tm

let _x = nameSym "x"
let _y = nameSym "y"
let _z = nameSym "z"
utest
  _lamWithBody (lam args.
                  match args with [x, y, z] then
                    muli_ (nvar_ x) (nvar_ y)
                  else error "Test failed")
               (nulam_ _x (nulam_ _y (nulam_ _z (addi_ (int_ 1) (int_ 1)))))
with (nulam_ _x (nulam_ _y (nulam_ _z (muli_ (nvar_ _x) (nvar_ _y)))))

-- Generate skeleton code for looking up a value of a decision point depending
-- on its call history
let _lookupCallCtx : Lookup -> Name -> Name -> CtxEnv -> [[Name]] -> Skeleton =
  use MatchAst in use NeverAst in
    lam lookup. lam holeId. lam incVarName. lam info. lam paths.
      match info with { lbl2inc = lbl2inc } then
        -- TODO: Represent paths as trees, then this partition becomes trivial
        let partitionPaths : [[Name]] -> ([Name], [[[Name]]]) = lam paths.
          let startVals = foldl (lam acc. lam p.
                                   setInsert _eqn (head p) acc)
                                [] paths in
          let partition = (makeSeq (length startVals) []) in
          let partition =
            mapi
              (lam i. lam _. filter (lam p. _eqn (head p) (get startVals i)) paths)
              partition
          in
          (startVals, partition)
        in
        recursive let work : Name -> [[Name]] -> [Name] -> Expr =
          lam incVarName. lam paths. lam acc.
            let nonEmpty = filter (lam p. not (null p)) paths in
            match partitionPaths nonEmpty with (startVals, partition) then
              let branches =
                mapi (lam i. lam n.
                        let iv = callCtxLbl2Inc n info in
                        let count = callCtxLbl2Count n info in
                        matchex_ (deref_ (nvar_ incVarName)) (pint_ count)
                                 (work iv (map tail (get partition i)) (cons n acc)))
                     startVals
              in
              let defaultVal =
                if eqi (length nonEmpty) (length paths) then never_
                else lookup holeId
              in
              matchall_ (snoc branches defaultVal)
            else never
          in
        work incVarName (map reverse paths) []
      else never

-- Helper for creating a hidden equivalent of a public function and replace the
-- public function with a forwarding call to the hidden function.
type Binding = {ident : Name, ty : Type, body : Expr}
let _forwardCall : Name -> (Expr -> Expr) -> Binding -> (Binding, Binding) =
  use FunAst in
    lam local. lam f. lam bind.
      let fwdVar = _fwdVarFromName bind.ident in
      let newBody = lam args.
        bind_ (nulet_ fwdVar (appSeq_ (nvar_ local) (map nvar_ args)))
        (nvar_ fwdVar)
      in
      let localFun = {{bind with ident = local}
                            with body = f bind.body}
      in (localFun, {bind with body = _lamWithBody newBody bind.body})

type Lookup = Int -> Expr
type Table = Map Name (Map [Name] Int)
type CtxEnv = {info: CallCtxInfo, table: Table, count: Int}

recursive let _cmpPaths = lam p1 : [Name]. lam p2 : [Name].
  error "Not implemented"
end


let ctxEnvEmpty : [Name] -> CallGraph -> Expr -> CtxEnv =
  use Ast2CallGraph in lam public. lam g. lam tm.
    { info = callCtxInit public g tm
    , table = mapEmpty nameCmp
    , count = 0
    }

let ctxEnvAddHole : Name -> [Name] -> CtxEnv -> CtxEnv = lam name. lam paths. lam env.
  match env with { count = count, table = table } then
  match
    foldl
    (lam acc. lam k.
       match acc with (m, i) then (mapInsert path i, addi i 1)
       else never)
    (mapEmpty _cmpPaths, count)
    paths
  with (m, count) then
    {{env with count = count} with table = mapInsert name m}
  else never else never

--
lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + MatchAst + NeverAst
                         -- Included for debugging
                         + MExprPrettyPrint
  syn Intermediate =
  | Partial {part: Lookup -> Expr, table: Table}
  | Complete {prog: Expr, table: Table} -- TODO

  -- Find the initial mapping from decision points to values
  -- Returns a function of type 'Lookup'.
  sem initAssignments (table : Table) =
  | tm ->
    let idsOfHole = lam name.
      let m = mapFind name table in
      map (lam t. match t with (k, v) then v else never) (mapBindings m)
    in
    -- Find the start guess of each decision point
    recursive let findHoles : [(Int, Expr)] -> Expr -> [(Int, Expr)] =
      lam acc. lam t.
        match t with TmLet ({body = TmHole {startGuess = startGuess}} & le) then
          let ids = idsOfHole le.ident in
          findHoles (concat (map (lam i. (i, startGuess)) ids) acc) le.inexpr
        else
          sfold_Expr_Expr concat acc (smap_Expr_Expr (findHoles acc) t)
    in
    -- Build a map for int -> value
    let m =
      foldl (lam acc. lam t.
               mapInsert t.0 t.1 acc)
            (mapEmpty subi)
            (findHoles [] tm) in
    -- Return the lookup function
    lam i. mapFind i m

  -- Transform a program with decision points. Returns a function of type
  -- 'Skeleton'. Applying this function to a lookup function yields an MExpr
  -- program where the values of the decision points have been statically
  -- replaced by values given by the lookup function.
  sem transform (publicFns : [Name]) =
  | tm ->
    let pub2priv = _nameMapInit publicFns identity _privFunFromName in
    let tm = _replacePublic pub2priv tm in
    let env = ctxEnvEmpty publicFns (toCallGraph tm) tm in
    -- Declare the incoming variables
    let incVars =
      bindall_ (map (lam incVarName. nulet_ incVarName (ref_ (int_ _incUndef)))
                    (callCtxIncVarNames env.info))
    in
    let tm = bind_ incVars tm in
    lam lookup. _maintainCallCtx lookup env _callGraphTop tm

  -- Move the contents of each public function to a hidden private function, and
  -- forward the call to the public functions to their private equivalent.
  sem _replacePublic (pub2priv : Hashmap Name Name) =
  -- Function call: forward call for public function
  | TmLet ({ body = TmApp a } & t) ->
    match _appGetCallee (TmApp a) with Some callee then
      match hashmapLookup {eq = _eqn, hashfn = _nameHash} callee pub2priv
      with Some local then
        TmLet {{t with body = _appSetCallee (TmApp a) local}
                  with inexpr = _replacePublic pub2priv t.inexpr}
      else TmLet {t with inexpr = _replacePublic pub2priv t.inexpr}
    else TmLet {t with inexpr = _replacePublic pub2priv t.inexpr}

  -- Function definition: create private equivalent of public functions
  | TmLet ({ body = TmLam lm } & t) ->
    match hashmapLookup {eq = _eqn, hashfn = _nameHash} t.ident pub2priv
    with Some local then
      match _forwardCall local (_replacePublic pub2priv) t with (priv, pub) then
        let pubAndRest =
          TmLet {pub with inexpr = _replacePublic pub2priv t.inexpr}
        in TmLet {priv with inexpr = pubAndRest}
      else never
    else TmLet {{t with inexpr = _replacePublic pub2priv t.inexpr}
                   with body = _replacePublic pub2priv t.body}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds = foldl
      (lam acc. lam bind.
        match bind with { body = TmLam lm } then
          match hashmapLookup {eq = _eqn, hashfn =_nameHash} bind.ident pub2priv
          with Some local then
            match _forwardCall local (_replacePublic pub2priv) bind
            with (privBind, pubBind) then
              concat [privBind, pubBind] acc
            else never
          else cons bind acc
        else cons bind acc)
      [] bindings
    in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _replacePublic pub2priv t.inexpr}

  | tm -> smap_Expr_Expr (_replacePublic pub2priv) tm

  -- Maintain call context history by updating incoming variables before
  -- function calls.
  sem _maintainCallCtx (lookup : Lookup) (env : ContextEnv) (cur : Name) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    -- NOTE(Linnea, 2021-01-29): ANF form means no recursion necessary for the
    -- application node (can only contain values)
    let le = TmLet {t with inexpr = _maintainCallCtx lookup env cur t.inexpr} in
    match _appGetCallee (TmApp a) with Some callee then
      match callCtxFunLookup callee env.info
      with Some iv then
        -- Set the incoming var of callee to current node
        let count = callCtxLbl2Count t.ident env.info in
        let update = modref_ (nvar_ iv) (int_ count) in
        bind_ (nulet_ (nameSym "_") update) le
      else le
    else le

  -- Decision point: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
     match env.info with
      { callGraph = callGraph, publicFns = publicFns }
     then
       let paths = eqPaths callGraph cur depth publicFns in
       let env = ctxEnvAddHole ident paths in
       let iv = callCtxFun2Inc cur env.info in
       let lookupCode = _lookupCallCtx lookup ident iv env paths in
       TmLet {{t with body = lookupCode}
                 with inexpr = _maintainCallCtx lookup env cur t.inexpr}
     else never

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody =
      match callCtxFunLookup t.ident env.info with Some _
      then t.ident
      else cur
    in TmLet {{t with body = _maintainCallCtx lookup env curBody t.body}
                 with inexpr = _maintainCallCtx lookup env cur t.inexpr}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds =
      map (lam bind.
             match bind with { body = TmLam lm } then
               let curBody =
                 match callCtxFunLookup bind.ident env.info with Some _
                 then bind.ident
                 else cur
               in {bind with body = _maintainCallCtx lookup env curBody bind.body}
             else {bind with body = _maintainCallCtx lookup env cur bind.body})
      bindings
    in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _maintainCallCtx lookup env cur inexpr}
  | tm ->
    smap_Expr_Expr (_maintainCallCtx lookup env cur) tm
end

lang PPrintLang = MExprPrettyPrint + HolePrettyPrint

lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF

lang MExprHoles = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

----------------------
-- Call graph tests --
----------------------

let doCallGraphTests = lam r.
  let tests = lam ast. lam strVs. lam strEdgs.
    let toStr = lam ng.
      digraphAddEdges
        (map (lam t. (nameGetStr t.0, nameGetStr t.1, t.2)) (digraphEdges ng))
        (digraphAddVertices (map nameGetStr (digraphVertices ng))
                            (digraphEmpty eqString _eqn))
    in
    let sg = toStr (toCallGraph ast) in

    utest setEqual eqString strVs (digraphVertices sg) with true in

    let es = digraphEdges sg in
    utest length es with length strEdgs in
    map (lam t. (utest digraphIsSuccessor t.1 t.0 sg with true in ())) strEdgs
  in
  tests (anf r.ast) r.vs r.calls
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


let cgTests = [
    constant
  , identity
  , funCall
  , callSameFunctionTwice
  , innerFun
  , letWithFunCall
  , factorial
  , evenOdd
  , hiddenCall
] in

let _ = map doCallGraphTests cgTests in


---------------------------
-- Decision points tests --
---------------------------

let funA = nameSym "funA" in
let funB = nameSym "funB" in
let funC = nameSym "funC" in
let funD = nameSym "funD" in
let h = nameSym "h" in

let debug = false in

let debugPrint = lam ast. lam pub.
  if debug then
    let _ = printLn "----- BEFORE ANF -----\n" in
    let _ = printLn (expr2str ast) in
    let ast = anf ast in
    let _ = printLn "\n----- AFTER ANF -----\n" in
    let _ = printLn (expr2str ast) in
    let skel = transform pub ast in
    let lookup = initAssignments ast in
    let _ = printLn "\n----- AFTER TRANSFORMATION -----\n" in
    let _ = printLn (expr2str (skel lookup)) in
    ()
  else ()
in

-- let funA = lam _.
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
let ast = bindall_ [  nulet_ funA (ulam_ "_"
                        (bind_ (nulet_ h (hole_ (int_ 0) 2))
                               (nvar_ h)))
                    , nureclets_add funB
                        (ulam_ "xB"
                          (ulam_ "y" (if_ (var_ "xB")
                                          (if_ (var_ "y")
                                               (appf2_ (nvar_ funB) true_ false_)
                                               (app_ (nvar_ funA) (var_ "xB")))
                                          (app_ (nvar_ funA) (var_ "y")))))
                        reclets_empty
                    , nulet_ funC (ulam_ "xC"
                        (appf2_ (nvar_ funB) (var_ "xC") false_))
                   ]
in
let _ = debugPrint ast [funB, funC] in
let ast = anf ast in
let cg = toCallGraph ast in
let edgeCB =
  match digraphEdgesBetween funC funB cg with [(_,_,sym)]
  then sym else error "Expected one edge"
in
let edgesBA =
  match digraphEdgesBetween funB funA cg with [(_,_,s1), (_,_,s2)]
  then [s1, s2] else error "Expected two edges"
in
let edgeBA1 = head edgesBA in
let edgeBA2 = last edgesBA in
let edgeBB =
  match digraphEdgesBetween funB funB cg with [(_,_,sym)]
  then sym else error "Expected one edge"
in

let eqNameSeq = setEqual _eqn in

-- let lookup = lam _. lam path.
--   match      eqNameSeq path [edgeCB, edgeBA1] with true then int_ 1
--   else match eqNameSeq path [edgeCB, edgeBA2] with true then int_ 2
--   else match eqNameSeq path [edgeBB, edgeBA1] with true then int_ 3
--   else match eqNameSeq path [edgeBB, edgeBA2] with true then int_ 4
--   else match path with _ ++ [e] then
--     if nameEq e edgeBA1 then int_ 5
--     else if nameEq e edgeBA2 then int_ 6
--     else error (join ["Unknown path: ", strJoin " " (map nameGetStr path)])
--   else error (join ["Unknown path: ", strJoin " " (map nameGetStr path)])
-- in

-- -- Extensions are possibly in non-ANF to mimic calls from outside the library.
-- let appendToAst = lam ast. lam suffix.
--   let ast = bind_ ast suffix in
--   let skel = transform [funB, funC] ast in
--   let res = skel lookup in
--   let _ = print (expr2str res) in
--   res
-- in

-- utest eval { env = [] } (appendToAst ast
--   (app_ (nvar_ funC) true_)
-- ) with int_ 1 in

-- -- utest eval { env = [] } (appendToAst ast
-- --   (app_ (nvar_ funC) false_)
-- -- ) with int_ 2 in

-- -- utest eval { env = [] } (appendToAst ast
-- --   (appf2_ (nvar_ funB) true_ true_)
-- -- ) with int_ 3 in

-- -- utest eval { env = [] } (appendToAst ast
-- --   (appf2_ (nvar_ funB) true_ false_)
-- -- ) with int_ 5 in

-- -- utest eval { env = [] } (appendToAst ast
-- --   (appf2_ (nvar_ funB) false_ false_)
-- -- ) with int_ 6 in

-- -- utest eval { env = [] } (appendToAst ast
-- --   (bind_ (nulet_ (nameSym "_") (app_ (nvar_ funC) false_))
-- --          (appf2_ (nvar_ funB) false_ false_))
-- -- ) with int_ 6 in

-- -- let paths = eqPaths cg funA 2 [funB, funC] in
-- let dprintLn = lam d. let _ = dprint d in printLn "" in

-- -- -- ca
-- -- let _ = dprintLn ([edgeCB, edgeBA1]) in
-- -- let _ = dprintLn (get paths 1) in
-- -- let _ = printLn "" in

-- -- -- a
-- -- let _ = dprintLn (get paths 0) in
-- -- let _ = dprintLn ([edgeBA1]) in
-- -- let _ = printLn "" in

-- -- -- cb
-- -- let _ = dprintLn ([edgeCB, edgeBA2]) in
-- -- let _ = dprintLn (get paths 4) in
-- -- let _ = printLn "" in

-- -- -- da
-- -- let _ = dprintLn [edgeBB, edgeBA1] in
-- -- let _ = dprintLn (get paths 2) in
-- -- let _ = printLn "" in

-- -- let _ = dprintLn (get paths 3) in
-- -- let _ = dprintLn (get paths 5) in

-- let _ = dprintLn argv in

()
