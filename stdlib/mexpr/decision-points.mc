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
include "common.mc"


-- This file contains implementations related to decision points.

let _getSym = lam n.
  optionGetOrElse
    (lam. error "Expected symbol")
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

let _cmpPaths = seqCmp nameCmp

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
  lam letexpr : {ident : Name, tyBody : Type, body : Expr,
                 inexpr : Expr, ty : Type, info : Info}.
  lam f.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

let _handleLetEdge = use LamAst in
  lam letexpr : {ident : Name, tyBody : Type, body : Expr,
                 inexpr : Expr, ty : Type, info : Info}.
  lam f. lam g. lam prev.
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

  sem ty =
  | TmHole h -> tyunknown_ -- TODO(dlunde,2021-02-26) I added this for compatibility with an ANF change. Should maybe be `h.ty` rather than `TyUnknown {}` if it makes sense to give this term a type annotation (as with the other terms in ast.mc).

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
  lbl2count: Hashmap Name Int,

  -- Maps a decision points and a call path to a unique integer.
  hole2idx: Ref (Map Name (Map [Name] Int)),

  -- Counts the number of decision points stored thus far.
  count: Int
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
             optionGetOrElse (lam. error "Internal error: lookup failed")
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
    let hole2idx = ref (mapEmpty nameCmp) in
    { callGraph = callGraph
    , fun2inc = fun2inc
    , lbl2inc = lbl2inc
    , lbl2count = lbl2count
    , publicFns = publicFns
    , hole2idx  = hole2idx
    , count = 0
    }

-- Returns the binding of a function name, or None () if the name is not a node
-- in the call graph.
let callCtxFunLookup : Name -> CallCtxInfo -> Option Name = lam name. lam info.
  match info with { fun2inc = fun2inc } then
    hashmapLookup {eq = _eqn, hashfn = _nameHash} name fun2inc
  else never

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxFun2Inc : Name -> CallCtxInfo -> Name = lam name. lam info.
  optionGetOrElse (lam. error "fun2inc lookup failed")
                  (callCtxFunLookup name info)

-- Get the incoming variable name of an edge label, giving an error if the edge
-- is not part of the call graph.
let callCtxLbl2Inc : Name -> CallCtxInfo -> Name = lam lbl. lam info.
  match info with { lbl2inc = lbl2inc } then
    optionGetOrElse (lam. error "lbl2inc lookup failed")
                    (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                   lbl lbl2inc)
  else never

-- Get the count of an edge label, giving an error if the edge is not part of
-- the call graph.
let callCtxLbl2Count : Name -> CallCtxInfo -> Int = lam lbl. lam info.
  match info with { lbl2count = lbl2count } then
    optionGetOrElse (lam. error "lbl2count lookup failed")
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

let callCtxAddHole : Name -> [[Name]] -> CallCtxInfo -> CallCtxInfo =
  lam name. lam paths. lam info.
    match info with { hole2idx = hole2idx, count = count } then
    match
      foldl
      (lam acc. lam k.
         match acc with (m, i) then (mapInsert k i m, addi i 1)
         else never)
      (mapEmpty _cmpPaths, count)
      paths
    with (m, count) then
      modref hole2idx (mapInsert name m (deref hole2idx));
      {info with count = count}
    else never else never

let callCtxHole2Idx : Name -> [Name] -> CallCtxInfo -> Int =
  lam name. lam path. lam info.
    match info with { hole2idx = hole2idx } then
      mapFindWithExn path (mapFindWithExn name (deref hole2idx))
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
let _lamWithBody : ([Name] -> Expr) -> Expr -> Expr = use LamAst in
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
let _lookupCallCtx : Lookup -> Name -> Name -> CallCtxInfo -> [[Name]] -> Skeleton =
  use MatchAst in use NeverAst in
    lam lookup. lam holeId. lam incVarName. lam info. lam paths.
      match info with { lbl2inc = lbl2inc } then
        -- TODO: Represent paths as trees, then this partition becomes trivial
        let partitionPaths : [[Name]] -> ([Name], [[[Name]]]) = lam paths.
          let startVals = foldl (lam acc. lam p.
                                   setInsert _eqn (head p) acc)
                                [] paths in
          let partition = (create (length startVals) (lam. [])) in
          let partition =
            mapi
              (lam i. lam. filter (lam p. _eqn (head p) (get startVals i)) paths)
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
                else lookup (callCtxHole2Idx holeId acc info)
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
  use LamAst in
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

let _table = nameSym "table"

--
lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + MatchAst + NeverAst
                         -- Included for debugging
                         + MExprPrettyPrint
  syn Intermediate =
  | Complete {prog: Expr, table: Table}
  | Partial {part: Lookup -> Expr} -- TODO

  -- Find the initial mapping from decision points to values
  -- Returns a function of type 'Lookup'.
  sem initAssignments (table : Table) =
  | tm ->
    let idsOfHole = lam name.
      let m = mapFindWithExn name table in
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
    lam i. mapFindWithExn i m

  -- Transform a program with decision points. Returns a function of type
  -- 'Skeleton'. Applying this function to a lookup function yields an MExpr
  -- program where the values of the decision points have been statically
  -- replaced by values given by the lookup function.
  sem transform (publicFns : [Name]) =
  | tm ->
    let pub2priv = _nameMapInit publicFns identity _privFunFromName in
    let tm = _replacePublic pub2priv tm in
    let info = callCtxInit publicFns (toCallGraph tm) tm in
    -- Declare the incoming variables
    let incVars =
      bindall_ (map (lam incVarName. nulet_ incVarName (ref_ (int_ _incUndef)))
                    (callCtxIncVarNames info))
    in
    let tm = bind_ incVars tm in
    let lookup = lam i. get_ (nvar_ _table) (int_ i) in
    let prog = _maintainCallCtx lookup info _callGraphTop tm in
    Complete { prog = prog
             , table = deref (info.hole2idx)
             }

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
  sem _maintainCallCtx (lookup : Lookup) (info : CallCtxInfo) (cur : Name) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    -- NOTE(Linnea, 2021-01-29): ANF form means no recursion necessary for the
    -- application node (can only contain values)
    let le = TmLet {t with inexpr = _maintainCallCtx lookup info cur t.inexpr} in
    match _appGetCallee (TmApp a) with Some callee then
      match callCtxFunLookup callee info
      with Some iv then
        -- Set the incoming var of callee to current node
        let count = callCtxLbl2Count t.ident info in
        let update = modref_ (nvar_ iv) (int_ count) in
        bind_ (nulet_ (nameSym "_") update) le
      else le
    else le

  -- Decision point: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
     match info with
      { callGraph = callGraph, publicFns = publicFns }
     then
       let paths = eqPaths callGraph cur depth publicFns in
       let info = callCtxAddHole ident paths info in
       let iv = callCtxFun2Inc cur info in
       let lookupCode = _lookupCallCtx lookup ident iv info paths in
       TmLet {{t with body = lookupCode}
                 with inexpr = _maintainCallCtx lookup info cur t.inexpr}
     else never

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody =
      match callCtxFunLookup t.ident info with Some _
      then t.ident
      else cur
    in TmLet {{t with body = _maintainCallCtx lookup info curBody t.body}
                 with inexpr = _maintainCallCtx lookup info cur t.inexpr}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds =
      map (lam bind.
             match bind with { body = TmLam lm } then
               let curBody =
                 match callCtxFunLookup bind.ident info with Some _
                 then bind.ident
                 else cur
               in {bind with body = _maintainCallCtx lookup info curBody bind.body}
             else {bind with body = _maintainCallCtx lookup info cur bind.body})
      bindings
    in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _maintainCallCtx lookup info cur inexpr}
  | tm ->
    smap_Expr_Expr (_maintainCallCtx lookup info cur) tm
end

lang PPrintLang = MExprPrettyPrint + HolePrettyPrint

lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF
  + MExprSym + MExprEq

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
           (lam_ "n" (tyint_)
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

map doCallGraphTests cgTests;


---------------------------
-- Decision points tests --
---------------------------

let debug = false in

let debugPrint = lam ast. lam pub.
  if debug then
    printLn "----- BEFORE ANF -----\n";
    printLn (expr2str ast);
    let ast = anf ast in
    printLn "\n----- AFTER ANF -----\n";
    printLn (expr2str ast);
    match transform pub ast with Complete { prog = prog } then
      printLn "\n----- AFTER TRANSFORMATION -----\n";
      printLn (expr2str prog);
      ()
    else never
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
let ast = bindall_ [  nulet_ funA (ulam_ "_"
                        (bind_ (nulet_ h (hole_ (int_ 0) 2))
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
debugPrint ast [funB, funC];
let ast = anf ast in

match transform [funB, funC] ast with Complete { table = table, prog = prog } then
match mapBindings table with [(_, m)] then


if debug then
  printLn "Mapped paths";
  map dprintLn (sort (lam t1. lam t2. subi t1.1 t2.1) (mapBindings m))
else ();

let evalWithArgv = lam table : [Expr]. lam ast : Expr. lam ext : Expr.
  let ast = bind_ (bind_ (nulet_ _table table) ast) ext in
  eval { env = builtinEnv } ast
in

let idxs = map (lam t. t.1) (mapBindings m) in
let table = seq_ (mapi (lam i. lam. int_ (addi 1 i)) idxs) in

let eval = evalWithArgv table in

-- Path 1: C -> B (1)-> A
utest eval prog (
  app_ (nvar_ funC) true_
) with int_ 1 in

-- Path 2: B (1)-> A
utest eval prog (
  appf2_ (nvar_ funB) true_ false_
) with int_ 2 in

-- Path 3: B -> B (1)-> A
utest eval prog (
  appf2_ (nvar_ funB) true_ true_
) with int_ 3 in

-- Path 4: C -> B (2)-> A
utest eval prog (
  app_ (nvar_ funC) false_
) with int_ 4 in

-- Path 5: B (2)-> A
utest eval prog (
  appf2_ (nvar_ funB) false_ false_
) with int_ 5 in

-- Path 5 again
utest eval prog (
  bind_ (nulet_ (nameSym "_") (app_ (nvar_ funC) false_))
        (appf2_ (nvar_ funB) false_ false_)
) with int_ 5 in

-- Path 6: B -> B (2)-> A
-- unreachable

()

else never else never
=======
--include "mexpr.mc"
--include "pprint.mc"
--include "digraph.mc"
--include "string.mc"
--include "ast-builder.mc"
--include "eq-paths.mc"
--include "anf.mc"
--include "name.mc"
--include "common.mc"
--
---- This file contains implementations related to decision points. In particular,
---- it implements:
---- * A language fragment for decision points (HoleAst)
---- * An algorithm for AST -> call graph conversion (Ast2CallGraph fragment)
---- * Program transformations for programs with decision points (HolyCallGraph)
--
--let _top = nameSym "top"
--
--let _projName = nameSym "x"
--let _head = lam s. get_ s (int_ 0)
--let _tail = lam s. ntupleproj_ _projName 1 (splitat_ s (int_ 1))
--let _null = lam s. eqi_ (int_ 0) (length_ s)
--
--let _drecordproj = use MExprAst in
--  lam key. lam r.
--  nrecordproj_ _projName key r
--
--let _eqn = lam n1. lam n2.
--  if and (nameHasSym n1) (nameHasSym n2) then
--    nameEqSym n1 n2
--  else
--    error "Name without symbol."
--
--let _getSym = lam n.
--  (optionGetOrElse
--    (lam. error "Expected symbol")
--    (nameGetSym n))
--
--lang HoleAst
--  syn Expr =
--  | TmHole {startGuess : Expr,
--            depth : Int}
--
--  sem symbolizeExpr (env : SymEnv) =
--  | TmHole h -> TmHole h
--
--  sem smap_Expr_Expr (f : Expr -> a) =
--  | TmHole h -> TmHole h
--
--  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
--  | TmHole h -> acc
--end
--
--lang HolePrettyPrint = HoleAst + TypePrettyPrint
--  sem isAtomic =
--  | TmHole _ -> false
--
--  sem pprintCode (indent : Int) (env : SymEnv) =
--  | TmHole h ->
--    match pprintCode indent env h.startGuess with (env1, startStr) then
--      match pprintCode indent env1 h.depth with (env2, depthStr) then
--        (env2,
--           join ["Hole (", strJoin ", " [startStr, depthStr],")"])
--      else never
--    else never
--end
--
--lang HoleANF = HoleAst + ANF
--  sem isValue =
--  | TmHole _ -> false
--
--  sem normalize (k : Expr -> Expr) =
--  | TmHole {startGuess = startGuess, depth = depth} ->
--    k (TmHole {startGuess = normalizeTerm startGuess, depth = depth})
--end
--
--let hole_ = use HoleAst in
--  lam startGuess. lam depth.
--  TmHole {startGuess = startGuess, depth = depth}
--
---- Create a call graph from an AST.
---- * Vertices (identifier names) are functions f defined as: let f = lam. ...
---- * There is an edge between f1 and f2 iff f1 calls f2: let f1 = lam. ... (f2 a)
---- * "top" is the top of the graph (i.e., no incoming edges)
--
--type CallGraph = DiGraph Name Symbol
--
--let _handleLetVertex = use LamAst in
--  lam letexpr : {ident : Name, tyBody : Type, body : Expr,
--                 inexpr : Expr, ty : Type, info : Info}.
--  lam f.
--    match letexpr.body with TmLam lm
--    then cons letexpr.ident (f lm.body)
--    else f letexpr.body
--
--let _handleLetEdge = use LamAst in
--  lam letexpr : {ident : Name, tyBody : Type, body : Expr,
--                 inexpr : Expr, ty : Type, info : Info}.
--  lam f. lam g. lam prev.
--    match letexpr.body with TmLam lm
--    then f g letexpr.ident lm.body
--    else f g prev letexpr.body
--
--let _handleApps = use AppAst in use VarAst in
--  lam id. lam f. lam prev. lam g. lam app.
--    recursive let appHelper = lam g. lam app.
--      match app with TmApp {lhs = TmVar v, rhs = rhs} then
--        let resLhs =
--          if digraphHasVertex v.ident g then
--            digraphAddEdge prev v.ident id g
--          else g
--        in f resLhs prev rhs
--      else match app with TmApp ({lhs = TmApp a, rhs = rhs}) then
--        let resLhs = appHelper g (TmApp a) in
--        f resLhs prev rhs
--      else match app with TmApp a then
--        f (f g prev a.lhs) prev a.rhs
--      else never
--  in appHelper g app
--
---- Complexity (I think): O(|V|*|F|), as we visit each node exactly once and each
---- time potentially perform a graph union operation, which we assume has
---- complexity O(|F|). V is the set of nodes in the AST and F is the set of nodes
---- in the call graph (i.e. set of functions in the AST).
--lang Ast2CallGraph = LetAst + LamAst + RecLetsAst
--  sem toCallGraph =
--  | arg ->
--    let gempty = digraphAddVertex _top (digraphEmpty _eqn eqsym) in
--    let g = digraphAddVertices (_findVertices arg) gempty in
--    _findEdges g _top arg
--
--  sem _findVertices =
--  | TmLet t ->
--    let res_body = _handleLetVertex t _findVertices
--    in concat res_body (_findVertices t.inexpr)
--
--  | TmRecLets t ->
--    let res =
--      foldl (lam a. lam b. concat a (_handleLetVertex b _findVertices))
--            [] t.bindings
--    in
--    concat res (_findVertices t.inexpr)
--
--  | tm ->
--    sfold_Expr_Expr concat [] (smap_Expr_Expr _findVertices tm)
--
--  sem _findEdges (cg : CallGraph) (prev : Name) =
--  | TmLet ({body = TmApp a} & t) ->
--    let id = _getSym t.ident in
--    let resBody = _handleApps id _findEdges prev cg t.body in
--    _findEdges resBody prev t.inexpr
--
--  | TmLet ({body = TmLam lm} & t) ->
--    let resBody = _findEdges cg t.ident lm.body in
--    _findEdges resBody prev t.inexpr
--
--  | TmRecLets t ->
--    let res =
--      foldl (lam g. lam b. digraphUnion g (_handleLetEdge b _findEdges g prev))
--            cg t.bindings
--    in _findEdges res prev t.inexpr
--
--  | tm ->
--    sfold_Expr_Expr digraphUnion cg (smap_Expr_Expr (_findEdges cg prev) tm)
--end
--
---- Variable names to be used in transformed program
--let _callCtx = nameSym "callCtx"
--let _lookupTable = nameSym "lookupTable"
--let _lookup = nameSym "lookup"
--let _maxDepth = nameSym "maxDepth"
--let _addCall = nameSym "addCall"
--let _filter = nameSym "filter"
--let _max = nameSym "max"
--let _isPrefix = nameSym "isPrefix"
--let _isSuffix = nameSym "isSuffix"
--
--let _handleAppsCallCtx = use AppAst in use VarAst in
--  lam f. lam p. lam id. lam prev. lam app.
--    recursive let appHelper = lam app.
--      match app with TmApp {lhs = TmVar v, rhs = rhs} then
--        if p v.ident then
--          let isRecCall = _eqn prev v.ident in
--          let newCallCtx =
--            if isRecCall then (nvar_ _callCtx)
--            else appf2_ (nvar_ _addCall) (nvar_ _callCtx) id
--          in
--          app_ (app_ (TmVar v) newCallCtx)
--               (f p prev rhs)
--        else app
--      else match app with TmApp {lhs = TmApp a, rhs = rhs} then
--        let resLhs = appHelper (TmApp a) in
--        app_ resLhs (f p prev rhs)
--      else match app with TmApp a then
--        app_ (f p prev a.lhs) (f p prev a.rhs)
--      else never
--    in appHelper app
--
--lang ContextAwareHoles = Ast2CallGraph + HoleAst + IntAst + SymbAst
--  sem transform (publicFns : [Name]) =
--  | tm ->
--    let callGraph = toCallGraph tm in
--
--    -- Check if identifier is a function in the call graph
--    let isVertex = lam ident.
--      optionIsSome (find (_eqn ident) (digraphVertices callGraph)) in
--
--    -- Check if identifier is a public function
--    let isPublic = lam ident.
--      optionIsSome (find (_eqn ident) publicFns) in
--
--    -- Renaming function for public functions
--    let renamePub = lam ident.
--      let nameStr = nameGetStr ident in
--      let newNameStr = concat nameStr "Pr" in
--      nameNoSym newNameStr in
--
--    -- Replacer function for public functions
--    let makePubDummy = lam funName. lam tm.
--      recursive let work = lam tm. lam acc.
--        match tm with TmLam t then
--          TmLam {t with body=work t.body (snoc acc t.ident)}
--        else
--          foldl
--            (lam a. lam x. app_ a (nvar_ x))
--            (app_ (nvar_ (renamePub funName))
--            (nvar_ _callCtx)) acc
--      in work tm []
--    in
--    -- Extract dummy functions from the AST, to replace public functions
--    let dummies = _extract isPublic makePubDummy tm in
--    let defDummies = match dummies with [] then unit_ else bindall_ dummies in
--
--    -- Transform program to use call context
--    let trans = _transformCallCtx isVertex _top tm in
--
--    -- Rename public functions
--    let transRenamed = _renameIdents isPublic renamePub trans in
--
--    -- Define initial call context
--    let defCallCtx = nulet_ _callCtx (seq_ []) in
--
--    -- Define initial lookup table
--    let lookupTable = _initLookupTable (cons _top publicFns) callGraph tm in
--    -- AST-ify the lookup table
--    let defLookupTable =
--      nulet_ _lookupTable
--        (seq_ (map
--          (lam r : {id : Expr, path : [a], value : Expr}.
--            record_ [("id", r.id), ("path", seq_ (map symb_ r.path)), ("value", r.value)])
--          lookupTable))
--    in
--
--    -- Compute maximum depth of the decision points
--    let maxDepth =
--      match lookupTable with [] then 0
--      else
--        maxOrElse (lam. error "Expected non-empty lookup table")
--                  subi
--                  (map (lam r : {id : Expr, path : [a], value : Expr}.
--                         length r.path)
--                       lookupTable)
--    in
--    let defMaxDepth = nulet_ _maxDepth (int_ maxDepth) in
--
--    -- AST-ify filter
--    -- recursive let filter = lam p. lam s.
--    --   if (eqi 0 (length s)) then []
--    --   else if p (head s) then
--    --     let f = filter p (tail s)
--    --     in cons (head s) f
--    --   else (filter p (tail s))
--    -- in
--    let filter =
--      -- Local variables
--      let p = nameSym "p" in
--      let s = nameSym "s" in
--      let f = nameSym "f" in
--      nureclets_add _filter
--        (nulam_ p (nulam_ s
--          (if_ (_null (nvar_ s))
--               (seq_ [])
--               (if_ (app_ (nvar_ p) (_head (nvar_ s)))
--                    (bind_ (nulet_ f (appf2_ (nvar_ _filter) (nvar_ p) (_tail (nvar_ s))))
--                           (cons_ (_head (nvar_ s)) (nvar_ f)))
--                    (appf2_ (nvar_ _filter) (nvar_ p) (_tail (nvar_ s)))))))
--      reclets_empty
--    in
--
--    -- AST-ify max (for a non-empty list)
--    -- nlet max = lam cmp. lam seq.
--    --   recursive let work = lam e. lam seq.
--    --     if null seq then e
--    --     else
--    --       let h = head seq in
--    --       let t = tail seq in
--    --       if lti h e then work e t else work h t
--    --    in
--    --    work (head seq) (tail seq)
--    let max =
--      let cmp = nameSym "cmp" in
--      let seq = nameSym "seq" in
--      let work = nameSym "work" in
--      let e = nameSym "e" in
--      let h = nameNoSym "h" in
--      let t = nameNoSym "t" in
--      nulet_ _max
--        (nulam_ cmp (
--          (nulam_ seq
--          (bindall_ [(nureclets_add work
--                       (nulam_ e (nulam_ seq
--                         (if_ (_null (nvar_ seq))
--                           (nvar_ e)
--                           (bindall_ [nulet_ h (_head (nvar_ seq)),
--                                      nulet_ t (_tail (nvar_ seq)),
--                                      if_ (lti_ (appf2_ (nvar_ cmp) (nvar_ h) (nvar_ e)) (int_ 0))
--                                          (appf2_ (nvar_ work) (nvar_ e) (nvar_ t))
--                                          (appf2_ (nvar_ work) (nvar_ h) (nvar_ t))]) )))
--                     reclets_empty),
--                     appf2_ (nvar_ work) (_head (nvar_ seq)) (_tail (nvar_ seq))]))))
--    in
--
--    -- AST-ify isPrefix
--    -- recursive let isPrefix = lam eq. lam s1. lam s2.
--    --   if null s1 then true
--    --   else if null s2 then false
--    --   else if (eq (head s1) (head s2)) then (isPrefix eq (tail s1) (tail s2))
--    --   else false
--    -- in
--    let isPrefix =
--      let eq = nameSym "eq" in
--      let s1 = nameSym "s1" in
--      let s2 = nameSym "s2" in
--      nureclets_add _isPrefix (
--      (nulam_ eq (nulam_ s1 (nulam_ s2
--        (if_ (_null (nvar_ s1))
--             (true_)
--             (if_ (_null (nvar_ s2))
--                  (false_)
--                  (if_ (appf2_ (nvar_ eq) (_head (nvar_ s1)) (_head (nvar_ s2)))
--                       (appf3_ (nvar_ _isPrefix) (nvar_ eq) (_tail (nvar_ s1)) (_tail (nvar_ s2)) )
--                       (false_))) )))))
--      reclets_empty
--    in
--
--    -- AST-ify isSuffix
--    -- let isSuffix = lam eq. lam s1. lam s2.
--    --     isPrefix eq (reverse s1) (reverse s2)
--    -- in
--    let isSuffix =
--      let eq = nameSym "eq" in
--      let s1 = nameSym "s1" in
--      let s2 = nameSym "s2" in
--      nulet_ _isSuffix
--        (nulam_ eq (nulam_ s1 (nulam_ s2
--          (appf3_ (nvar_ _isPrefix)
--                  (nvar_ eq)
--                  (reverse_ (nvar_ s1))
--                  (reverse_ (nvar_ s2)))))) in
--
--    -- Lookup the value for a decision point in a given call context
--    -- let lookup = lam callCtx. lam id.
--    --   let entries = filter (lam t. eqsym t.0 id) lookupTable in
--    --   let entriesSuffix = filter (lam t. isSuffix eqi t.1 callCtx) entries in
--    --   let cmp = lam t1. lam t2. subi (length t1.1) (length t2.1) in
--    --   max cmp entriesSuffix
--    -- in
--    let lookup =
--      let id = nameSym "id" in
--      let entries = nameSym "entries" in
--      let entriesSuffix = nameSym "entriesSuffix" in
--      let entriesLongestSuffix = nameSym "entriesLongestSuffix" in
--      let eqsym = nameSym "eqsym" in
--      let cmp = nameSym "cmp" in
--      let y = nameSym "y" in
--      let t = nameSym "t" in
--      let x = nameSym "x" in
--      let t1 = nameSym "t1" in
--      let t2 = nameSym "t2" in
--      nulet_ _lookup
--        (nulam_ _callCtx (nulam_ id
--        (bindall_ [
--          nulet_ entries (
--              appf2_ (nvar_ _filter)
--                     (nulam_ t (eqsym_ (nvar_ id) (_drecordproj "id" (nvar_ t))))
--                     (nvar_ _lookupTable)),
--          nulet_ eqsym (nulam_ x (nulam_ y (eqsym_ (nvar_ x) (nvar_ y)))),
--          nulet_ entriesSuffix
--               (appf2_ (nvar_ _filter)
--                       (nulam_ t (appf3_ (nvar_ _isSuffix) (nvar_ eqsym) (_drecordproj "path" (nvar_ t)) (nvar_ _callCtx)))
--                       (nvar_ entries)),
--          nulet_ cmp
--            (nulam_ t1 (nulam_ t2
--              (subi_
--                 (length_ (_drecordproj "path" (nvar_ t1)))
--                 (length_ (_drecordproj "path" (nvar_ t2)))))),
--          nulet_ entriesLongestSuffix (appf2_ (nvar_ _max) (nvar_ cmp) (nvar_ entriesSuffix)),
--          _drecordproj "value" (nvar_ entriesLongestSuffix)])))
--    in
--    let defLookup = bindall_ [isPrefix, isSuffix, max, filter, lookup] in
--
--    -- Add a function call to the call context:
--    -- let addCall = lam callCtx. lam lbl.
--    --   if gti (length callCtx) maxDepth then
--    --     snoc (tail callCtx) lbl
--    --   else
--    --     snoc callCtx lbl
--    let defAddCall =
--      let lbl = nameSym "lbl" in
--      nulet_ _addCall (
--        nulam_ _callCtx (nulam_ lbl (
--          if_ (eqi_ (nvar_ _maxDepth) (int_ 0)) (nvar_ _callCtx)
--            (if_ (lti_ (length_ (nvar_ _callCtx)) (nvar_ _maxDepth))
--              (snoc_ (nvar_ _callCtx) (nvar_ lbl))
--              (snoc_ (_tail (nvar_ _callCtx)) (nvar_ lbl))) )))
--    in
--
--    -- Put all the pieces together
--    bindall_ [defLookupTable,
--              defCallCtx,
--              defMaxDepth,
--              defAddCall,
--              defLookup,
--              defDummies,
--              transRenamed]
--
--  -- Extract expressions from the body of identifiers using extractor.
--  -- Consider identifier for which p is true.
--  sem _extract (p : String -> Bool)
--              (extractor : String -> Expr -> Expr) =
--  | TmLet ({body = TmLam lm} & t) ->
--    let res =
--      if p t.ident then
--        let newBody = extractor t.ident t.body in
--        [TmLet {{t with body = newBody} with inexpr=unit_}]
--      else []
--    in concat res (_extract p extractor t.inexpr)
--
--  | TmRecLets t ->
--    let handleLet = lam le : RecLetBinding.
--      if p le.ident then
--        match le.body with TmLam lm then
--          let newBody = extractor le.ident le.body in
--          [{le with body=newBody}]
--        else
--          error (strJoin "" ["Expected identifier ",
--                             le.ident,
--                             " to define a lambda."])
--      else []
--    in
--    let binds =
--      foldl (lam acc. lam b. concat acc (handleLet b)) [] t.bindings
--    in concat [TmRecLets {{t with inexpr=unit_} with bindings=binds}]
--              (_extract p extractor t.inexpr)
--
--  | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (_extract p extractor) tm)
--
--  -- Rename identifiers for which p is true, with renaming function rf
--  sem _renameIdents (p : String -> Bool) (rf : String -> String) =
--  | TmLet ({body = TmLam lm} & t) ->
--    let newIdent =
--      if p t.ident then
--        rf t.ident
--      else
--        t.ident
--    in TmLet {{{t with ident = newIdent}
--                with body = _renameIdents p rf t.body}
--                with inexpr = _renameIdents p rf t.inexpr}
--
--  | TmRecLets t ->
--    let handleLet = lam le : RecLetBinding.
--      -- Defines a public function
--      if p le.ident then
--        match le.body with TmLam lm then
--          let newIdent = rf le.ident in
--          let newBody = _renameIdents p rf le.body in
--          {{le with ident=newIdent} with body=newBody}
--        else
--          error (strJoin "" ["Identifier ",
--                             le.ident,
--                             " expected to refer to a function."])
--      else le
--    in TmRecLets {{t with bindings = map handleLet t.bindings}
--                   with inexpr = _renameIdents p rf t.inexpr}
--
--  | TmVar v ->
--    if p v.ident then
--      TmVar {v with ident = rf v.ident}
--    else TmVar v
--
--  | tm -> smap_Expr_Expr (_renameIdents p rf) tm
--
--  -- Transform program to use call context.
--  -- Considers only identifiers for which p is true.
--  sem _transformCallCtx (p : Name -> Bool) (prev : Name) =
--  -- Add call context as extra argument in function definitions
--  | TmLet ({body = TmLam lm} & t) ->
--    if p t.ident then
--      let newBody =
--        nulam_ _callCtx
--               (TmLam {lm with body = _transformCallCtx p t.ident lm.body})
--      in TmLet {{t with body = newBody}
--                 with inexpr = _transformCallCtx p prev t.inexpr}
--    else TmLet {t with inexpr = _transformCallCtx p prev t.inexpr}
--
--  | TmRecLets t ->
--    let handleLetExpr = lam le : RecLetBinding.
--      if p le.ident then
--        match le.body with TmLam lm then
--          let newBody =
--            nulam_ _callCtx
--              (TmLam {lm with body = _transformCallCtx p le.ident lm.body})
--          in {le with body = newBody}
--        else
--          error "Expected letexpr to have a TmLam in its body"
--      else le
--    in
--    let binds = foldl (lam a. lam b. cons (handleLetExpr b) a) [] t.bindings in
--    TmRecLets {{t with bindings = binds}
--                with inexpr = _transformCallCtx p prev t.inexpr}
--   -- Insert call context as extra argument in function calls (not recursive ones)
--  | TmLet ({body = TmApp a} & t) ->
--    let id = symb_ (_getSym t.ident) in
--    let resBody = _handleAppsCallCtx _transformCallCtx p id prev (TmApp a) in
--    TmLet {{t with body = resBody}
--            with inexpr = _transformCallCtx p prev t.inexpr}
--  -- Replace holes with lookups
--  | TmLet ({body = TmHole h} & t) ->
--    let id = symb_ (_getSym t.ident) in
--    let lookupHole = app_ (app_ (nvar_ _lookup) (nvar_ _callCtx)) id in
--    TmLet {{t with body = lookupHole}
--            with inexpr = _transformCallCtx p prev t.inexpr}
--
--  | tm -> smap_Expr_Expr (_transformCallCtx p prev) tm
--
--  -- Initialise lookup table as a list of triples (id, path, startGuess)
--  sem _initLookupTable (publicFns : [Name]) (g : CallGraph) =
--  | tm ->
--    let holeInfo = _holeInfo tm in
--    let zip = zipWith (lam a. lam b. (a, b)) in
--    foldl
--      (lam acc. lam t : {fun : Name, hole : {startGuess : Expr, depth : Int}, id : Expr}.
--         let fun = t.fun in
--         let hole = t.hole in
--         let depth =
--           match hole.depth with TmConst {val = CInt n} then n.val
--           else error "Depth must be a constant integer"
--         in
--         let paths = eqPaths g fun depth publicFns in
--         let idPathValInfo =
--           map (lam path. {id=t.id, path=path, value=hole.startGuess})
--               paths
--         in concat acc idPathValInfo)
--      [] holeInfo
--
--  -- Return a list of records with keys (function name, hole, id) for all holes
--  sem _holeInfo =
--  | tm -> _holeInfo2 _top tm
--
--  sem _holeInfo2 (prev : Name) =
--  | TmLet ({body = TmHole h} & t) ->
--    let id = _getSym t.ident in
--    concat [{fun=prev, hole=h, id=symb_ id}]
--           (_holeInfo2 prev t.inexpr)
--
--  | TmLet ({body = TmLam lm} & t) ->
--    let resBody = _holeInfo2 t.ident lm.body in
--    concat resBody (_holeInfo2 prev t.inexpr)
--
--  | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (_holeInfo2 prev) tm)
--end
--
---- TODO(dlunde,2020-09-29): Why does the include order matter here? If I place
---- MExprPrettyPrint first, I get a pattern matching error.
--lang PPrintLang = MExprPrettyPrint + HolePrettyPrint
--
--lang TestLang = MExpr + ContextAwareHoles + PPrintLang + MExprANF + HoleANF
--  + MExprSym + MExprEq
--
--mexpr
--
--use TestLang in
--
--let anf = compose normalizeTerm symbolize in
--
---- Enable/disable printing
--let printEnabled = false in
--let print = if printEnabled then print else lam x. x in
--
---- Enable/disable eval
--let evalEnabled = false in
--let evalE = lam expr. lam expected.
--  if evalEnabled then eval {env = builtinEnv} expr else expected in
--
---- Prettyprinting
--let pprint = lam ast.
--  print "\n\n";
--  print (expr2str ast);
--  print "\n\n" in ();
--
---- Perform transform tests
--let dprintTransform = lam ast.
--  -- Symbolize
--  let ast = symbolize ast in
--  let anfast = anf ast in
--  -- Label applications
--  print "\n-------------- BEFORE ANF --------------";
--  pprint ast;
--  print "-------------- AFTER ANF --------------";
--  pprint anfast;
--  print "-------------- AFTER TRANSFORMATION --------------";
--  let ast = transform [] anfast in
--  pprint ast;
--  print "-------------- END OF TRANSFORMED AST --------------";
--  ast
--in
--let testTransform =
--  lam r : {ast : Expr, expected : Expr, vs : [String], calls : [(String, String)]}.
--  let tast = dprintTransform r.ast in
--  utest evalE tast r.expected with r.expected using eqExpr in ()
--in
--
---- Perform call graph tests
--let callGraphTests = lam ast. lam strVs : [String]. lam strEdgs.
--  -- Convert to graph with string nodes
--  let toStr = lam ng.
--    digraphAddEdges
--      (map (lam t : DigraphEdge v l. (nameGetStr t.0, nameGetStr t.1, t.2))
--           (digraphEdges ng))
--      (digraphAddVertices (map nameGetStr (digraphVertices ng))
--                          (digraphEmpty eqString eqsym))
--  in
--  let g = toCallGraph ast in
--  let sg = toStr g in
--
--  let x : [String] = digraphVertices sg in
--  digraphPrintDot sg (lam x. x) (lam x. int2string (sym2hash x));
--  utest strVs with x using setEqual eqString in
--
--  let es = digraphEdges sg in
--  utest length es with length strEdgs in
--  iter
--    (lam t : (String, String). (utest digraphIsSuccessor t.1 t.0 sg with true in ()))
--    strEdgs
--in
--let testCallgraph =
--  lam r : {ast : Expr, expected : Expr,
--           vs : [String], calls : [(String, String)]}.
--  callGraphTests (anf r.ast) r.vs r.calls
--in
--
---- 1
--let constant = {
--  ast = int_ 1,
--  expected = int_ 1,
--  vs = ["top"],
--  calls = []
--} in
--
---- let foo = lam x. x in ()
--let identity = {
--  ast = ulet_ "foo" (ulam_ "x" (var_ "x")),
--  expected = unit_,
--  vs = ["top", "foo"],
--  calls = []
--} in
--
---- let foo = lam x. x in
---- let bar = lam x. foo x in ()
--let funCall = {
--  ast = bind_ (ulet_ "foo" (ulam_ "x" (var_ "x")))
--              (ulet_ "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))),
--  expected = unit_,
--  vs = ["top", "foo", "bar"],
--  calls = [("bar", "foo")]
--} in
--
---- let foo = lam x. x in
---- let bar = lam x. addi (foo x) (foo x) in
---- bar 1
--let ast =
--  bindall_ [identity.ast,
--            ulet_ "bar" (ulam_ "x" (addi_ (app_ (var_ "foo") (var_ "x"))
--                                         (app_ (var_ "foo") (var_ "x")))),
--            (app_ (var_ "bar") (int_ 1))] in
--let callSameFunctionTwice = {
--  ast = ast,
--  expected = int_ 2,
--  vs = ["top", "foo", "bar"],
--  calls = [("top", "bar"), ("bar", "foo"), ("bar", "foo")]
--} in
--
----let foo = lam x. lam y. addi x y in
----foo 1 2
--let twoArgs = {
--  ast = bind_
--          (ulet_ "foo"
--            (ulam_ "x" (ulam_ "y" (addi_ (var_ "x") (var_ "y")))))
--          (appf2_ (var_ "foo") (int_ 1) (int_ 2)),
--  expected = int_ 3,
--  vs = ["top", "foo"],
--  calls = [("top", "foo")]
--} in
--
---- let foo = lam a. lam b.
----     let bar = lam x. addi b x in
----     let b = 3 in
----     addi (bar b) a
---- in ()
--let innerFun = {
--  ast = ulet_ "foo" (ulam_ "a" (ulam_ "b" (
--          let bar = ulet_ "bar" (ulam_ "x"
--                         (addi_ (var_ "b") (var_ "x"))) in
--          let babar = ulet_ "b" (int_ 3) in
--          bind_ bar (
--          bind_ babar (
--            addi_ (app_ (var_ "bar")
--                        (var_ "b"))
--                  (var_ "a")))))),
--  expected = unit_,
--  vs = ["top", "foo", "bar"],
--  calls = [("foo", "bar")]
--} in
--
---- let foo = lam x. x in
---- let a = foo 1 in
---- a
--let letWithFunCall = {
--  ast = let foo = ulet_ "foo" (ulam_ "x" (var_ "x")) in
--        let a = ulet_ "a" (app_ (var_ "foo") (int_ 1)) in
--        bind_ (bind_ foo a) (var_ "a"),
--  expected = int_ 1,
--  vs = ["top", "foo"],
--  calls = [("top", "foo")]
--} in
--
---- recursive let factorial = lam n.
----     if eqi n 0 then
----       1
----     else
----       muli n (factorial (subi n 1))
---- in
---- factorial 4
--let factorial = {
--  ast = bind_
--    (ureclets_add "factorial"
--           (lam_ "n" (tyint_)
--                 (if_ (eqi_ (var_ "n") (int_ 0))
--                      (int_ 1)
--                      (muli_ (var_ "n")
--                             (app_ (var_ "factorial")
--                                   (subi_ (var_ "n")
--                                          (int_ 1))))))
--     reclets_empty)
--    (app_ (var_ "factorial") (int_ 2)),
--  expected = int_ 2,
--  vs = ["top", "factorial"],
--  calls = [("top", "factorial"), ("factorial", "factorial")]
--} in
--
---- recursive
----     let even = lam x.
----         if eqi x 0
----         then true
----         else odd (subi x 1)
----     let odd = lam x.
----         if eqi x 1
----         then true
----         else even (subi x 1)
---- in even 4
--let evenOdd ={
--  ast = bind_
--    (ureclets_add "even" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 0))
--                                       (true_)
--                                       (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
--    (ureclets_add "odd" (ulam_ "x" (if_ (eqi_ (var_ "x") (int_ 1))
--                                      (true_)
--                                      (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
--     reclets_empty))
--    (app_ (var_ "even") (int_ 2)),
--  expected = true_,
--  vs = ["top", "even", "odd"],
--  calls = [("top", "even"), ("even", "odd"), ("odd", "even")]
--} in
--
---- let bar = lam y. y in
---- let foo = lam f. lam x. f x in -- cannot see that foo calls bar
---- foo bar 1
--let hiddenCall = {
--  ast = bindall_ [
--          ulet_ "bar" (ulam_ "y" (var_ "y")),
--          ulet_ "foo" (ulam_ "f" (ulam_ "x" (app_ (var_ "f") (var_ "x")))),
--          appf2_ (var_ "foo") (var_ "bar") (int_ 1)],
--  expected = int_ 1,
--  vs = ["top", "foo", "bar"],
--  calls = [("top", "foo")]
--} in
--
---- let foo = lam x. lam y.
----   if (<hole>) then x
----   else let d = <hole> in addi x d
---- in foo 42 3
--let hole1 = {
--  ast =
--    bind_
--      (ulet_ "foo"
--           (ulam_ "x" (ulam_ "y" (if_ ((hole_ true_ (int_ 2))) (var_ "x")
--                           (bind_ (ulet_ "d" (hole_ (int_ 1) (int_ 2)))
--                                  (addi_ (var_ "x") (var_ "d")))))))
--      (appf2_ (var_ "foo") (int_ 42) (int_ 3)),
--  expected = int_ 42,
--  vs = ["top", "foo"],
--  calls = [("top", "foo")]
--} in
--
----let foo = lam x.
----          let d1 = <hole> in
----          let bar = lam y.
----                      let d2 = <hole> in
----                      addi d1 (addi d2 y) in
----          bar 1
----in foo 1
--let hole2 = {
--  ast =
--    bind_
--      (ulet_ "foo"
--        (ulam_ "x" (bind_
--          ((bind_ (ulet_ "d1" (hole_ (int_ 1) (int_ 2)))
--             (ulet_ "bar"
--               (ulam_ "y" (bind_ (ulet_ "d2" (hole_ (int_ 3) (int_ 2)))
--                                 (addi_  (var_ "d1") (addi_ (var_ "d2") (var_ "y"))))))))
--          (app_ (var_ "bar") (int_ 1)))
--        ))
--      (app_ (var_ "foo") (int_ 1)),
--   expected = int_ 5,
--   vs = ["top", "foo", "bar"],
--   calls = [("top", "foo"), ("foo", "bar")]
--} in
--
---- let bar = lam x.
----   let h = TmHole {depth = 2, startGuess = true} in
----   if h then x else (addi x 1)
---- in
---- recursive let foo = lam x.
----   if eqi x 1 then
----     foo 2
----   else
----     bar x
---- in
---- let b1 = bar 1 in
---- let b2 = bar 2 in
---- foo 1
--let hole3 = {
--  ast = bindall_ [ulet_ "bar" (ulam_ "x"
--                    (bind_ (ulet_ "h" (hole_ true_ (int_ 2)))
--                           (if_ (var_ "h")
--                                (var_ "x")
--                                (addi_ (var_ "x") (int_ 1))))),
--                  ureclets_add
--                    "foo" (ulam_ "x"
--                      (if_ (eqi_ (var_ "x") (int_ 1))
--                           (app_ (var_ "foo") (int_ 2))
--                           (app_ (var_ "bar") (var_ "x"))))
--                  reclets_empty,
--                  ulet_ "b1" (app_ (var_ "bar") (int_ 1)),
--                  ulet_ "b2" (app_ (var_ "bar") (int_ 2)),
--                  app_ (var_ "foo") (int_ 1)],
--  expected = int_ 2,
--  vs = ["top", "bar", "foo"],
--  calls = [("top", "foo"), ("top", "bar"), ("top", "bar"), ("foo", "foo"), ("foo", "bar")]
--} in
--
--let allTests = [
--    hole1
--  , hole2
--  ,  hole3
--  , constant
--  , identity
--  , funCall
--  , callSameFunctionTwice
--  , innerFun
--  , letWithFunCall
--  , factorial
--  , evenOdd
--  , hiddenCall
--] in
--
--let tTests = [hole1, hole2, hole3] in
--let cgTests = allTests in
--
--map testTransform tTests;
--map testCallgraph cgTests;
--
--()

