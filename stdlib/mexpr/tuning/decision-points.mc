include "mexpr/mexpr.mc"
include "mexpr/pprint.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/boot-parser.mc"
include "mexpr/utesttrans.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"
include "digraph.mc"
include "string.mc"
include "eq-paths.mc"
include "name.mc"
include "hashmap.mc"
include "eqset.mc"
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

type Binding = {ident : Name, body : Expr}
let _handleLetVertex = use LamAst in
  lam f.lam letexpr : Binding.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

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
    concat
      (_handleLetVertex _findVertices {ident = t.ident, body = t.body})
      (_findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam acc. lam b : RecLetBinding.
               concat acc
                 (_handleLetVertex _findVertices {ident = b.ident, body = b.body}))
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
      let handleBinding = lam g. lam b : RecLetBinding.
        match b with { body = TmLam { body = lambody }, ident = ident } then
          _findEdges g ident lambody
        else
          _findEdges g prev b.body
      in foldl (lam g. lam b. digraphUnion g (handleBinding g b)) cg t.bindings
    in _findEdges res prev t.inexpr

  | tm ->
    sfold_Expr_Expr digraphUnion cg (smap_Expr_Expr (_findEdges cg prev) tm)
end

--------------------------------------------
-- Language fragments for decision points --
--------------------------------------------

let decisionPointsKeywords =
[ "HoleBool"
, "HoleIntRange"
]

let _lookup = lam s : String. lam m : Map String a.
  mapLookupOrElse (lam. error (concat s " not found")) s m

let _expectConstInt = lam s. lam i.
  use IntAst in
  match i with TmConst {val = CInt {val = i}} then i
  else error (concat "Expected a constant integer: " s)

lang HoleAst = IntAst + ANF + KeywordMaker
  syn Hole =

  syn Expr =
  | TmHole {init : Expr,
            depth : Int,
            ty : Type,
            info : Info,
            hole : Hole}

  sem ty =
  | TmHole {ty = ty} -> ty

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmHole h -> TmHole h

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmHole h -> acc

  sem isAtomic =
  | TmHole _ -> false

  sem pprintCode (indent : Int) (env : SymEnv) =
  | TmHole h ->
    match pprintCode indent env h.init with (env, startStr) then
      (env,
         join ["boolHole ", startStr, " ", int2string h.depth])
    else never

  sem isValue =
  | TmHole _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmHole ({init = init} & t) ->
    k (TmHole {t with init = normalizeTerm t.init})

  sem isKeyword =
  | TmHole _ -> true

  sem _mkHole (info : Info) (hty : Type) (hole : Map String Expr -> Hole)
              (validate : Expr -> Expr) =
  | arg ->
    use RecordAst in
    match arg with TmRecord {bindings = bindings} then
      let bindings = mapFromList cmpString
        (map (lam t : (SID, Expr). (sidToString t.0, t.1))
           (mapBindings bindings)) in
      let init = _lookup "init" bindings in
      let depth = _lookup "depth" bindings in
      validate
        (TmHole { init = init
                , depth = _expectConstInt "depth" depth
                , info = info
                , ty = hty
                , hole = hole bindings})
    else error "Expected record type"
end

-- A Boolean decision point.
lang HoleBoolAst = BoolAst + HoleAst
  syn Hole =
  | BoolHole {}

  sem sample =
  | BoolHole {} ->
    randElem [true_, false_]

  sem fromString =
  | "true" -> true
  | "false" -> false

  sem matchKeywordString (info : Info) =
  | "HoleBool" ->
    Some (1,
      let validate = lam expr.
        match expr with TmHole {init = init} then
          match init with TmConst {val = CBool _} then expr
          else error "Inital value not a constant Boolean"
        else error "Not a decision point" in

      lam lst. _mkHole info tybool_ (lam. BoolHole {}) validate (get lst 0))
end

-- An integer decision point (range of integers).
lang HoleIntRangeAst = IntAst + HoleAst
  syn Hole =
  | IntRange {min : Int,
              max : Int}

  sem sample =
  | IntRange {min = min, max = max} ->
    int_ (randIntU min (addi max 1))

  sem matchKeywordString (info : Info) =
  | "HoleIntRange" ->
    Some (1,
      let validate = lam expr.
        match expr
        with TmHole {init = TmConst {val = CInt {val = i}},
                     hole = IntRange {min = min, max = max}}
        then
          if and (leqi min i) (geqi max i) then expr
          else error "Initial value is not within range"
        else error "Not an integer decision point" in

      lam lst. _mkHole info tyint_
        (lam m.
           let min = _expectConstInt "min" (_lookup "min" m) in
           let max = _expectConstInt "max" (_lookup "max" m) in
           if leqi min max then
             IntRange {min = min, max = max}
           else error (join ["Empty domain: ",
                           int2string min, "..", int2string max]))
        validate (get lst 0))
end

let holeBool_ = use HoleBoolAst in
  lam init. lam depth.
  TmHole { init = init
         , depth = depth
         , ty = tybool_
         , info = NoInfo ()
         , hole = BoolHole {}}

------------------------------
-- Call context environment --
------------------------------

-- Maintains call context information necessary for program transformations.
-- Except for 'hole2idx' and 'count', the information is static.
type CallCtxEnv = {

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

  -- Maps a decision point and a call path to a unique integer.
  -- TODO(Linnea, 2021-04-21): Once we have 'smapAccumL_Expr_Expr', this
  -- shouldn't be a reference.
  hole2idx: Ref (Map Name (Map[Name] Int)),

  -- Maps an index to its decision point. The key set is the union of the value
  -- sets of 'hole2idx'.
  -- OPT(Linnea, 2021-05-19): Consider other representations, as the same
  -- expression may be repeated many times.
  idx2hole: Ref ([Expr])
}

-- Create a new name from a prefix string and name.
let _newNameFromStr : Str -> Name -> Name = lam prefix. lam name.
  nameSym (concat prefix (nameGetStr name))
-- Get the name of the incoming variable from a name.
let _incVarFromName = _newNameFromStr "inc_"

-- Compute the initial call context environment for a program.
let callCtxInit : [Name] -> CallGraph -> Expr -> CallCtxEnv =
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
    , idx2hole = ref []
    }

-- Returns the binding of a function name, or None () if the name is not a node
-- in the call graph.
let callCtxFunLookup : Name -> CallCtxEnv -> Option Name =
  lam name : Name. lam env : CallCtxEnv.
    match env with { fun2inc = fun2inc } then
      hashmapLookup {eq = _eqn, hashfn = _nameHash} name fun2inc
    else never

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxFun2Inc : Name -> CallCtxEnv -> Name = lam name. lam env.
  optionGetOrElse (lam. error "fun2inc lookup failed")
                  (callCtxFunLookup name env)

-- Get the incoming variable name of an edge label, giving an error if the edge
-- is not part of the call graph.
let callCtxLbl2Inc : Name -> CallCtxEnv -> Name =
  lam lbl : Name. lam env : CallCtxEnv.
    match env with { lbl2inc = lbl2inc } then
      optionGetOrElse (lam. error "lbl2inc lookup failed")
                      (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                     lbl lbl2inc)
    else never

-- Get the count of an edge label, giving an error if the edge is not part of
-- the call graph.
let callCtxLbl2Count : Name -> CallCtxEnv -> Int =
  lam lbl : Name. lam env : CallCtxEnv.
    match env with { lbl2count = lbl2count } then
      optionGetOrElse (lam. error "lbl2count lookup failed")
                      (hashmapLookup {eq = _eqn, hashfn = _nameHash}
                                     lbl lbl2count)
    else never

-- Get all the incoming variable names of the program.
let callCtxIncVarNames : CallCtxEnv -> [Name] = lam env : CallCtxEnv.
  match env with { fun2inc = fun2inc } then
    hashmapValues {eq = _eqn, hashfn = _nameHash} fun2inc
  else never

-- Lookup the internal name of a public function.
let callCtxPubLookup : Name -> CallCtxEnv -> Option Name = lam name. lam env.
  match env with { pub2internal = pub2internal } then
    hashmapLookup {eq = _eqn, hashfn = _nameHash} name pub2internal
  else never

let callCtxAddHole : Expr -> Name -> [[Name]] -> CallCtxEnv -> CallCtxEnv =
  lam hole. lam name. lam paths. lam env : CallCtxEnv.
    match env with { hole2idx = hole2idx, idx2hole = idx2hole} then
    let countInit = length (deref idx2hole) in
    match
      foldl
      (lam acc. lam k.
         match acc with (m, i) then (mapInsert k i m, addi i 1)
         else never)
      (mapEmpty _cmpPaths, countInit)
      paths
    with (m, count) then
      let n = length paths in
      utest n with subi count countInit in
      modref idx2hole (concat (deref idx2hole) (create n (lam. hole)));
      modref hole2idx (mapInsert name m (deref hole2idx));
      env
    else never
  else dprintLn env; never

let callCtxHole2Idx : Name -> [Name] -> CallCtxEnv -> Int =
  lam name. lam path. lam env : CallCtxEnv.
    match env with { hole2idx = hole2idx } then
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
utest
  _appGetCallee (appf3_ (nvar_ _x) true_ (nvar_ _y) (int_ 4))
with Some _x using optionEq nameEq
utest
  _appGetCallee (addi_ (nvar_ _x) (int_ 3))
with None () using optionEq nameEq

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
let t =
  utest _appSetCallee
        (appf2_ (nvar_ _x) (nvar_ _y) (int_ 4)) _y
  with  (appf2_ (nvar_ _y) (nvar_ _y) (int_ 4))
  using use MExprEq in eqExpr in ()

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
let t =
  utest
    _lamWithBody (lam args.
                    match args with [x, y, z] then
                      muli_ (nvar_ x) (nvar_ y)
                    else error "Test failed")
                 (nulam_ _x (nulam_ _y (nulam_ _z (addi_ (int_ 1) (int_ 1)))))
  with (nulam_ _x (nulam_ _y (nulam_ _z (muli_ (nvar_ _x) (nvar_ _y)))))
  using use MExprEq in eqExpr in ()

-- Generate code for looking up a value of a decision point depending on its
-- call history
let _lookupCallCtx : Lookup -> Name -> Name -> CallCtxEnv -> [[Name]] -> Expr =
  use MatchAst in use NeverAst in
    lam lookup. lam holeId. lam incVarName. lam env : CallCtxEnv. lam paths.
      match env with { lbl2inc = lbl2inc } then
        -- TODO(Linnea, 2021-04-21): Represent paths as trees, then this
        -- partition becomes trivial
        let partitionPaths : [[Name]] -> ([Name], [[[Name]]]) = lam paths.
          let startVals = foldl (lam acc. lam p.
                                   eqsetInsert _eqn (head p) acc)
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
                        let iv = callCtxLbl2Inc n env in
                        let count = callCtxLbl2Count n env in
                        matchex_ (deref_ (nvar_ incVarName)) (pint_ count)
                                 (work iv (map tail (get partition i)) (cons n acc)))
                     startVals
              in
              let defaultVal =
                if eqi (length nonEmpty) (length paths) then never_
                else lookup (callCtxHole2Idx holeId acc env)
              in
              matchall_ (snoc branches defaultVal)
            else never
          in
        work incVarName (map reverse paths) []
      else never

-- Helper for creating a hidden equivalent of a public function and replace the
-- public function with a forwarding call to the hidden function.
type Binding = {ident : Name, body : Expr}
let _forwardCall : Name -> (Expr -> Expr) -> Binding -> (Binding, Binding) =
  lam local. lam f. lam bind : Binding.
    let fwdVar = _fwdVarFromName bind.ident in
    let newBody = lam args.
      bind_ (nulet_ fwdVar (appSeq_ (nvar_ local) (map nvar_ args)))
      (nvar_ fwdVar)
    in
    let localFun = {{bind with ident = local}
                          with body = f bind.body}
    in (localFun, {bind with body = _lamWithBody newBody bind.body})

type LookupTable = Map Int Expr

let _table = nameSym "table"
let _argv = nameSym "argv"
  -- argv_
  -- use Argv const node
  --match find (lam n. eqString "argv" (nameGetStr n)) builtinNames with Some n
  --then n else error "argv name not found"

--
lang FlattenHoles = Ast2CallGraph + HoleAst + IntAst + MatchAst + NeverAst
                    -- Included for debugging
                    + MExprPrettyPrint

  -- Transform a program with decision points. All decision points will be
  -- eliminated and replaced by lookups in a static table. One reference per
  -- function tracks which function that latest called that function, thereby
  -- maintaining call history.
  sem flatten (publicFns : [Name]) =
  | t ->
    let pub2priv = _nameMapInit publicFns identity _privFunFromName in
    let tm = _replacePublic pub2priv t in
    let env = callCtxInit publicFns (toCallGraph tm) tm in
    -- Declare the incoming variables
    let incVars =
      bindall_ (map (lam incVarName. nulet_ incVarName (ref_ (int_ _incUndef)))
                    (callCtxIncVarNames env))
    in
    let tm = bind_ incVars tm in
    let lookup = lam i. get_ (nvar_ _table) (int_ i) in
    let prog = _maintainCallCtx lookup env _callGraphTop tm in
    (_wrapArgv env prog, _initAssignments env t, deref env.idx2hole)

  -- Find the initial mapping from decision points to values
  sem _initAssignments (env : CallCtxEnv) =
  | tm ->
    let idx2hole = deref env.idx2hole in
    mapFromList subi
      (mapi (lam i. lam hole.
         match hole with TmHole { init = init } then (i, init)
         else error "Not a hole term")
         idx2hole)

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
  | TmLet ({ body = TmLam lm } & t) & tm ->
    match hashmapLookup {eq = _eqn, hashfn = _nameHash} t.ident pub2priv
    with Some local then
      match _forwardCall local (_replacePublic pub2priv) {ident = t.ident, body = t.body}
      with (priv, pub) then
        let pubAndRest =
          TmLet {{{t with ident = pub.ident}
                     with body = pub.body}
                     with inexpr = _replacePublic pub2priv t.inexpr}
        in TmLet {{{t with ident = priv.ident}
                      with body = priv.body}
                      with inexpr = pubAndRest}
      else never
    else TmLet {{t with inexpr = _replacePublic pub2priv t.inexpr}
                   with body = _replacePublic pub2priv t.body}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds = foldl
      (lam acc : [RecLetBinding]. lam bind : RecLetBinding.
        match bind with { body = TmLam lm } then
          match hashmapLookup {eq = _eqn, hashfn =_nameHash} bind.ident pub2priv
          with Some local then
            match _forwardCall local (_replacePublic pub2priv) {ident = bind.ident, body = bind.body}
            with (privBind, pubBind) then
              concat [{{bind with ident = privBind.ident}
                             with body = privBind.body},
                      {{bind with ident = pubBind.ident}
                             with body = pubBind.body}] acc
            else never
          else cons bind acc
        else cons bind acc)
      [] bindings
    in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _replacePublic pub2priv t.inexpr}

  | tm -> smap_Expr_Expr (_replacePublic pub2priv) tm

  -- Maintain call context history by updating incoming variables before
  -- function calls.
  sem _maintainCallCtx (lookup : Lookup) (env : CallCtxEnv) (cur : Name) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    -- NOTE(Linnea, 2021-01-29): ANF form means no recursion necessary for the
    -- application node (can only contain values)
    let le = TmLet {t with inexpr = _maintainCallCtx lookup env cur t.inexpr} in
    match _appGetCallee (TmApp a) with Some callee then
      match callCtxFunLookup callee env
      with Some iv then
        -- Set the incoming var of callee to current node
        let count = callCtxLbl2Count t.ident env in
        let update = modref_ (nvar_ iv) (int_ count) in
        bind_ (nulet_ (nameSym "") update) le
      else le
    else le

  -- Decision point: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
     match env with
      { callGraph = callGraph, publicFns = publicFns }
     then
       let paths = eqPaths callGraph cur depth publicFns in
       let env = callCtxAddHole t.body ident paths env in
       let iv = callCtxFun2Inc cur env in
       let lookupCode = _lookupCallCtx lookup ident iv env paths in
       TmLet {{t with body = lookupCode}
                 with inexpr = _maintainCallCtx lookup env cur t.inexpr}
     else never

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody =
      match callCtxFunLookup t.ident env with Some _
      then t.ident
      else cur
    in TmLet {{t with body = _maintainCallCtx lookup env curBody t.body}
                 with inexpr = _maintainCallCtx lookup env cur t.inexpr}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds =
      map (lam bind : RecLetBinding.
        match bind with { body = TmLam lm } then
          let curBody =
            match callCtxFunLookup bind.ident env with Some _
            then bind.ident
            else cur
          in {bind with body = _maintainCallCtx lookup env curBody bind.body}
        else {bind with body = _maintainCallCtx lookup env cur bind.body})
      bindings
    in TmRecLets {{t with bindings = newBinds}
                     with inexpr = _maintainCallCtx lookup env cur inexpr}
  | tm ->
    smap_Expr_Expr (_maintainCallCtx lookup env cur) tm

  sem _wrapArgv (env : CallCtxEnv) =
  | tm ->
    -- TODO: apply a convert function on each argument depending on the type of
    -- the hole
    use BootParser in
    let impl = parseMExprString [] "
    let head = lam seq. get seq 0 in
    let tail = lam seq. subsequence seq 1 (subi (length seq) 1) in
    let null = lam seq. eqi 0 (length seq) in
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

    let string2bool = lam s : String.
      match s with \"true\" then true
      else match s with \"false\" then false
      else error (concat \"Cannot be converted to Bool: \" s)
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

    ()
    " in

    let getName : String -> Expr -> Name = lam s. lam expr.
      match findName s expr with Some n then n
      else error (concat "not found: " s) in

    let zipWithName = getName "zipWith" impl in
    let string2boolName = getName "string2bool" impl in
    let string2intName = getName "string2int" impl in

    let convertFuns = map (lam h.
      match h with TmHole {ty = TyBool _} then string2boolName
      else match h with TmHole {ty = TyInt _} then string2intName
      else dprintLn h; error "Unsupported type"
    ) (deref env.idx2hole) in

    let x = nameSym "x" in
    let y = nameSym "y" in
    let doConvert = nulam_ x (nulam_ y (app_ (nvar_ x) (nvar_ y))) in

    matchex_
      (splitat_ argv_ (subi_ (length_ argv_) (int_ (length convertFuns))))
      (ptuple_ [pvarw_, npvar_ _table])
      (bindall_
        [ impl
        , nulet_ _table
          (appf3_ (nvar_ zipWithName) doConvert
            (seq_ (map nvar_ convertFuns)) (nvar_ _table))
        , tm])
end

lang Holes =
  HoleAst + HoleBoolAst + HoleIntRangeAst + FlattenHoles

lang MExprHoles = Holes + MExpr + MExprANF

lang TestLang = MExprHoles + MExprSym + MExprEq

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

----------------------
-- Call graph tests --
----------------------

type CallGraphTest = {ast : Expr, expected : Expr, vs : [String],
                      calls : [(String, String)]} in

let doCallGraphTests = lam r : CallGraphTest.
  let tests = lam ast. lam strVs : [String]. lam strEdgs : [(String, String)].
    let toStr = lam ng.
      digraphAddEdges
        (map (lam t : DigraphEdge Name Name.
           (nameGetStr t.0, nameGetStr t.1, t.2)) (digraphEdges ng))
           (digraphAddVertices (map nameGetStr (digraphVertices ng))
                               (digraphEmpty eqString _eqn))
    in
    let sg = toStr (toCallGraph ast) in

    utest eqsetEqual eqString strVs (digraphVertices sg) with true in

    let es = digraphEdges sg in
    utest length es with length strEdgs in
    map (lam t : (String, String).
      utest digraphIsSuccessor t.1 t.0 sg with true in ()) strEdgs
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


let cgTests =
[ constant
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
    match flatten pub ast with (prog, _) then
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
let ast = bindall_ [  nulet_ funA (ulam_ ""
                        (bind_ (nulet_ h (holeBool_ (int_ 0) 2))
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

match flatten [funB, funC] ast with (prog, table) then

  let evalWithArgv = lam table : [Expr]. lam ast : Expr. lam ext : Expr.
    let astExt =
      match ast with TmMatch ({thn = thn} & t) then
        TmMatch {t with thn = bind_ thn ext}
      else dprintLn ast; error "Expected match expression"
    in
    printLn "\n----- AFTER TEST TRANSFORMATION -----\n";
    printLn (expr2str ast);
    eval { env = mapEmpty nameCmp } ast
  in

  --let idxs = map (lam t : ([Name], Int). t.1) (mapBindings m) in
  let idxs = mapi (lam i. lam. i) (mapBindings table) in
  let table = mapi (lam i. lam. int_ (addi 1 i)) idxs in

  let eval = evalWithArgv table in

  -- Path 1: C -> B (1)-> A
  utest eval prog (
    app_ (nvar_ funC) true_
  ) with int_ 1 using eqExpr in

  -- Path 2: B (1)-> A
  utest eval prog (
    appf2_ (nvar_ funB) true_ false_
  ) with int_ 2 using eqExpr in

  -- Path 3: B -> B (1)-> A
  utest eval prog (
    appf2_ (nvar_ funB) true_ true_
  ) with int_ 3 using eqExpr in

  -- Path 4: C -> B (2)-> A
  utest eval prog (
    app_ (nvar_ funC) false_
  ) with int_ 4 using eqExpr in

  -- Path 5: B (2)-> A
  utest eval prog (
    appf2_ (nvar_ funB) false_ false_
  ) with int_ 5 using eqExpr in

  -- Path 5 again
  utest eval prog (
    bind_ (nulet_ (nameSym "") (app_ (nvar_ funC) false_))
          (appf2_ (nvar_ funB) false_ false_)
  ) with int_ 5 using eqExpr in

  -- Path 6: B -> B (2)-> A
  -- unreachable

()

else never
