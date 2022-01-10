include "mexpr/mexpr.mc"
include "mexpr/pprint.mc"
include "mexpr/eq.mc"
include "mexpr/utesttrans.mc"
include "mexpr/anf.mc"
include "mexpr/ast-builder.mc"

include "sys.mc"
include "digraph.mc"

include "ast.mc"
include "call-graph.mc"
include "eq-paths.mc"
include "name-info.mc"
include "prefix-tree.mc"

-- Implements context expansion for a program with holes.

let _nameMapInit : [a] -> (a -> Name) -> (a -> v) -> Map Name v =
  lam items. lam toKey. lam toVal.
    foldl (lam acc. lam e. mapInsert (toKey e) (toVal e) acc)
      (mapEmpty nameCmp)
      items

------------------------------
-- Call context environment --
------------------------------

type Edge = (NameInfo, NameInfo, NameInfo)
type Path = [Edge]

let edgeCmp = lam e1 : Edge. lam e2 : Edge.
  nameInfoCmp e1.2 e2.2

let _threadPoolNbrThreadsStr = "threadPoolNbrThreads"
let _threadPoolId2idxStr = "threadPoolId2idx"

-- Maintains call context information necessary for program transformations.
type CallCtxEnv = {

  -- Call graph of the program. Functions are nodes, function calls are edges.
  callGraph: CallGraph,

  -- List of public functions of the program (possible entry points in the call
  -- graph)
  publicFns: [NameInfo],

  -- Maps names of functions to the name of its incoming variable. The incoming
  -- variables keep track of the execution path during runtime.
  fun2inc: Map Name Name,

  -- Maps edge labels in the call graph to the incoming variable name of its
  -- from-node.
  lbl2inc: Map Name Name,

  -- Each node in the call graph assigns a per-node unique integer to each
  -- incoming edge. This map maps an edge to the count value of its destination
  -- node.
  lbl2count: Map Name Int,

  -- Whether or not the program runs with a thread pool. If the identifiers
  -- 'threadPoolNbrThreads', 'threadPoolId2idx' are defined in the program, then
  -- the 'threadPoolInfo' contains the binding of 'threadPoolNbrThreads' and the
  -- name of threadPoolId2idx, otherwise None ().
  threadPoolInfo: Option (Int, Name),

  -- Maps a hole and a call path to a unique integer.
  hole2idx: Map NameInfo (Map [NameInfo] Int),

  -- Maps an index to its hole. The key set is the union of the value
  -- sets of 'hole2idx'.
  -- OPT(Linnea, 2021-05-19): Consider other representations, as the same
  -- expression may be repeated many times.
  idx2hole: [Expr],

  -- Maps a hole to the function in which it is defined
  hole2fun: Map NameInfo NameInfo,

  -- Maps a hole to its type
  hole2ty: Map NameInfo Type,

  -- Maps a context-expanded hole index to its edge path
  verbosePath: Map Int Path,

  -- Maps a base hole to its prefix tree, which stores a compact representation of
  -- the paths
  contexts: Map NameInfo (PTree NameInfo)

}

-- Create a new name from a prefix string and name.
let _newNameFromStr : Str -> Name -> Name = lam prefix. lam name.
  nameSym (concat prefix (nameGetStr name))
-- Get the name of the incoming variable from a name.
let _incVarFromName = _newNameFromStr "inc_"

let _findLetBinding : Name -> Expr -> Option Expr = use MExprAst in
  lam name. lam expr.
    recursive let findLetBindingH = lam acc. lam expr.
      match acc with Some e then Some e
      else match expr with TmLet {ident = ident, body = body, inexpr = inexpr}
      then
        if nameEq ident name then Some body
        else match findLetBindingH acc body with Some b then Some b
        else findLetBindingH acc inexpr
      else sfold_Expr_Expr findLetBindingH acc expr
    in
    findLetBindingH (None ()) expr

-- Compute the initial call context environment for a program.
let callCtxInit : [NameInfo] -> CallGraph -> Expr -> CallCtxEnv =
  lam publicFns. lam callGraph. lam tm.
    let fun2inc =
      _nameMapInit (callGraphNames callGraph) identity _incVarFromName
    in

    let lbl2inc =
      _nameMapInit (callGraphEdgeNames callGraph)
        (lam e. match e with (_, _, lbl) then lbl else never)
        (lam e.
           match e with (from, _, _) then
             mapFindExn from fun2inc
           else never)
    in

    let callGraphRev = digraphReverse callGraph in

    let lbl2count =
      foldl (lam acc. lam funName.
               let incomingEdges =
                 _callGraphNameSeq (digraphEdgesFrom funName callGraphRev) in
               match foldl (lam acc. lam e.
                              match e with (_, _, lbl) then
                                match acc with (hm, i) then
                                  (mapInsert lbl i hm,
                                   addi i 1)
                                else never
                              else never)
                           (acc, 1)
                           incomingEdges
               with (hm, _) then hm
               else never)
            (mapEmpty nameCmp)
            (digraphVertices callGraph)

    in

    let threadPoolInfo =
      use MExprAst in
      switch
        (findName _threadPoolNbrThreadsStr tm, findName _threadPoolId2idxStr tm)
      case (Some n1, Some n2) then
        match _findLetBinding n1 tm
        with Some (TmConst {val = CInt {val = i}})
        then Some (i, n2)
        else error (join [ "Expected "
                         , _threadPoolNbrThreadsStr
                         , " to be bound to an integer"])
      case (None (), None ()) then None ()
      case _ then error (join ["Expected both or none of "
                              , _threadPoolNbrThreadsStr
                              , " and "
                              , _threadPoolId2idxStr,
                              " to be defined."])
      end
    in

    { callGraph = callGraph
    , fun2inc = fun2inc
    , lbl2inc = lbl2inc
    , lbl2count = lbl2count
    , publicFns = publicFns
    , threadPoolInfo = threadPoolInfo
    , hole2idx = mapEmpty nameInfoCmp
    , idx2hole = []
    , hole2fun = mapEmpty nameInfoCmp
    , hole2ty = mapEmpty nameInfoCmp
    , verbosePath = mapEmpty subi
    , contexts = mapEmpty nameInfoCmp
    }

-- Returns the incoming variable of a function name, or None () if the name is
-- not a node in the call graph.
let callCtxFunLookup : Name -> CallCtxEnv -> Option Name =
  lam name : Name. lam env : CallCtxEnv.
    match env with { fun2inc = fun2inc } then
      mapLookup name fun2inc
    else never

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxFun2Inc : Name -> CallCtxEnv -> Name = lam name. lam env : CallCtxEnv.
  match env with { fun2inc = fun2inc } then
    mapFindExn name fun2inc
  else never

-- Get the incoming variable name of an edge label, giving an error if the edge
-- is not part of the call graph.
let callCtxLbl2Inc : Name -> CallCtxEnv -> Name =
  lam lbl : Name. lam env : CallCtxEnv.
    match env with { lbl2inc = lbl2inc } then
      optionGetOrElse (lam. error "lbl2inc lookup failed")
                      (mapLookup lbl lbl2inc)
    else never

-- Get the count of an edge label, giving an error if the edge is not part of
-- the call graph.
let callCtxLbl2Count : Name -> CallCtxEnv -> Int =
  lam lbl : Name. lam env : CallCtxEnv.
    match env with { lbl2count = lbl2count } then
      optionGetOrElse (lam. error "lbl2count lookup failed")
                      (mapLookup lbl lbl2count)
    else never

-- Get all the incoming variable names of the program.
let callCtxIncVarNames : CallCtxEnv -> [Name] = lam env : CallCtxEnv.
  match env with { fun2inc = fun2inc } then
    mapValues fun2inc
  else never

let callCtxAddHole : Expr -> NameInfo -> [[Edge]] -> NameInfo -> CallCtxEnv -> CallCtxEnv =
  lam h. lam name. lam paths. lam funName. lam env : CallCtxEnv.
    match env with
      { hole2idx = hole2idx, idx2hole = idx2hole, hole2fun = hole2fun,
        hole2ty = hole2ty, verbosePath = verbosePath, contexts = contexts }
    in
    let countInit = length idx2hole in
    -- Empty prefix tree with a sentinel node
    let tree = prefixTreeEmpty nameInfoCmp (nameSym "", NoInfo ()) in
    match
      foldl
      (lam acc. lam path.
         match acc with (m, verbose, tree, i) in
         let lblPath = map (lam e : Edge. e.2) path in
         ( mapInsert lblPath i m,
           mapInsert i path verbose,
           prefixTreeInsert nameInfoCmp tree i (reverse lblPath),
           addi i 1)
         )
      (mapEmpty (seqCmp nameInfoCmp), env.verbosePath, tree, countInit)
      paths
    with (m, verbose, tree, count) in
    let n = length paths in
    utest n with subi count countInit in
    {{{{{{env with hole2idx = mapInsert name m hole2idx}
              with idx2hole = concat idx2hole (create n (lam. h))}
              with hole2fun = mapInsert name funName hole2fun}
              with hole2ty = mapInsert name (use HoleAst in tyTm h) hole2ty}
              with verbosePath = verbose}
              with contexts = mapInsert name tree contexts}

let callCtxHole2Idx : NameInfo -> [NameInfo] -> CallCtxEnv -> Int =
  lam nameInfo. lam path. lam env : CallCtxEnv.
    match env with { hole2idx = hole2idx } then
      mapFindExn path (mapFindExn nameInfo hole2idx)
    else never

let callCtxDeclareIncomingVars : Int -> CallCtxEnv -> [Expr] =
  lam init : Int. lam env : CallCtxEnv.
    match env with { threadPoolInfo = threadPoolInfo } then
      switch threadPoolInfo
      case Some (nbrThreads, id2idxName) then
        let totalNbrThreads = addi 1 nbrThreads in
        map (lam iv.
          nulet_ iv
            (tensorCreate_ tyunknown_
                           (seq_ [int_ totalNbrThreads])
                           (nulam_ (nameSym "") (ref_ (int_ init)))))
          (callCtxIncVarNames env)
      case None () then
        map (lam iv.
          nulet_ iv (ref_ (int_ init)))
          (callCtxIncVarNames env)
      end
    else never

let callCtxReadIncomingVar : Name -> CallCtxEnv -> Expr =
  lam iv. lam env : CallCtxEnv.
    match env with { threadPoolInfo = threadPoolInfo } then
      switch threadPoolInfo
      case Some (_, id2idxName) then
        let idxName = nameSym "idx" in
        bindall_
        [ nulet_ idxName (app_
          (deref_ (nvar_ id2idxName)) uunit_)
        , deref_ (tensorGetExn_ tyunknown_ (nvar_ iv) (seq_ [nvar_ idxName]))
        ]
      case None () then
        deref_ (nvar_ iv)
      end
    else never

let callCtxModifyIncomingVar : Name -> Int -> CallCtxEnv -> Expr =
  lam iv. lam v : Int. lam env : CallCtxEnv.
    match env with { threadPoolInfo = threadPoolInfo } then
      switch threadPoolInfo
      case Some (_, id2idxName) then
        let idxName = nameSym "idx" in
        bindall_
        [ nulet_ idxName (app_
          (deref_ (nvar_ id2idxName)) uunit_)
        , modref_ (tensorGetExn_ tyunknown_ (nvar_ iv) (seq_ [nvar_ idxName])) (int_ v)
        ]
      case None () then
        modref_ (nvar_ iv) (int_ v)
      end
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
let _appGetCallee : Expr -> Option NameInfo = use AppAst in use VarAst in lam tm.
  recursive let work = lam app.
    match app with TmApp {lhs = TmVar v} then
      Some (v.ident, v.info)
    else match app with TmApp {lhs = TmApp a} then
      work (TmApp a)
    else None ()
  in work tm

let _x = nameSym "x"
let _xInfo = (_x, NoInfo ())
let _y = nameSym "y"
let _yInfo = (_y, NoInfo ())
utest
  _appGetCallee (appf3_ (nvar_ _x) true_ (nvar_ _y) (int_ 4))
with Some _xInfo using optionEq nameInfoEq
utest
  _appGetCallee (addi_ (nvar_ _x) (int_ 3))
with None () using optionEq nameInfoEq

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

-- Generate code for looking up a value of a hole depending on its call history
let _lookupCallCtx
  : (Int -> Expr) -> NameInfo -> Name
  -> CallCtxEnv -> [[NameInfo]] -> Expr =
  lam lookup. lam holeId. lam incVarName. lam env : CallCtxEnv. lam paths.
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

type LookupTable = [Expr]

let _table = nameSym "table"
let _argv = nameSym "argv"

type ContextExpanded =
{ ast : Expr             -- The context-expanded ast
, table : LookupTable    -- The initial lookup table
, tempDir : String       -- The temporary directory
, tempFile : String      -- The file from which hole values are read
, cleanup : Unit -> Unit -- Removes all temporary files from the disk
, env : CallCtxEnv       -- Call context environment
}

-- Fragment for transforming a program with holes.
lang ContextExpand = HoleCallGraph + HoleAst + IntAst
  -- 'contextExpand public t' eliminates all holes in the expression 't' and and
  --  replace them by lookups in a static table. One reference per function
  --  tracks which function that latest called that function, thereby
  --  maintaining call history. Returns a result of type 'ContextExpanded'.
  sem contextExpand (publicFns : [NameInfo]) =
  | t ->
    let lookup = lam i. tensorGetExn_ tyunknown_ (nvar_ _table) (seq_ [int_ i]) in
    match _contextExpandWithLookup publicFns lookup t with (prog, env)
    then
      let tempDir = sysTempDirMake () in
      let tuneFile = sysJoinPath tempDir ".tune" in
      let ast = _wrapReadFile env tuneFile prog in
      { ast = ast
      , table = _initAssignments env
      , tempDir = tempDir
      , tempFile = tuneFile
      , cleanup = sysTempDirDelete tempDir
      , env = env
      }
    else never

  -- 'insert public table t' replaces the holes in expression 't' by the values
  -- in 'table'
  sem insert (publicFns : [NameInfo]) (table : LookupTable) =
  | t ->
    let lookup = lam i. get table i in
    match _contextExpandWithLookup publicFns lookup t with (prog, _)
    then prog else never

  sem _contextExpandWithLookup (publicFns : [NameInfo]) (lookup : Int -> Expr) =
  | t ->
    let pub2priv =
      _nameMapInit (map (lam t : NameInfo. t.0) publicFns)
        identity _privFunFromName
    in
    let tm = _replacePublic pub2priv t in

    -- Compute the call graph
    let g = toCallGraph tm in

    -- Prune the call graph
    let eqPathsAssoc = _eqPaths g publicFns _callGraphTop tm in
    let eqPathsMap : Map NameInfo [Path] = mapFromSeq nameInfoCmp eqPathsAssoc in
    let keepEdges : [Edge] =
      foldl (lam acc. lam path : (NameInfo, [[(NameInfo,NameInfo,NameInfo)]]).
               concat acc (foldl concat [] path.1))
        [] eqPathsAssoc
    in

    let edgeCmp = lam e1 : DigraphEdge NameInfo NameInfo. lam e2 : DigraphEdge NameInfo NameInfo.
      nameInfoCmp e1.2 e2.2
    in
    let keepEdges = setToSeq (setOfSeq edgeCmp keepEdges) in

    let pruned = foldl (lam acc. lam e : DigraphEdge NameInfo NameInfo.
      match e with (from, to, lbl) then
        digraphAddEdge from to lbl
          (digraphMaybeAddVertex from (digraphMaybeAddVertex to acc))
      else never)
      (digraphEmpty nameInfoCmp nameInfoEq)
      keepEdges in

    -- Initialize environment
    let env = callCtxInit publicFns pruned tm in

    -- Declare the incoming variables
    let incVars =
      let exprs =
        callCtxDeclareIncomingVars _incUndef env in
      if null exprs then uunit_
      else bindall_ exprs
    in
    let tm = bind_ incVars tm in

    -- Transform program to maintain the call history when needed
    match _maintainCallCtx lookup eqPathsMap _callGraphTop env tm with (env, prog) in
    (prog, env)

  -- Compute the equivalence paths of each hole.
  -- ... -> [(Name, [[Name]])]
  sem _eqPaths (g : CallGraph) (public : [NameInfo]) (cur : NameInfo) =
  | TmLet ({body = TmHole {depth = depth}, ident = ident} & t) ->
    let paths = eqPaths g cur depth public in
    cons ((ident, t.info), paths) (_eqPaths g public cur t.inexpr)

  | TmLet ({ body = TmLam lm } & t) ->
    concat (_eqPaths g public (t.ident, t.info) t.body)
           (_eqPaths g public cur t.inexpr)

  | TmRecLets t ->
    concat
      (foldl (lam acc. lam bind: RecLetBinding.
         let cur =
           match bind with { body = TmLam lm } then (bind.ident, bind.info)
           else cur
         in concat acc (_eqPaths g public cur bind.body))
         [] t.bindings)
      (_eqPaths g public cur t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr (_eqPaths g public cur) tm)

  -- Find the initial mapping from holes to values
  sem _initAssignments =
  | env ->
    let env : CallCtxEnv = env in
    map (lam h. default h) env.idx2hole

  -- Move the contents of each public function to a hidden private function, and
  -- forward the call to the public functions to their private equivalent.
  sem _replacePublic (pub2priv : Map Name Name) =
  -- Function call: forward call for public function
  | TmLet ({ body = TmApp a } & t) ->
    match _appGetCallee (TmApp a) with Some callee then
      match callee with (callee, _) then
        match mapLookup callee pub2priv
        with Some local then
          TmLet {{t with body = _appSetCallee (TmApp a) local}
                    with inexpr = _replacePublic pub2priv t.inexpr}
        else TmLet {t with inexpr = _replacePublic pub2priv t.inexpr}
      else never
    else TmLet {t with inexpr = _replacePublic pub2priv t.inexpr}

  -- Function definition: create private equivalent of public functions
  | TmLet ({ body = TmLam lm } & t) & tm ->
    match mapLookup t.ident pub2priv
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
          match mapLookup bind.ident pub2priv
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
  sem _maintainCallCtx (lookup : Lookup) (eqPaths : Map NameInfo [Path])
                       (cur : NameInfo) (env : CallCtxEnv) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    match
      match _maintainCallCtx lookup eqPaths cur env t.inexpr with (env, inexpr) in
      match _maintainCallCtx lookup eqPaths cur env t.body with (env, body) in
      ( env,
        TmLet {{t with inexpr = inexpr}
                  with body = body})
    with (env, le) in
    let env : CallCtxEnv = env in
    -- Track call only if edge is part of the call graph
    match env with { callGraph = callGraph } in
    match callCtxFunLookup cur.0 env with Some _ then
      match _appGetCallee (TmApp a) with Some callee then
        match callCtxFunLookup (nameInfoGetName callee) env
        with Some iv then
          if digraphIsSuccessor callee cur callGraph then
            -- Set the incoming var of callee to current node
            let count = callCtxLbl2Count t.ident env in
            let update = callCtxModifyIncomingVar iv count env in
            (env, bind_ (nulet_ (nameSym "") update) le)
          else (env, le) -- edge not part of call graph
        else (env, le) -- callee not part of call graph
      else (env, le) -- not an application with TmVar
    else (env, le) -- caller not part of call graph

  -- Hole: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
    match
      let isTop = nameInfoEq cur _callGraphTop in
      if or (eqi depth 0) isTop then
        let env = callCtxAddHole t.body (ident, t.info) [[]] cur env in
        (env, lookup (callCtxHole2Idx (ident, t.info) [] env))
      else
        let paths = mapFindExn (ident, t.info) eqPaths in
        let env = callCtxAddHole t.body (ident, t.info) paths cur env in
        let iv = callCtxFun2Inc cur.0 env in
        let lblPaths = map (lam p. map (lam e : Edge. e.2) p) paths in
        let res = _lookupCallCtx lookup (ident, t.info) iv env lblPaths in
        (env, res)
    with (env, lookupCode) in
    match _maintainCallCtx lookup eqPaths cur env t.inexpr with (env, inexpr) in
    ( env,
      TmLet {{t with body = lookupCode}
                with inexpr = inexpr})

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody = (t.ident, t.info) in
    match _maintainCallCtx lookup eqPaths curBody env t.body with (env, body) in
    match _maintainCallCtx lookup eqPaths cur env t.inexpr with (env, inexpr) in
    ( env,
      TmLet {{t with body = body}
                with inexpr = inexpr})

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    match
      mapAccumL (lam env : CallCtxEnv. lam bind : RecLetBinding.
        let curBody =
          match bind with { body = TmLam lm } then (bind.ident, bind.info)
          else cur
        in
        match _maintainCallCtx lookup eqPaths curBody env bind.body
        with (env, body) in (env, { bind with body = body })
      ) env bindings
    with (env, newBinds) in
    match _maintainCallCtx lookup eqPaths cur env inexpr with (env, inexpr) in
    ( env,
      TmRecLets {{t with bindings = newBinds}
                    with inexpr = inexpr})
  | tm ->
    smapAccumL_Expr_Expr (_maintainCallCtx lookup eqPaths cur) env tm

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

lang MExprHoles = HoleAst + ContextExpand + MExprSym + MExprANF

lang HolesPrettyPrint = MExprHoles + MExprPrettyPrint

lang TestLang = HolesPrettyPrint + MExprEq

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

let debug = false in

let debugPrint = lam ast. lam pub.
  if debug then
    printLn "----- BEFORE ANF -----\n";
    printLn (expr2str ast);
    let ast = anf ast in
    printLn "\n----- AFTER ANF -----\n";
    printLn (expr2str ast);
    match contextExpand pub ast with {ast = ast} then
      printLn "\n----- AFTER TRANSFORMATION -----\n";
      printLn (expr2str ast);
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

match contextExpand [(funB, NoInfo ()), (funC, NoInfo ())] ast with
  {ast = flatAst, table = table, tempFile = tempFile, cleanup = cleanup, env = env}
then

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
  let insertedAst = insert [(funB, NoInfo ()), (funC, NoInfo ())] table ast in

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

else never
