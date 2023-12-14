-- Implements graph coloring for maintaining the call context during runtime of
-- the program.

include "ast.mc"
include "eq-paths.mc"
include "prefix-tree.mc"
include "call-graph.mc"
include "name-info.mc"

include "mexpr/utils.mc"

------------------------------
-- Call context environment --
------------------------------

type Edge = (NameInfo, NameInfo, NameInfo)
type Path = [Edge]
type EqPaths = {id: NameInfo, home: NameInfo, eqPaths: [Path]}

let edgeCmp = lam e1 : Edge. lam e2 : Edge.
  nameInfoCmp e1.2 e2.2

let _nameMapInit : all a. all v. [a] -> (a -> Name) -> (a -> v) -> Map Name v =
  lam items: [a]. lam toKey: a -> Name. lam toVal: a -> v.
    foldl (lam acc: Map Name v. lam e: a. mapInsert (toKey e) (toVal e) acc)
      (mapEmpty nameCmp)
      items

let _threadPoolNbrThreadsStr = "threadPoolNbrThreads"
let _threadPoolId2idxStr = "threadPoolId2idx"

-- Maintains call context information necessary for program transformations.
type CallCtxEnv = use Ast in {

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

  -- Maps edge labels in the call graph to its from-node.
  lbl2fun: Map Name Name,

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
let _newNameFromStr : String -> Name -> Name = lam prefix. lam name.
  nameSym (concat prefix (nameGetStr name))
-- Get the name of the incoming variable from a name.
let _incVarFromName = _newNameFromStr "inc_"

let _findLetBinding : Name -> use Ast in Expr -> Option (use Ast in Expr) =
  use MExprAst in
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
let callCtxInit : [NameInfo] -> CallGraph -> use Ast in Expr -> CallCtxEnv =
  lam publicFns. lam callGraph. lam tm.
    let fun2inc =
      _nameMapInit (callGraphNames callGraph) identity _incVarFromName
    in

    let lbl2inc =
      _nameMapInit (callGraphEdgeNames callGraph)
        (lam e. match e with (_, _, lbl) in lbl)
        (lam e.
           match e with (from, _, _) in
           mapFindExn from fun2inc)
    in

    let lbl2fun =
      _nameMapInit (callGraphEdgeNames callGraph)
        (lam e. match e with (_, _, lbl) in lbl)
        (lam e. match e with (from, _, _) in from)
    in

    let callGraphRev = digraphReverse callGraph in

    let lbl2count =
      foldl (lam acc. lam funName.
               let incomingEdges =
                 _callGraphNameSeq (digraphEdgesFrom funName callGraphRev) in
               match foldl (lam acc. lam e.
                              match e with (_, _, lbl) in
                              match acc with (hm, i) in
                              (mapInsert lbl i hm, addi i 1))
                           (acc, 1)
                           incomingEdges
               with (hm, _) in hm)
            (mapEmpty nameCmp)
            (digraphVertices callGraph)

    in

    let threadPoolInfo =
      use MExprAst in
      switch
        use MExprFindSym in
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
    , lbl2fun = lbl2fun
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

-- Get the incoming variable name of a function, giving an error if the function
-- name is not part of the call graph.
let callCtxHole2Fun : NameInfo -> CallCtxEnv -> NameInfo = lam name. lam env : CallCtxEnv.
  mapFindExn name env.hole2fun

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

let callCtxAddHole
  : use Ast in Expr -> NameInfo -> [[Edge]] -> NameInfo -> CallCtxEnv -> CallCtxEnv =
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

let callCtxDeclareIncomingVars : Int -> CallCtxEnv -> [use Ast in Expr] =
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

let callCtxReadIncomingVar : Name -> CallCtxEnv -> use Ast in Expr =
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

let callCtxModifyIncomingVar : Name -> Int -> CallCtxEnv -> use Ast in Expr =
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

--------------------
-- Graph coloring --
--------------------

-- Helpers --

-- The initial value of an incoming variable.
let _incUndef = 0
-- Get the name of a forwarding call variable from a name.
let _fwdVarFromName = _newNameFromStr "fwd_"
-- Get the name of a private function from a name.
let _privFunFromName = _newNameFromStr "pri_"

-- Get the leftmost node (callee function) in a nested application node. Returns
-- optionally the variable name if the leftmost node is a variable, otherwise
-- None ().
let _appGetCallee
  : use Ast in Expr -> Option NameInfo = use AppAst in use VarAst in lam tm.
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
let _appSetCallee
  : use Ast in Expr -> Name -> use Ast in Expr = use AppAst in use VarAst in
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
let _lamWithBody
  : ([Name] -> use Ast in Expr) -> use Ast in Expr -> use Ast in Expr =
  use LamAst in
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

-- Helper for creating a hidden equivalent of a public function and replace the
-- public function with a forwarding call to the hidden function.
type Binding = {ident : Name, body : use Ast in Expr}
let _forwardCall
  : Name -> (use Ast in Expr -> use Ast in Expr) -> Binding -> (Binding, Binding) =
  lam local. lam f. lam bind : Binding.
    let fwdVar = _fwdVarFromName bind.ident in
    let newBody = lam args.
      bind_ (nulet_ fwdVar (appSeq_ (nvar_ local) (map nvar_ args)))
      (nvar_ fwdVar)
    in
    let localFun = {{bind with ident = local}
                          with body = f bind.body}
    in (localFun, {bind with body = _lamWithBody newBody bind.body})

-- Graph coloring proper --

lang GraphColoring = HoleAst + HoleCallGraph
  sem colorCallGraph (publicFns : [NameInfo]) =
  | t ->
    let pub2priv =
      _nameMapInit (map (lam t : NameInfo. t.0) publicFns)
        identity _privFunFromName
    in
    let tm = _replacePublic pub2priv t in

    -- Compute the call graph
    let g = toCallGraph tm in

    -- Prune the call graph
    let eqPaths : [EqPaths] =
      _eqPaths g publicFns callGraphTop [] tm
    in
    let eqPathsAssoc =
      map (lam e: EqPaths.
        (e.id, e.eqPaths)) eqPaths
    in
    let eqPathsMap : Map NameInfo [Path] = mapFromSeq nameInfoCmp eqPathsAssoc in
    let keepEdges : [Edge] =
      foldl (lam acc. lam path : (NameInfo, [[(NameInfo,NameInfo,NameInfo)]]).
               concat acc (foldl concat [] path.1))
        [] eqPathsAssoc
    in

    -- Keep edges that are part of context strings
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
    match _maintainCallCtx eqPathsMap callGraphTop env tm with (env, prog) in
    (env, prog)

  -- Main function for graph coloring. Maintains call context history by
  -- updating incoming variables before function calls.
  sem _maintainCallCtx (eqPaths : Map NameInfo [Path]) (cur : NameInfo) (env : CallCtxEnv) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    match
      match _maintainCallCtx eqPaths cur env t.inexpr with (env, inexpr) in
      match _maintainCallCtx eqPaths cur env t.body with (env, body) in
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

  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
    let paths = mapFindExn (ident, t.info) eqPaths in
    let env = callCtxAddHole t.body (ident, t.info) paths cur env in
    match _maintainCallCtx eqPaths cur env t.inexpr with (env, inexpr) in
    (env, TmLet {t with inexpr = inexpr})

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody = (t.ident, t.info) in
    match _maintainCallCtx eqPaths curBody env t.body with (env, body) in
    match _maintainCallCtx eqPaths cur env t.inexpr with (env, inexpr) in
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
        match _maintainCallCtx eqPaths curBody env bind.body
        with (env, body) in (env, { bind with body = body })
      ) env bindings
    with (env, newBinds) in
    match _maintainCallCtx eqPaths cur env inexpr with (env, inexpr) in
    ( env,
      TmRecLets {{t with bindings = newBinds}
                    with inexpr = inexpr})
  | tm ->
    smapAccumL_Expr_Expr (_maintainCallCtx eqPaths cur) env tm


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

  -- Finds the home vertex and equivalence path for each hole.
  sem _eqPaths (g : CallGraph) (public : [NameInfo]) (cur : NameInfo) (acc: [EqPaths]) =
  | TmLet ({body = TmHole {depth = depth}, ident = ident} & t) ->
    let paths = eqPaths g cur depth public in
    cons {id=(ident, t.info), home=cur, eqPaths=paths}
      (_eqPaths g public cur acc t.inexpr)

  | TmLet ({ body = TmLam lm } & t) ->
    concat (_eqPaths g public (t.ident, t.info) acc t.body)
           (_eqPaths g public cur [] t.inexpr)

  | TmRecLets t ->
    concat
      (foldl (lam acc. lam bind: RecLetBinding.
         let cur =
           match bind with { body = TmLam lm } then (bind.ident, bind.info)
           else cur
         in concat acc (_eqPaths g public cur [] bind.body))
         [] t.bindings)
      (_eqPaths g public cur acc t.inexpr)

  | tm ->
    sfold_Expr_Expr (_eqPaths g public cur) acc tm

end
