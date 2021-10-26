include "mexpr/mexpr.mc"
include "mexpr/pprint.mc"
include "mexpr/eq.mc"
include "mexpr/keyword-maker.mc"
include "mexpr/boot-parser.mc"
include "mexpr/utesttrans.mc"
include "mexpr/ast-builder.mc"
include "mexpr/anf.mc"

include "sys.mc"
include "digraph.mc"
include "string.mc"
include "eq-paths.mc"
include "name.mc"
include "prefix-tree.mc"

-- This file contains implementations related to decision points.

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

type NameInfo = (Name, Info)

let nameInfoCmp = lam v1 : NameInfo. lam v2 : NameInfo.
  nameCmp v1.0 v2.0

let nameInfoEq = lam l1 : NameInfo. lam l2 : NameInfo.
  _eqn l1.0 l2.0

let nameInfoGetStr = lam ni : NameInfo.
  nameGetStr ni.0

let nameInfoGetName = lam ni : NameInfo.
  ni.0

let nameInfoGetInfo = lam ni : NameInfo.
  ni.1

let _cmpPaths = seqCmp nameInfoCmp

let _nameMapInit : [a] -> (a -> Name) -> (a -> v) -> Map Name v =
  lam items. lam toKey. lam toVal.
    foldl (lam acc. lam e. mapInsert (toKey e) (toVal e) acc)
      (mapEmpty nameCmp)
      items

-------------------------
-- Call graph creation --
-------------------------

-- NOTE(Linnea, 2021-02-03): the call graph creation algorithm assumes that the
-- AST is symbolized and in ANF.

-- The type of the call graph. Vertices are names of function identifiers, edges
-- are names of application nodes.

type CallGraph = DiGraph NameInfo NameInfo

let callGraphNames = lam cg.
  map (lam t : NameInfo. t.0) (digraphVertices cg)

let _callGraphNameSeq = lam seq.
  map (lam t : (NameInfo, NameInfo, NameInfo).
    ((t.0).0, (t.1).0, (t.2).0)) seq

let callGraphEdgeNames = lam cg.
  _callGraphNameSeq (digraphEdges cg)

-- The top of the call graph, has no incoming edges.
let _callGraphTop = (nameSym "top", NoInfo ())

type Binding = {ident : Name, body : Expr, info : Info}
let _handleLetVertex = use LamAst in
  lam f. lam letexpr : Binding.
    match letexpr.body with TmLam lm
    then cons (letexpr.ident, letexpr.info) (f lm.body)
    else f letexpr.body

let _handleApps = use AppAst in use VarAst in
  lam id. lam f. lam prev. lam g. lam name2info. lam app.
    recursive let appHelper = lam g. lam app.
      match app with TmApp {lhs = TmVar v, rhs = rhs} then
        let resLhs =
          if digraphHasVertex (v.ident, v.info) g then
            let correctInfo : Info = mapFindExn v.ident name2info
              -- match
              --   find (lam n : NameInfo. nameEq v.ident n.0) (digraphVertices g)
              -- with Some v then v else error "impossible"
            in
            [(prev, (v.ident, correctInfo), id)]
          else []
        in concat resLhs (f g prev name2info rhs)
      else match app with TmApp {lhs = TmApp a, rhs = rhs} then
        let resLhs = appHelper g (TmApp a) in
        concat resLhs (f g prev name2info rhs)
      else match app with TmApp a then
        concat (f g prev name2info a.lhs) (f g prev name2info a.rhs)
      else never
  in appHelper g app

-- NOTE(Linnea, 2021-02-03): Complexity O(|V|*|F|), as we visit each node
-- exactly once and each time potentially perform a graph union operation, which
-- we assume has complexity O(|F|). V is the set of nodes in the AST and F is
-- the set of nodes in the call graph (i.e. set of functions in the AST).

-- Construct a call graph from an AST. The nodes are named functions, and the
-- edges are calls to named functions. Complexity TODO
lang Ast2CallGraph = LetAst + LamAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex _callGraphTop
      (digraphEmpty nameInfoCmp nameInfoEq) in
    let g = digraphAddVertices (_findVertices arg) gempty in
    let infoMap = mapFromSeq nameCmp (digraphVertices g) in
    let edges = _findEdges g _callGraphTop infoMap arg in
    digraphAddEdges edges g

  sem _findVertices =
  | TmLet t ->
    concat
      (_handleLetVertex _findVertices
        {ident = t.ident, body = t.body, info = t.info})
      (_findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam acc. lam b : RecLetBinding.
               concat acc
                 (_handleLetVertex _findVertices
                   {ident = b.ident, body = b.body, info = b.info}))
            [] t.bindings
    in concat res (_findVertices t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr _findVertices tm)

  sem _findEdges (cg : CallGraph) (prev : NameInfo) (name2info : Map Name Info) =
  | TmLet ({body = TmApp a} & t) ->
    let resBody = _handleApps (t.ident, t.info) _findEdges prev cg name2info t.body in
    concat resBody (_findEdges cg prev name2info t.inexpr)

  | TmLet ({body = TmLam lm} & t) ->
    let resBody = _findEdges cg (t.ident, t.info) name2info lm.body in
    concat resBody (_findEdges cg prev name2info t.inexpr)

  | TmRecLets t ->
    let res =
      let handleBinding = lam g. lam b : RecLetBinding.
        match b with { body = TmLam { body = lambody }, ident = ident, info = info } then
          _findEdges g (ident, info) name2info lambody
        else
          _findEdges g prev name2info b.body
      in foldl (lam acc. lam b. concat acc (handleBinding cg b)) [] t.bindings
    in concat res (_findEdges cg prev name2info t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr (_findEdges cg prev name2info) tm)

end

--------------------------------------------
-- Language fragments for decision points --
--------------------------------------------

let decisionPointsKeywords = ["hole", "Boolean", "IntRange"]

let _lookupExit = lam info : Info. lam s : String. lam m : Map String a.
  mapLookupOrElse (lam. infoErrorExit info (concat s " not found")) s m

let _expectConstInt = lam info : Info. lam s. lam i.
  use IntAst in
  match i with TmConst {val = CInt {val = i}} then i
  else infoErrorExit info (concat "Expected a constant integer: " s)

lang HoleAst = IntAst + ANF + KeywordMaker
  syn Hole =

  syn Expr =
  | TmHole {default : Expr,
            depth : Int,
            ty : Type,
            info : Info,
            inner : Hole}

  sem tyTm =
  | TmHole {ty = ty} -> ty

  sem symbolizeExpr (env : SymEnv) =
  | TmHole h -> TmHole h

  sem default =
  | TmHole {default = default} -> default
  | t -> smap_Expr_Expr default t

  sem isAtomic =
  | TmHole _ -> false

  sem pprintHole =

  sem pprintCode (indent : Int) (env : SymEnv) =
  | TmHole t ->
    match pprintCode indent env t.default with (env, default) then
      match pprintHole t.inner with (keyword, bindings) then
        (env, join
          [ "hole ("
          , keyword
          , " {"
          , "depth = ", int2string t.depth, ", "
          , "default = ", default, ", "
          , strJoin ", "
            (map (lam b : (String, String). join [b.0, " = ", b.1])
               bindings)
          ,  "}"
          , ")"
          ])
      else never
    else never

  sem isValue =
  | TmHole _ -> false

  sem next (last : Option Expr) (stepSize : Int) =
  | TmHole {inner = inner} ->
    hnext last stepSize inner

  sem hnext (last : Option Expr) (stepSize : Int) =

  sem sample =
  | TmHole {inner = inner} ->
    hsample inner

  sem hsample =

  sem normalize (k : Expr -> Expr) =
  | TmHole ({default = default} & t) ->
    k (TmHole {t with default = normalizeTerm t.default})

  sem isKeyword =
  | TmHole _ -> true

  sem matchKeywordString (info : Info) =
  | "hole" -> Some (1, lam lst. head lst)

  sem _mkHole (info : Info) (hty : Type) (holeMap : Map String Expr -> Hole)
              (validate : Expr -> Expr) =
  | arg ->
    use RecordAst in
    match arg with TmRecord {bindings = bindings} then
      let bindings = mapFromSeq cmpString
        (map (lam t : (SID, Expr). (sidToString t.0, t.1))
           (mapBindings bindings)) in
      let default = _lookupExit info "default" bindings in
      let depth = mapLookupOrElse (lam. int_ 0) "depth" bindings in
      validate
        (TmHole { default = default
                , depth = _expectConstInt info "depth" depth
                , info = info
                , ty = hty
                , inner = holeMap bindings})
    else error "impossible"
end

-- A Boolean decision point.
lang HoleBoolAst = BoolAst + HoleAst
  syn Hole =
  | BoolHole {}

  sem hsample =
  | BoolHole {} ->
    get [true_, false_] (randIntU 0 2)

  sem hnext (last : Option Expr) (stepSize : Int) =
  | BoolHole {} ->
    match last with None () then Some false_
    else match last with Some (TmConst {val = CBool {val = false}}) then
      Some true_
    else match last with Some (TmConst {val = CBool {val = true}}) then
      None ()
    else never

  sem fromString =
  | "true" -> true
  | "false" -> false

  sem matchKeywordString (info : Info) =
  | "Boolean" ->
    Some (1,
      let validate = lam expr.
        match expr with TmHole {default = default} then
          match default with TmConst {val = CBool _} then expr
          else infoErrorExit info "Default value not a constant Boolean"
        else infoErrorExit info "Not a decision point" in

      lam lst. _mkHole info tybool_ (lam. BoolHole {}) validate (get lst 0))

  sem pprintHole =
  | BoolHole {} ->
    ("Boolean", [])
end

-- An integer decision point (range of integers).
lang HoleIntRangeAst = IntAst + HoleAst
  syn Hole =
  | HIntRange {min : Int,
              max : Int}

  sem hsample =
  | HIntRange {min = min, max = max} ->
    int_ (randIntU min (addi max 1))

  sem hnext (last : Option Expr) (stepSize : Int) =
  | HIntRange {min = min, max = max} ->
    match last with None () then Some (int_ min)
    else match last with Some (TmConst {val = CInt {val = i}}) then
      if eqi i max then
        None ()
      else
        let next = addi i stepSize in
        utest geqi next min with true in
        if leqi next max then Some (int_ next)
        else None ()
    else never

  sem matchKeywordString (info : Info) =
  | "IntRange" ->
    Some (1,
      let validate = lam expr.
        match expr
        with TmHole {default = TmConst {val = CInt {val = i}},
                     inner = HIntRange {min = min, max = max}}
        then
          if and (leqi min i) (geqi max i) then expr
          else infoErrorExit info "Default value is not within range"
        else infoErrorExit info "Not an integer decision point" in

      lam lst. _mkHole info tyint_
        (lam m.
           let min = _expectConstInt info "min" (_lookupExit info "min" m) in
           let max = _expectConstInt info "max" (_lookupExit info "max" m) in
           if leqi min max then
             HIntRange {min = min, max = max}
           else infoErrorExit info
             (join ["Empty domain: ", int2string min, "..", int2string max]))
        validate (get lst 0))

  sem pprintHole =
  | HIntRange {min = min, max = max} ->
    ("IntRange", [("min", int2string min), ("max", int2string max)])
end

let holeBool_ = use HoleBoolAst in
  lam default. lam depth.
  TmHole { default = default
         , depth = depth
         , ty = tybool_
         , info = NoInfo ()
         , inner = BoolHole {}}

let holeIntRange_ = use HoleIntRangeAst in
  lam default. lam depth. lam min. lam max.
  TmHole { default = default
         , depth = depth
         , ty = tyint_
         , info = NoInfo ()
         , inner = HIntRange {min = min, max = max}}


------------------------------
-- Call context environment --
------------------------------

type Edge = (NameInfo, NameInfo, NameInfo)
type Path = [Edge]

let edgeCmp = lam e1 : Edge. lam e2 : Edge.
  nameInfoCmp e1.2 e2.2

let threadPoolNbrThreadsStr = "threadPoolNbrThreads"
let threadPoolId2idxStr = "threadPoolId2idx"

-- Maintains call context information necessary for program transformations.
-- Except for 'hole2idx' and 'count', the information is static.
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

  -- Maps a decision point and a call path to a unique integer.
  -- TODO(Linnea, 2021-04-21): Once we have 'smapAccumL_Expr_Expr', this
  -- shouldn't be a reference.
  hole2idx: Ref (Map NameInfo (Map [NameInfo] Int)),

  -- Maps an index to its decision point. The key set is the union of the value
  -- sets of 'hole2idx'.
  -- OPT(Linnea, 2021-05-19): Consider other representations, as the same
  -- expression may be repeated many times.
  idx2hole: Ref ([Expr]),

  -- Maps a hole to the function in which it is defined
  hole2fun: Ref (Map NameInfo NameInfo),

  -- Maps a hole to its type
  hole2ty: Ref (Map NameInfo Type),

  -- Maps a hole index to its edge path
  verbosePath: Ref (Map Int Path)
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
        (findName threadPoolNbrThreadsStr tm, findName threadPoolId2idxStr tm)
      case (Some n1, Some n2) then
        match _findLetBinding n1 tm
        with Some (TmConst {val = CInt {val = i}})
        then Some (i, n2)
        else error (join [ "Expected "
                         , threadPoolNbrThreadsStr
                         , " to be bound to an integer"])
      case (None (), None ()) then None ()
      case _ then error (join ["Expected both or none of "
                              , threadPoolNbrThreadsStr
                              , " and "
                              , threadPoolId2idxStr,
                              " to be defined."])
      end
    in

    { callGraph = callGraph
    , fun2inc = fun2inc
    , lbl2inc = lbl2inc
    , lbl2count = lbl2count
    , publicFns = publicFns
    , threadPoolInfo = threadPoolInfo
    , hole2idx  = ref (mapEmpty nameInfoCmp)
    , idx2hole = ref []
    , hole2fun = ref (mapEmpty nameInfoCmp)
    , hole2ty = ref (mapEmpty nameInfoCmp)
    , verbosePath = ref (mapEmpty subi)
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

let callCtxAddHole : Expr -> NameInfo -> [[NameInfo]] -> NameInfo -> CallCtxEnv -> CallCtxEnv =
  lam h. lam name. lam paths. lam funName. lam env : CallCtxEnv.
    match env with
      { hole2idx = hole2idx, idx2hole = idx2hole, hole2fun = hole2fun,
        hole2ty = hole2ty, verbosePath = verbosePath}
    then
    let countInit = length (deref idx2hole) in
    match
      foldl
      (lam acc. lam path.
         match acc with (m, verbose, i) then
           let lblPath = map (lam e : Edge. e.2) path in
           (mapInsert lblPath i m, mapInsert i path verbose, addi i 1)
         else never)
      (mapEmpty _cmpPaths, deref env.verbosePath, countInit)
      paths
    with (m, verbose, count) then
      let n = length paths in
      utest n with subi count countInit in
      modref idx2hole (concat (deref idx2hole) (create n (lam. h)));
      modref hole2idx (mapInsert name m (deref hole2idx));
      modref hole2fun (mapInsert name funName (deref hole2fun));
      modref hole2ty (mapInsert name (use HoleAst in tyTm h) (deref hole2ty));
      modref verbosePath verbose;
      env
    else never
  else never

let callCtxHole2Idx : NameInfo -> [NameInfo] -> CallCtxEnv -> Int =
  lam nameInfo. lam path. lam env : CallCtxEnv.
    match env with { hole2idx = hole2idx } then
      mapFindExn path (mapFindExn nameInfo (deref hole2idx))
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

-- Generate code for looking up a value of a decision point depending on its
-- call history
let _lookupCallCtx
  : (Int -> Expr) -> NameInfo -> Name
  -> CallCtxEnv -> [[NameInfo]] -> Expr =
  lam lookup. lam holeId. lam incVarName. lam env : CallCtxEnv. lam paths.

    let tree = prefixTreeEmpty nameInfoCmp (nameSym "", NoInfo ()) in

    let dummyIds = create (length paths) (lam i. i) in
    let tree = prefixTreeInsertMany nameInfoCmp tree dummyIds (map reverse paths) in

    recursive let work : NameInfo -> [PTree] -> [NameInfo] -> Expr =
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
          match branches with (defaultCase, matches) then
            let default = switch defaultCase
              case [] then never_
              case [default] then default
              case _ then error "expected at most one default case"
              end
            in
            bind_
              (nulet_ tmpName (callCtxReadIncomingVar incVarName env))
              (matchall_ (snoc matches default))
          else never
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

type Flattened =
{ ast : Expr             -- The flattened ast
, table : LookupTable    -- The initial lookup table
, tempDir : String       -- The temporary directory
, tempFile : String      -- The file from which decision point values are read
, cleanup : Unit -> Unit -- Removes all temporary files from the disk
, env : CallCtxEnv       -- Call context environment
}

-- Fragment for transforming a program with decision points.
lang FlattenHoles = Ast2CallGraph + HoleAst + IntAst
  -- 'flatten public t' eliminates all decision points in the expression 't' and
  --  and replace them by lookups in a static table One reference per function
  --  tracks which function that latest called that function, thereby
  --  maintaining call history. Returns a result of type 'Flattened'.
  sem flatten (publicFns : [NameInfo]) =
  | t ->
    let lookup = lam i. tensorGetExn_ tyunknown_ (nvar_ _table) (seq_ [int_ i]) in
    match _flattenWithLookup publicFns lookup t with (prog, env)
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

  -- 'insert public table t' replaces the decision points in expression 't' by
  -- the values in 'table'
  sem insert (publicFns : [NameInfo]) (table : LookupTable) =
  | t ->
    let lookup = lam i. get table i in
    match _flattenWithLookup publicFns lookup t with (prog, _)
    then prog else never

  sem _flattenWithLookup (publicFns : [NameInfo]) (lookup : Int -> Expr) =
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
    let prog = _maintainCallCtx lookup env eqPathsMap _callGraphTop tm in
    (prog, env)

  -- Compute the equivalence paths of each decision point
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

  -- Find the initial mapping from decision points to values
  sem _initAssignments =
  | env ->
    let env : CallCtxEnv = env in
    let idx2hole = deref env.idx2hole in
    map (lam h. default h) idx2hole

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
  sem _maintainCallCtx (lookup : Lookup) (env : CallCtxEnv)
                       (eqPaths : Map NameInfo [Path]) (cur : NameInfo) =
  -- Application: caller updates incoming variable of callee
  | TmLet ({ body = TmApp a } & t) ->
    let le =
      TmLet {{t with inexpr = _maintainCallCtx lookup env eqPaths cur t.inexpr}
                with body = _maintainCallCtx lookup env eqPaths cur t.body}
    in
    -- Track call only if edge is part of the call graph
    match env with { callGraph = callGraph } then
      match callCtxFunLookup cur.0 env with Some _ then
        match _appGetCallee (TmApp a) with Some callee then
          match callCtxFunLookup (nameInfoGetName callee) env
          with Some iv then
            if digraphIsSuccessor callee cur callGraph then
              -- Set the incoming var of callee to current node
              let count = callCtxLbl2Count t.ident env in
              let update = callCtxModifyIncomingVar iv count env in
              bind_ (nulet_ (nameSym "") update) le
            else le -- edge not part of call graph
          else le -- callee not part of call graph
        else le -- not an application with TmVar
      else le -- caller not part of call graph
    else never

  -- Decision point: lookup the value depending on call history.
  | TmLet ({ body = TmHole { depth = depth }, ident = ident} & t) ->
    let lookupCode =
      if eqi depth 0 then
        let env = callCtxAddHole t.body (ident, t.info) [[]] cur env in
        lookup (callCtxHole2Idx (ident, t.info) [] env)
      else
        let paths = mapFindExn (ident, t.info) eqPaths in
        let env = callCtxAddHole t.body (ident, t.info) paths cur env in
        let iv = callCtxFun2Inc cur.0 env in
        let lblPaths = map (lam p. map (lam e : Edge. e.2) p) paths in

        let res = _lookupCallCtx lookup (ident, t.info) iv env lblPaths in
        res
    in
    TmLet {{t with body = lookupCode}
              with inexpr = _maintainCallCtx lookup env eqPaths cur t.inexpr}

  -- Function definitions: possibly update cur inside body of function
  | TmLet ({ body = TmLam lm } & t) ->
    let curBody = (t.ident, t.info) in
    TmLet {{t with body = _maintainCallCtx lookup env eqPaths curBody t.body}
              with inexpr = _maintainCallCtx lookup env eqPaths cur t.inexpr}

  | TmRecLets ({ bindings = bindings, inexpr = inexpr } & t) ->
    let newBinds =
      map (lam bind : RecLetBinding.
        match bind with { body = TmLam lm } then
          let curBody = (bind.ident, bind.info) in
          {bind with body =
             _maintainCallCtx lookup env eqPaths curBody bind.body}
        else
        {bind with body = _maintainCallCtx lookup env eqPaths cur bind.body})
      bindings
    in
    TmRecLets {{t with bindings = newBinds}
                  with inexpr = _maintainCallCtx lookup env eqPaths cur inexpr}
  | tm ->
    smap_Expr_Expr (_maintainCallCtx lookup env eqPaths cur) tm

  sem _wrapReadFile (env : CallCtxEnv) (tuneFile : String) =
  | tm ->
    -- TODO: update in case stdlib functions are better
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

    let eqSeq = lam eq : (a -> a -> Bool).
      recursive let work = lam as. lam bs.
      let pair = (as, bs) in
      match pair with ([], []) then true else
      match pair with ([a] ++ as, [b] ++ bs) then
        if eq a b then work as bs else false
        else false
      in work
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
      if eqi (length delim) 0 then [s]
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
    ) (deref env.idx2hole) in

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

lang Holes =
  HoleAst + HoleBoolAst + HoleIntRangeAst + FlattenHoles

lang MExprHoles = Holes + MExprSym + MExprANF

lang HolesPrettyPrint = MExprHoles + MExprPrettyPrint

lang TestLang = HolesPrettyPrint + MExprEq

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
      let edges = map (lam t : (NameInfo, NameInfo, NameInfo).
        match t with (from, to, label) then
          (nameGetStr from.0, nameGetStr to.0, label.0)
        else never
      ) (digraphEdges ng) in

      let vertices = map nameInfoGetStr (digraphVertices ng) in

      digraphAddEdges edges (digraphAddVertices vertices (digraphEmpty cmpString _eqn))
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
  expected = uunit_,
  vs = ["top", "foo"],
  calls = []
} in

-- let foo = lam x. x in
-- let bar = lam x. foo x in ()
let funCall = {
  ast = bind_ (ulet_ "foo" (ulam_ "x" (var_ "x")))
              (ulet_ "bar" (ulam_ "x" (app_ (var_ "foo") (var_ "x")))),
  expected = uunit_,
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
  expected = uunit_,
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
    match flatten pub ast with {ast = ast} then
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

match flatten [(funB, NoInfo ()), (funC, NoInfo ())] ast with
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
