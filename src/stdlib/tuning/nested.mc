-- Analyzes nested measuring points. A measuring point A is nested within a
-- measuring point B if A is reachable from within the subexpressions of B. This
-- is only possible if B is a match expression. This file augments the execution
-- time dependencies of such measuring points B so that they contain the
-- execution time dependencies of A.

-- Furthermore, if a measuring point A is syntactically scoped within another
-- measuring point B, we remove the A measuring point. Since A's dependencies
-- are already added to B, and since A will _always_ be executed within B, we do
-- not need A as a separate measuring point.

include "hole-cfa.mc"
include "digraph.mc"
include "common.mc"

lang NestedMeasuringPoints = MExprHoleCFA
  sem analyzeNested (env: CallCtxEnv) (cfaGraph : CFAGraph) =
  | t ->
    -- Convert from direct style map
    let cfaData = cfaGraphData cfaGraph in

    -- Collect all lambda abstract values
    let avLams : Set Name = mapFoldWithKey (
      lam acc: Set Name. lam. lam v: Set AbsVal.
        setFold (lam acc: Set Name. lam abs: AbsVal.
          match abs with AVLam {ident = ident} then
            setInsert (int2name cfaGraph.im ident) acc
          else acc) acc v
      ) (setEmpty nameCmp) cfaData
    in

    -- Build call graph from flow information
    let top = nameSym "top" in
    let callGraph = buildCallGraph cfaGraph.im avLams top cfaData t in

    -- Compute the set of eholes for each measuring point
    let eholes : Map Name [AbsVal] = mapFoldWithKey (
      lam acc. lam ident. lam avs.
        let eholes = setFold (lam acc. lam av.
          match av with AVEHole _ then cons av acc
          else acc
        ) [] avs
        in
        if null eholes then acc
        else mapInsert ident eholes acc
    ) (mapEmpty nameCmp) cfaData
    in

    let identDepsEnclosing : [(Name, [AbsVal], Name)] =
      _measEnclosingLam eholes avLams top [] t
    in

    -- Maps a measuring point to its enclosing lambda, and its dependencies
    let measEnclosingMap : Map Name (Name, [AbsVal]) = foldl (
      lam acc. lam x : (Name, [AbsVal], Name).
        mapInsert x.0 (x.2, x.1) acc
      ) (mapEmpty nameCmp) identDepsEnclosing
    in

    -- Maps a lambda to the set of measuring points that it contains
    let measInLam : Map Name (Set Name) = foldl (
      lam acc. lam x : (Name, [AbsVal], Name).
        match x with (meas, _, encLam) in
        let measSet =
          match mapLookup encLam acc with Some set then
            setInsert meas set
          else setOfSeq nameCmp [meas]
        in
        mapInsert encLam measSet acc
      ) (mapEmpty nameCmp) identDepsEnclosing
    in

    -- The set of measuring point names
    let measSet = setOfSeq nameCmp (mapKeys measInLam) in

    -- Collect augmented dependencies
    let deps : [(Name, [AbsVal])] =
      augmentDependencies
       cfaGraph.im env measEnclosingMap measInLam measSet cfaData eholes callGraph [] t
    in

    -- Collect syntactically scoped measuring points
    let synScoped : [Name] = collectSyntacticallyScoped eholes [] t in

    -- Remove the syntactically scoped measuring points to the CFA result
    let data : Map Name (Set AbsVal) = foldl (lam acc. lam ident.
        mapRemove ident acc
      ) cfaData synScoped
    in

    -- Add the augmented dependencies to the CFA result
    let data : Map Name (Set AbsVal) = foldl (
      lam acc. lam identAvs : (Name, [AbsVal]).
        match identAvs with (ident, avs) in
        match mapLookup ident acc with Some oldAvs then
          let newAvs = setUnion oldAvs (setOfSeq cmpAbsVal avs) in
          mapInsert ident newAvs acc
        else
          -- No dependencies, cannot spawn new ones
          acc
      ) data deps
    in

    -- Convert back to direct style map
    tensorIteri (lam i. lam.
      let d =
        match mapLookup (int2name cfaGraph.im (get i 0)) data with Some s then s
        else setEmpty cmpAbsVal
      in
      tensorSetExn cfaGraph.data i d) cfaGraph.data;

    cfaGraph

  sem buildCallGraph (im: IndexMap) (avLams : Set Name) (top : Name)
                     (data : Map Name (Set AbsVal)) =
  | t ->
    -- The nodes are the AVLams recorded in the data flow
    let g = digraphEmpty nameCmp eqsym in
    let g = digraphAddVertices (cons top (setToSeq avLams)) g in
    -- The edges are applications
    let edges = _callGraphEdges im data avLams top [] t in
    let g = digraphAddEdges edges g in
    g

  sem _callGraphEdges (im: IndexMap) (data: Map Name (Set AbsVal))
                      (avLams: Set Name) (cur : Name)
                      (acc : [(Name,Name,Symbol)]) =
  | TmLam t ->
    if setMem t.ident avLams then
      _callGraphEdges im data avLams t.ident acc t.body
    else
      -- Lambda expression not reachable, we are done.
      acc

  | TmApp t ->
    match t.lhs with TmVar v then
      let res =
        match mapLookup v.ident data with Some avs then
          let avLamsLhs = setFold (lam acc. lam av.
            match av with AVLam {ident = ident} then
              setInsert (int2name im ident) acc
            else acc) (setEmpty nameCmp) avs
          in
          -- Add an edge for each lam that flows to lhs
          map (lam l. (cur,l,gensym ())) (setToSeq avLamsLhs)
        else []
      in concat res acc
    else errorSingle [infoTm t.lhs] "Not a TmVar in application"

  | TmExt t -> acc

  | t ->
    sfold_Expr_Expr (_callGraphEdges im data avLams cur) acc t

  -- Find the closest enclosing lambda for each measuring point
  sem _measEnclosingLam (data : Map Name [AbsVal]) (avLams : Set Name)
                        (cur : Name) (acc : [(Name,[AbsVal],Name)]) =
  | TmLam t ->
    if setMem t.ident avLams then
      _measEnclosingLam data avLams t.ident acc t.body
    else
      -- Lambda expression not reachable, we are done.
      acc

  | TmLet ({ ident = ident, body = TmApp app } & t) ->
    let resInexpr = _measEnclosingLam data avLams cur acc t.inexpr in
    match mapLookup ident data with Some eholes then
      concat [(ident, eholes, cur)] resInexpr
    else resInexpr

  | TmLet ({ ident = ident, body = TmMatch m } & t) ->
    let resInexpr = _measEnclosingLam data avLams cur acc t.inexpr in
    let resMatch = sfold_Expr_Expr (_measEnclosingLam data avLams cur) [] (TmMatch m) in
    match mapLookup ident data with Some eholes then
      join [[(ident, eholes, cur)], resInexpr, resMatch]
    else concat resInexpr resMatch

  | t ->
    sfold_Expr_Expr (_measEnclosingLam data avLams cur) acc t

  -- Augment dependencies for nested measuring points.
  sem augmentDependencies (im: IndexMap)
                          (env: CallCtxEnv)
                          (enclosingLam : Map Name (Name, [AbsVal]))
                          (measInLam : Map Name (Set Name))
                          (measSet : Set Name)
                          (data : Map Name (Set AbsVal))
                          (dataEholes : Map Name [AbsVal])
                          (callGraph : Digraph Name Symbol)
                          (acc: [(Name, [AbsVal])]) =
  -- A match is the only type of measuring point that can have a nested
  -- measuring point, since it is the only one that consists of several
  -- subexpressions.
  | TmLet ({ ident = ident, body = TmMatch m } & t) ->
    let resInexpr =
      augmentDependencies
        im env enclosingLam measInLam measSet data dataEholes callGraph acc t.inexpr
    in
    let resMatch = sfold_Expr_Expr (
        augmentDependencies im env enclosingLam measInLam measSet data dataEholes callGraph)
        [] (TmMatch m)
    in
    match mapLookup ident enclosingLam with Some (encLam, _) then
      -- Check what measuring points that are reachable from the branches
      let depThn =
        augmentDependenciesH
          ident im env enclosingLam measInLam measSet data dataEholes callGraph [] m.thn in
      let depEls =
        augmentDependenciesH
          ident im env enclosingLam measInLam measSet data dataEholes callGraph [] m.els in
      let deps = (ident, concat depThn depEls) in
      join [resInexpr, resMatch, [deps]]
    else concat resInexpr resMatch

  | t ->
    sfold_Expr_Expr
      (augmentDependencies im env enclosingLam measInLam measSet data dataEholes callGraph)
      acc t

  sem eholesOf (info : Info) (env: CallCtxEnv) (ident: Name) =
  | avs ->
    let avs : [AbsVal] = avs in
    recursive let passesThrough = lam path.
      match path with [] then false
      else match path with [(from,to,lbl)] ++ path in
        if nameEq (nameInfoGetName lbl) ident then true
        else passesThrough path
    in
    foldl (lam acc. lam av.
        match av with AVEHole r then
          let contexts = setToSeq r.contexts in
          match contexts with [_] then cons (AVEHole r) acc
          else
            let idPaths = map (lam c. (c, mapFindExn c env.verbosePath)) contexts in
            let keep = filter (lam t: (Int, Path). passesThrough t.1) idPaths in
            let keepIds = map (lam t: (Int, Path). t.0) keep in
            utest gti (length keepIds) 0 with true in
            cons (AVEHole {r with contexts = setOfSeq subi keepIds}) acc
        else acc
      ) [] avs

  -- Collect all dependencies reachable from an expression, either from function
  -- applications or from one of the subexpressions themselves.
  sem augmentDependenciesH (ident: Name) -- The enclosing measuring point
                           (im: IndexMap)
                           (env: CallCtxEnv)
                           (enclosingLam : Map Name (Name, [AbsVal]))
                           (measInLam : Map Name (Set Name))
                           (measSet : Set Name)
                           (data : Map Name (Set AbsVal))
                           (dataEholes : Map Name [AbsVal])
                           (callGraph : Digraph Name Symbol)
                           (acc : [AbsVal]) =
  | TmLet ({body = TmApp app} & t) ->
    let resBody =
      match app.lhs with TmVar v then
        match mapLookup v.ident data with Some avs then
          -- What lambdas can flow to lhs?
          let avLamsLhs = setFold (lam acc. lam av.
            match av with AVLam {ident = ident} then
              setInsert (int2name im ident) acc
            else acc) (setEmpty nameCmp) avs
          in
          -- What measuring points are reachable from these lambdas?
          let reachable : [AbsVal] = setFold (
            lam acc. lam lamIdent.
              let reachNodes =
                setOfSeq nameCmp (mapKeys (digraphBFS lamIdent callGraph))
              in
              -- Reachable nodes that contain measuring points
              let reachMeasNodes = setIntersect reachNodes measSet in
              -- Collect dependencies of the reachable measuring points
              setFold (lam acc : [AbsVal]. lam node : Name.
                match mapLookup node measInLam with Some set then
                  setFold (lam acc. lam measIdent.
                    match mapLookup measIdent enclosingLam with Some (_, deps)
                    then eholesOf (infoTm (TmApp app)) env t.ident deps
                    else error "impossible"
                  ) [] set
                else error "impossible"
              ) acc reachMeasNodes
            ) [] avLamsLhs
          in reachable
        else []
      else errorSingle [infoTm app.lhs] "Not a TmVar in application"
    in
    let resLet = optionGetOr [] (mapLookup t.ident dataEholes) in
    let resInexpr = sfold_Expr_Expr
      (augmentDependenciesH ident im env enclosingLam measInLam measSet data dataEholes callGraph)
      acc t.inexpr
    in join [resBody, resLet, resInexpr]

  | TmLet t ->
    let resLet = optionGetOr [] (mapLookup t.ident dataEholes) in
    let resRest = sfold_Expr_Expr
        (augmentDependenciesH ident im env enclosingLam measInLam measSet data dataEholes callGraph)
        acc (TmLet t)
    in concat resLet resRest

  | t ->
    sfold_Expr_Expr
      (augmentDependenciesH ident im env enclosingLam measInLam measSet data dataEholes callGraph)
      acc t

  -- Collect measuring points that are syntactically scoped within another
  -- measuring point. They are not needed, because their dependencies have
  -- already been added to the enclosing measuring point, and will always be
  -- executed within the enclosing measuring point.
  sem collectSyntacticallyScoped (eholes : Map Name [AbsVal]) (acc : [Name]) =
  -- Need only consider match expressions, by same logic as for
  -- 'augmentDependencies'
  | TmLet ({ ident = ident, body = TmMatch m } & t) ->
    -- Recurse inexpr and body
    let resInexpr = collectSyntacticallyScoped eholes acc t.inexpr in
    let resMatch = sfold_Expr_Expr (collectSyntacticallyScoped eholes)
        [] (TmMatch m)
    in
    -- Are we in a measuring point?
    if mapMem ident eholes then
      -- Collect syntactically scoped measuring points
      let scopedThn = collectSyntacticallyScopedH eholes [] m.thn in
      let scopedEls = collectSyntacticallyScopedH eholes [] m.els in
      join [resInexpr, resMatch, scopedThn, scopedEls]
    else concat resInexpr resMatch

  | t ->
    sfold_Expr_Expr (collectSyntacticallyScoped eholes) acc t

  -- Return the measuring points syntactically scoped in an expression
  sem collectSyntacticallyScopedH (eholes : Map Name [AbsVal]) (acc: [Name]) =
  | TmLet t ->
    let resLet = if mapMem t.ident eholes then [t.ident] else [] in
    let resRest = sfold_Expr_Expr (collectSyntacticallyScopedH eholes)
        acc (TmLet t)
    in concat resLet resRest

  | t ->
    sfold_Expr_Expr (collectSyntacticallyScopedH eholes) acc t

end

lang TestLang = GraphColoring + MExprHoleCFA + ContextExpand +
                NestedMeasuringPoints +
                BootParser + MExprSym + MExprPrettyPrint + MExprANFAll
end

mexpr

use TestLang in

-- Test functions --

let debug = false in
let parse = lam str.
  let ast = parseMExprStringKeywordsExn holeKeywords str in
  let ast = makeKeywords ast in
  symbolize ast
in
let test: Bool -> Expr -> [String] -> [(String,[AbsVal],Map NameInfo (Map [NameInfo] Int),IndexMap)] =
  lam debug: Bool. lam t: Expr. lam vars: [String].
    -- Use small ANF first, needed for context expansion
    let tANFSmall = use MExprHoles in normalizeTerm t in

    -- Do graph coloring to get context information (throw away the AST).
    match colorCallGraph [] tANFSmall with (env, _) in

    -- Initialize the graph data
    let graphData = graphDataInit env in

    -- Apply full ANF
    let tANF = normalizeTerm tANFSmall in

    if debug then
      -- Version with debug printouts
      match pprintCode 0 pprintEnvEmpty t with (_,tStr) in
      printLn "\n--- ORIGINAL PROGRAM ---";
      printLn tStr;
      match pprintCode 0 pprintEnvEmpty tANF with (pprintEnv,tANFStr) in
      printLn "\n--- ANF ---";
      printLn tANFStr;
      match holeCfaDebug graphData pprintEnv tANF with (pprintEnv,cfaRes) in
      match cfaGraphToString pprintEnv cfaRes with (_, resStr) in
      printLn "\n--- CFA GRAPH ---";
      printLn resStr;
      let cfaRes : CFAGraph = cfaRes in
      let cfaRes : CFAGraph  = analyzeNested env cfaRes tANF in
      match cfaGraphToString pprintEnv cfaRes with (_, resStr) in
      printLn "\n--- AUGMENTED CFA GRAPH ---";
      printLn resStr;
      let avs : [(String, [AbsVal], Map NameInfo (Map [NameInfo] Int), IndexMap)] =
        map (lam var: String.
          let binds = mapBindings (cfaGraphData cfaRes) in
          let res = foldl (lam acc. lam b : (Name, Set AbsVal).
            if eqString var (nameGetStr b.0) then setToSeq b.1 else acc
          ) [] binds in
          (var, res, env.hole2idx, cfaRes.im)
        ) vars
      in avs

    else
      -- Version without debug printouts
      let cfaRes : CFAGraph = holeCfa graphData tANF in
      let cfaRes : CFAGraph  = analyzeNested env cfaRes tANF in
      let avs : [(String, [AbsVal], Map NameInfo (Map [NameInfo] Int), IndexMap)] =
        map (lam var: String.
          let binds = mapBindings (cfaGraphData cfaRes) in
          let res = foldl (lam acc. lam b : (Name, Set AbsVal).
            if eqString var (nameGetStr b.0) then setToSeq b.1 else acc
          ) [] binds in
          (var, res, env.hole2idx, cfaRes.im)
        ) vars
      in avs
in

-- Custom equality function
type Dep = {d: [(String,[[String]])], e: [(String,[[String]])]} in
let gbl = lam s. (s,[[]]) in
let eqTestHole = eqSeq
  (lam t1:(String,[AbsVal],Map NameInfo (Map [NameInfo] Int),IndexMap).
   lam t2:(String,Dep).
     let index2Path : String -> Int -> [String] = lam str. lam i.
       let pathMap =
         match mapFoldWithKey (lam acc. lam nameInfo. lam bind.
           match acc with Some _ then acc
           else if eqString (nameInfoGetStr nameInfo) str then Some bind
           else acc
         ) (None ()) t1.2
         with Some pathMap then pathMap
         else error "impossible"
       in
       match mapFoldWithKey (lam acc. lam path. lam index.
         if eqi index i then Some (map nameInfoGetStr path)
         else acc
       ) (None ()) pathMap
       with Some path then path
       else error "impossible"
     in

     if eqString t1.0 t2.0 then
       let data : [(String,Set Int)] = foldl (lam acc. lam av.
           match av with AVDHole {id = id, contexts = contexts}
           then
             cons (nameGetStr (int2name t1.3 id), contexts) acc else acc
         ) [] t1.1
       in
       let exe : [(String,Set Int)] = foldl (lam acc. lam av.
           match av with AVEHole {id = id, contexts = contexts}
           then cons (nameGetStr (int2name t1.3 id), contexts) acc else acc
         ) [] t1.1
       in
       let deps : Dep = t2.1 in
       -- Comparison of names
       let namesEq =
         let dataStrs = map (lam e : (String,Set Int). e.0) data in
         let exeStrs = map (lam e : (String,Set Int). e.0) exe in
         let depDataStrs = map (lam e : (String,[[String]]). e.0) deps.d in
         let depExeStrs = map (lam e : (String,[[String]]). e.0) deps.e in
         if setEq (setOfSeq cmpString dataStrs) (setOfSeq cmpString depDataStrs) then
           setEq (setOfSeq cmpString exeStrs) (setOfSeq cmpString depExeStrs)
         else false
       in
       -- Comparison of contexts
       if namesEq then
         let dataCtxs = map (lam e : (String,Set Int). (e.0, setToSeq e.1)) data in
         let dataCtxPaths = map (lam e : (String, [Int]). map (index2Path e.0) e.1) dataCtxs in
         let dataCtxPaths = map (setOfSeq (seqCmp cmpString)) dataCtxPaths in

         let exeCtxs = map (lam e : (String,Set Int). (e.0, setToSeq e.1)) exe in
         let exeCtxPaths = map (lam e : (String, [Int]). map (index2Path e.0) e.1) exeCtxs in
         let exeCtxPaths = map (setOfSeq (seqCmp cmpString)) exeCtxPaths in

         let depDataCtxs : [Set [String]] = map (lam e : (String,[[String]]). setOfSeq (seqCmp cmpString) e.1) deps.d in
         let depExeCtxs : [Set [String]] = map (lam e : (String,[[String]]). setOfSeq (seqCmp cmpString) e.1) deps.e in

         if setEq (setOfSeq setCmp dataCtxPaths) (setOfSeq setCmp depDataCtxs) then
           setEq (setOfSeq setCmp exeCtxPaths) (setOfSeq setCmp depExeCtxs)
         else false
       else false
     else false
) in
--------------------


let t = parse
"
let f1 = lam x.
  let h1 = hole (IntRange{min=100,max=200,default=200}) in
  if lti x 10 then
    -- Start measuring point m1 --
    let res = sleepMs h1 in
    res
    -- End measuring point m1 --
  else ()
in
let h2 = hole (Boolean{default=true}) in
let foo =
-- Start measuring point m2 --
  if h2 then f1 5 else sleepMs 150
-- End measuring point m2 --
in
f1 10
"
in

utest test debug t ["h1", "h2", "res", "foo"]
with [ ("h1", {d=[gbl "h1"], e=[]})
     , ("h2", {d=[gbl "h2"], e=[]})
     , ("res", {d=[], e=[gbl "h1"]})
     , ("foo", {d=[gbl "h2"], e=[gbl "h1", gbl "h2"]})
     ]
using eqTestHole in

let t = parse
"
recursive let f1 = lam x.
  let h1 = hole (IntRange{min=100,max=200,default=200}) in
  let m1 = sleepMs h1 in
  ()
in
recursive let f2 = lam x.
  let c = f1 x in c
in
recursive let f3 = lam x.
  ()
in
let h2 = hole (IntRange{min=100,max=200,default=200}) in
let m2 = if h2 then let a = f2 () in a else () in
let m3 = if h2 then () else let b = f1 () in b in
let m4 = if h2 then f3 () else () in
()
"
in

utest test debug t ["h1", "h2", "m1", "m2", "m3", "m4"]
with [ ("h1", {d=[ gbl "h1" ], e=[]})
     , ("h2", {d=[ gbl "h2" ], e=[]})
     , ("m1", {d=[], e=[ gbl "h1" ]})
     , ("m2", {d=[ gbl "h2" ], e=[ gbl "h2", gbl "h1" ]})
     , ("m3", {d=[ gbl "h2" ], e=[ gbl "h2", gbl "h1" ]})
     , ("m4", {d=[ gbl "h2" ], e=[ gbl "h2" ]})
     ]
using eqTestHole in

let t = parse
"
let g1 = lam x.
  let h2 = hole (IntRange{min=100,max=200,default=200}) in
  sleepMs h2
in
let f1 = lam x.
  let h1 = hole (IntRange{min=100,max=200,default=200}) in
  let m1 =
    if h1 then
      let f2 = lam x. g1 x in
      f2 x
    else ()
  in m1
in
f1 ()
"
in

utest test debug t ["m1"]
with [ ("m1", {d=[ gbl "h1" ], e=[ gbl "h1", gbl "h2"]})
     ]
using eqTestHole in


let t = parse
"
let f1 = lam x.
  let h1 = hole (IntRange{min=100,max=200,default=200}) in
  let h2 = hole (Boolean {default=true}) in
  let h3 = hole (Boolean {default=true}) in
  let h4 = hole (IntRange{min=100,max=200,default=200}) in
  let m1 =
    if h2 then
      let sleepVar = sleepMs in
      let m2 = sleepVar h1 in
      let m3 =
        if h3 then 1 else sleepMs h4
      in m3
    else ()
  in m1
in
f1 ()
"
in

()
