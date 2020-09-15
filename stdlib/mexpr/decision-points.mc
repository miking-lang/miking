include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"
include "prelude.mc"

-- This file contains implementations related to decision points. In particular,
-- it implements:
-- * A language fragment for decision points (HoleAst)
-- * An algorithm for AST -> call graph conversion (Ast2CallGraph fragment)
-- * Program transformations for programs with decision points (HolyCallGraph)

let _top = nameSym "top"

let _eqn = lam n1. lam n2.
  if and (nameHasSym n1) (nameHasSym n2) then
    nameEqSym n1 n2
  else
    error "Name without symbol."

lang HoleAst
  syn Expr =
  | TmHole {tp : Type,
            startGuess : Expr,
            depth : Int}
  sem symbolize (env : Env) =
end

lang HoleAstPrettyPrint = HoleAst + TypePrettyPrint
  sem isAtomic =
  | TmHole _ -> false

  sem pprintCode (indent : Int) (env : Env) =
  | TmHole h ->
    match pprintCode indent env h.startGuess with (env1, startStr) then
      match pprintCode indent env1 h.depth with (env2, depthStr) then
        (env2,
          join ["Hole (",
                strJoin ", " [getTypeStringCode indent h.tp, startStr, depthStr],
                ")"])
      else never
    else never
end

-- Temporary workaround: uniquely labeled decision points
lang LHoleAst = HoleAst
  syn Expr =
  | LTmHole {tp : Type,
             startGuess : Expr,
             depth : Int}

  sem symbolize (env : Env) =
  | LTmHole h -> LTmHole h

  sem fromTmHole =
  | TmHole h -> LTmHole {tp = h.tp, startGuess = h.startGuess,
                         depth = h.depth, id = symb_ (gensym ())}

  sem toTmHole =
  | LTmHole h -> TmHole {tp = h.tp, startGuess = h.startGuess, depth = h.depth}

  sem smap_Expr_Expr (f : Expr -> a) =
  | LTmHole h -> LTmHole h

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | LTmHole h -> acc
end

lang LHoleAstPrettyPrint = LHoleAst + HoleAstPrettyPrint
  sem isAtomic =
  | LTmHole _ -> false

  sem pprintCode (indent : Int) (env : Env) =
  | LTmHole h -> pprintCode indent env (toTmHole (LTmHole h))
end

let hole_ = use LHoleAst in
  lam tpe. lam startGuess. lam depth.
  fromTmHole (TmHole {tp = tpe, startGuess = startGuess, depth = depth})


-- Temporary workaround: uniquely labeled TmApps
lang LAppAst = AppAst
  syn Expr =
  | TmLApp {lhs : Expr, rhs : Expr, id : Symbol}

  sem fromAppAst =
  | TmApp t -> TmLApp {lhs = t.lhs, rhs = t. rhs, id = gensym ()}

  sem toAppAst =
  | TmLApp t -> TmApp {lhs = t.lhs, rhs = t.rhs}

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmLApp t -> TmLApp {lhs = f t.lhs, rhs = f t.rhs, id = t.id}

  sem sfold_Expr_Expr (f : a -> b -> a) (acc : a) =
  | TmLApp t -> f (f acc t.lhs) t.rhs

  -- Traverse an expression and label all TmApps
  sem labelApps =
  | TmApp t ->
    fromAppAst (TmApp {lhs = labelApps t.lhs, rhs = labelApps t.rhs})
  | tm -> smap_Expr_Expr labelApps tm

  sem symbolize (env : Env) =
  | TmLApp t -> fromAppAst (symbolize env (toAppAst (TmLApp t)))
end

lang LAppEval = LAppAst + AppEval
  sem eval (ctx : {env : Env}) =
  | TmLApp t -> eval ctx (toAppAst (TmLApp t))
end

lang LAppPrettyPrint = LAppAst + AppPrettyPrint
  sem isAtomic =
  | TmLApp _ -> false

  sem pprintCode (indent : Int) (env : Env) =
  | TmLApp t ->
    let s = pprintCode indent env (toAppAst (TmLApp t)) in
    s
end


-- Create a call graph from an AST.
-- * Vertices (represented as strings) are functions f defined as: let f = lam. ...
-- * There is an edge between f1 and f2 iff f1 calls f2: let f1 = lam. ... (f2 a)
-- * "top" is the top of the graph (i.e., no incoming edges)

-- Helper functions
let _handleLetVertex = use FunAst in
  lam letexpr. lam f.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

let _handleLetEdge = use FunAst in
  lam letexpr. lam f. lam g. lam prev.
    match letexpr.body with TmLam lm
    then f g letexpr.ident lm.body
    else f g prev letexpr.body

-- Complexity (I think): O(|V|*|F|), as we visit each node exactly once and each
-- time potentially perform a graph union operation, which we assume has
-- complexity O(|F|). V is the set of nodes in the AST and F is the set of nodes
-- in the call graph (i.e. set of functions in the AST).
lang Ast2CallGraph = LetAst + FunAst + RecLetsAst + LAppAst
  sem toCallGraph =
  | arg ->
    let vs = findVertices arg in
    let gempty = digraphAddVertex _top (digraphEmpty _eqn eqs) in
    let gvs = foldl (lam g. lam v. digraphAddVertex v g) gempty vs in
    findEdges gvs _top arg

  -- Find all vertices of the call graph
  sem findVertices =
  | TmLet t ->
    let res_body = _handleLetVertex t findVertices
    in concat res_body (findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam a. lam b. concat a (_handleLetVertex b findVertices))
            [] t.bindings
    in concat res (findVertices t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr findVertices tm)

  -- Find all edges of the call graph
  sem findEdges (cgraph : DiGraph) (prev : String) =
  | TmLet t ->
    -- let <fun-name> = lam. ...
    let res_body = _handleLetEdge t findEdges cgraph prev
    in findEdges res_body prev t.inexpr

  | TmLApp t ->
    let res_lhs =
      match t.lhs with TmVar n then
        -- <fun-name> <argument>
        if digraphHasVertex n.ident cgraph
        then digraphAddEdge prev n.ident t.id cgraph
        else cgraph
      else
        findEdges cgraph prev t.lhs
    in findEdges res_lhs prev t.rhs

  | TmApp t -> error "TmApps should be labeled by converting to TmLApp"

  | TmRecLets t ->
    let res =
      foldl (lam g. lam b. digraphUnion g (_handleLetEdge b findEdges g prev))
            cgraph t.bindings
    in findEdges res prev t.inexpr

  | tm ->
    sfold_Expr_Expr digraphUnion cgraph (smap_Expr_Expr (findEdges cgraph prev) tm)
end

-- Define variable names to be used in transformed program
let _callCtx = "callCtx"
let _lookupTable = "lookupTable"
let _lookup = "lookup"
let _maxDepth = "maxDepth"
let _addCall = "addCall"
let _filter = "filter"
let _max = "max"
let _isPrefix = "isPrefix"
let _isSuffix = "isSuffix"

lang ContextAwareHoles = Ast2CallGraph + LHoleAst + IntAst + SymbAst
  -- Transform the program
  sem transform (publicFns : [Name]) =
  | tm ->
    -- Equip TmApps with unique labels
    let ltm = labelApps tm in

     -- Compute the call graph
    let callGraph = toCallGraph ltm in

    -- Renaming function for public functions
    let renameF = lam ident.
      let nameStr = nameGetStr ident in
      let newNameStr = concat nameStr "Pr" in
      nameNoSym newNameStr in

    -- Check if identifier is a public function
    let isPublic = lam ident.
      optionIsSome (find (_eqn ident) publicFns) in

    -- Check if identifier is a function in the call graph
    let isFun = lam ident.
      optionIsSome (find (_eqn ident) (digraphVertices callGraph)) in

    -- Replacer function for public functions
    let makeDummy = lam funName. lam tm.
      recursive let work = lam tm. lam acc.
        match tm with TmLam t then
          TmLam {t with body=work t.body (snoc acc t.ident)}
        else
          foldl (lam a. lam x. app_ a (nvar_ x)) (app_ (nvar_ (renameF funName)) (var_ _callCtx)) acc
      in work tm []
    in
    -- Extract dummy functions from the AST, to replace public functions
    let dummies = extract isPublic makeDummy ltm in
    let defDummies = match dummies with [] then unit_ else bindall_ dummies in

    -- Transform program to use call context
    let trans = transformCallCtx isFun _top ltm in

    -- Rename public functions
    let transRenamed = rename isPublic renameF trans in

    -- Define initial call context
    let defCallCtx = let_ _callCtx (seq_ []) in

    -- Define initial lookup table
    let lookupTable = initLookupTable (cons _top publicFns) ltm in
    -- AST-ify the lookup table
    let defLookupTable =
      let_ _lookupTable
        (seq_ (map (lam r. record_ [("id", r.id), ("path", seq_ (map symb_ r.path)), ("value", r.value)]) lookupTable))
    in

    -- Compute maximum depth of the decision points
    let maxDepth =
      match lookupTable with [] then 0
      else max subi (map (lam r. length r.path) lookupTable)
    in
    -- AST-ify the maxDepth variable
    let defMaxDepth = let_ _maxDepth (int_ maxDepth) in

    -- AST-ify filter
    -- recursive let filter = lam p. lam s.
    --   if (eqi 0 (length s)) then []
    --   else if p (head s) then
    --     let f = filter p (tail s)
    --     in cons (head s) f
    --   else (filter p (tail s))
    -- in
    let filter =
      -- Define local variables
      reclets_add _filter
        (lam_ "p" (None ())
              (lam_ "s" (None ())
                    (if_ (null_ (var_ "s"))
                         (seq_ [])
                         (if_ (app_ (var_ "p") (head_ (var_ "s")))
                              (bind_ (let_ "f" (appf2_ (var_ _filter) (var_ "p") (tail_ (var_ "s"))))
                                     (cons_ (head_ (var_ "s")) (var_ "f")))
                              (appf2_ (var_ _filter) (var_ "p") (tail_ (var_ "s")))) )))
      reclets_empty
    in

    -- AST-ify max (for a non-empty list)
    -- let max = lam cmp. lam seq.
    --   recursive let work = lam e. lam seq.
    --     if null seq then e
    --     else
    --       let h = head seq in
    --       let t = tail seq in
    --       if lti h e then work e t else work h t
    --    in
    --    work (head seq) (tail seq)
    -- in utest max [2, 4, 5] with 5 in
    let max =
      let_ _max
        (lam_ "cmp" (None ()) (
          (lam_ "seq" (None ())
          (bindall_ [(reclets_add "work"
                       (lam_ "e" (None ())
                                (lam_ "seq" (None ())
                                              (if_ (null_ (var_ "seq"))
                                                   (var_ "e")
                                                   (bindall_ [let_ "h" (head_ (var_ "seq")),
                                                              let_ "t" (tail_ (var_ "seq")),
                                                              if_ (lti_ (appf2_ (var_ "cmp") (var_ "h") (var_ "e")) (int_ 0))
                                                                  (appf2_ (var_ "work") (var_ "e") (var_ "t"))
                                                                  (appf2_ (var_ "work") (var_ "h") (var_ "t"))]) )))
                     reclets_empty),
                     appf2_ (var_ "work") (head_ (var_ "seq")) (tail_ (var_ "seq"))]))))
    in

    -- AST-ify isPrefix
    -- recursive let isPrefix = lam eq. lam s1. lam s2.
    --   if null s1 then true
    --   else if null s2 then false
    --   else if (eq (head s1) (head s2)) then (isPrefix eq (tail s1) (tail s2))
    --   else false
    -- in
    let isPrefix =
      reclets_add _isPrefix (
      (lam_ "eq" (None ())
            (lam_ "s1" (None ())
                  (lam_ "s2" (None ())
                             (if_ (null_ (var_ "s1"))
                                  (true_)
                                  (if_ (null_ (var_ "s2"))
                                       (false_)
                                       (if_ (appf2_ (var_ "eq") (head_ (var_ "s1")) (head_ (var_ "s2")))
                                            (appf3_ (var_ _isPrefix) (var_ "eq") (tail_ (var_ "s1")) (tail_ (var_ "s2")) )
                                            (false_))) )))))
                                            reclets_empty
    in

    -- AST-ify isSuffix
    -- let isSuffix = lam eq. lam s1. lam s2.
    --     isPrefix eq (reverse s1) (reverse s2)
    -- in
    let isSuffix =
      let_ _isSuffix
        ((lam_ "eq" (None ())
              (lam_ "s1" (None ())
                    (lam_ "s2" (None ())
                          (appf3_ (var_ _isPrefix)
                                  (var_ "eq")
                                  (reverse_ (var_ "s1"))
                                  (reverse_ (var_ "s2"))))))) in

    -- Lookup the value for a decision point in a given call context
    -- let lookup = lam callCtx. lam id.
    --   let entries = filter (lam t. eqs t.0 id) lookupTable in
    --   let entriesSuffix = filter (lam t. isSuffix eqi t.1 callCtx) entries in
    --   let cmp = lam t1. lam t2. subi (length t1.1) (length t2.1) in
    --   max cmp entriesSuffix
    -- in
    let lookup =
      let_ _lookup
           (lam_ _callCtx (None ())
                 (lam_ "id" (None ())
                       (bindall_ [
        let_ "entries" (
            appf2_ (var_ _filter)
                   (lam_ "t" (None ()) (eqs_ (var_ "id") (recordproj_ "id" (var_ "t"))))
                   (var_ _lookupTable)),
        let_ "eqs" (lam_ "x" (None ()) (lam_ "y" (None ()) (eqs_ (var_ "x") (var_ "y")))),
        let_ "entriesSuffix"
             (appf2_ (var_ _filter)
                     (lam_ "t" (None ()) (appf3_ (var_ _isSuffix) (var_ "eqs") (recordproj_ "path" (var_ "t")) (var_ _callCtx)))
                     (var_ "entries")),
        let_ "cmp"
          (lam_ "t1" (None ())
                     (lam_ "t2" (None ())
                                (subi_
                                   (length_ (recordproj_ "path" (var_ "t1")))
                                   (length_ (recordproj_ "path" (var_ "t2")))))),
        let_ "entriesLongestSuffix" (appf2_ (var_ _max) (var_ "cmp") (var_ "entriesSuffix")),
        recordproj_ "value" (var_ "entriesLongestSuffix")])))
    in
    let defLookup = bindall_ [isPrefix, isSuffix, max, filter, lookup] in

    -- Add a function call to the call context:
    -- let addCall = lam callCtx. lam lbl.
    --   if gti (length callCtx) maxDepth then
    --     snoc (tail callCtx) lbl
    --   else
    --     snoc callCtx lbl
    let defAddCall =
      let_ _addCall (
        lam_ _callCtx (None ()) (
          lam_ "lbl" (None ()) (
            if_ (eqi_ (var_ _maxDepth) (int_ 0)) (var_ _callCtx)
                (if_ (lti_ (length_ (var_ _callCtx)) (var_ _maxDepth))
                    (snoc_ (var_ _callCtx) (var_ "lbl"))
                    (snoc_ (tail_ (var_ _callCtx)) (var_ "lbl"))) )))
    in

    -- Put all the pieces together
    symbolize assocEmpty
      (bindall_ [defLookupTable,
                 defCallCtx,
                 defMaxDepth,
                 defAddCall,
                 defLookup,
                 defDummies,
                 transRenamed])

  -- Extract expressions from the body of identifiers for which p is true using extractor function
  sem extract (p : String -> Bool)
              (extractor : String -> Expr -> Expr) =
  | TmLet {body = TmLam lm, ident=ident, inexpr=inexpr} ->
    let t = {body = TmLam lm, ident=ident, inexpr=inexpr} in
    let res =
      if p t.ident then
        let newBody = extractor t.ident t.body in
        [TmLet {{t with body = newBody} with inexpr=unit_}]
      else []
    in concat res (extract p extractor t.inexpr)

  | TmRecLets t ->
    let handleLet = lam le.
      if p le.ident then
        match le.body with TmLam lm then
          let newBody = extractor le.ident le.body in
          [{le with body=newBody}]
        else error (strJoin "" ["Expected identifier ", le.ident, " to define a lambda."])
      else []
    in
    let binds = foldl (lam acc. lam b. concat acc (handleLet b)) [] t.bindings in
    concat [TmRecLets {inexpr=unit_, bindings=binds}] (extract p extractor t.inexpr)

  | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (extract p extractor) tm)

  -- Rename identifiers for which p is true, with renaming function rf
  sem rename (p : String -> Bool) (rf : String -> String) =
  | TmLet {body = TmLam lm, ident=ident, inexpr=inexpr} ->
    let t = {body = TmLam lm, ident=ident, inexpr=inexpr} in
    let newIdent =
      if p t.ident then
        rf t.ident
      else
        t.ident
    in TmLet {{{t with ident = newIdent}
                with body = rename p rf t.body}
                with inexpr = rename p rf t.inexpr}

  | TmRecLets t ->
    let handleLet = lam le.
      -- Defines a public function
      if p le.ident then
        match le.body with TmLam lm then
          let newIdent = rf le.ident in
          let newBody = rename p rf le.body in
          {{le with ident=newIdent} with body=newBody}
        else
          error (strJoin "" ["Identifier ", le.ident, " expected to refer to a function."])
      else
        le
     in TmRecLets {{t with bindings = map handleLet t.bindings}
                    with inexpr = rename p rf t.inexpr}

  | TmVar v ->
    if p v.ident then
      TmVar {v with ident = rf v.ident}
    else TmVar v

  | tm -> smap_Expr_Expr (rename p rf) tm

  -- Transform program to use call context, considering identifiers for which p is true.
  sem transformCallCtx (p : String -> Bool) (prev : String) =
  -- Add call context as extra argument in function definitions
  | TmLet {body = TmLam lm, ident=ident, inexpr=inexpr} ->
    let t = {body = TmLam lm, ident=ident, inexpr=inexpr} in
    -- Is the name one of the nodes in the call graph?
    if p t.ident then
      let newBody = lam_ _callCtx (None ())
                      (TmLam {lm with body = transformCallCtx p t.ident lm.body}) in
      TmLet {{t with body = newBody} with inexpr = transformCallCtx p prev t.inexpr}
    else TmLet {t with inexpr = transformCallCtx p prev t.inexpr}

  -- Same as for TmLet, but for each binding
  | TmRecLets t ->
    let handleLetExpr = lam le.
      if p le.ident then
        match le.body with TmLam lm then
          let newBody = lam_ _callCtx  (None ())
                          (TmLam {lm with body = transformCallCtx p le.ident lm.body})
          in {le with body = newBody}
        else error "Internal error: this letexpr should have a TmLam in its body"
      else le
    in
    TmRecLets {{t with bindings = foldl (lam a. lam b. cons (handleLetExpr b) a) [] t.bindings}
                with inexpr = transformCallCtx p prev t.inexpr}

  -- Insert call context as extra argument in function calls (not recursive ones)
  | TmLApp {lhs = TmVar v, rhs = rhs, id = id} ->
    if p v.ident then
      -- Append to call context (only if not recursive call)
      let isRecursiveCall = _eqn prev v.ident in
      let addToCallCtx = if isRecursiveCall then (var_ _callCtx)
                         else appf2_ (var_ _addCall) (var_ _callCtx) (symb_ id)
      in TmLApp {lhs = app_ (TmVar v) addToCallCtx, rhs = transformCallCtx p prev rhs, id = id}
    else
      TmLApp {lhs = TmVar v, rhs = transformCallCtx p prev rhs, id = id}

  -- Replace holes with a call to lookup function
  | LTmHole t ->
    TmApp {lhs = TmApp {lhs = var_ _lookup, rhs = var_ _callCtx}, rhs = t.id}

  | tm -> smap_Expr_Expr (transformCallCtx p prev) tm

  -- Initialise lookup table as a list of triples (id, path, startGuess)
  sem initLookupTable (publicFns : [Name]) =
  | tm ->
    let g = toCallGraph tm in
    let functionIDPairs = allFunHoles tm in
    let zip = zipWith (lam a. lam b. (a,b)) in
    foldl (lam acc. lam t.
               let fun = t.0 in
               let hole = match t.1 with LTmHole h then h else error "Internal error" in
               let depth = match hole.depth with TmConst {val = CInt n} then n.val
                           else error "Depth must be a constant integer" in
               let allPaths = eqPaths g fun depth publicFns in
               let idPathValTriples = map (lam path. {id=hole.id, path=path, value=hole.startGuess}) allPaths
               in concat acc idPathValTriples) --
           [] functionIDPairs

  -- Return a list of pairs (function name, hole) for all holes in tm
  sem allFunHoles =
  | tm -> allFunHoles2 _top tm

  sem allFunHoles2 (prev : Name) =
  | TmLet t ->
    let res_body =
      match t.body with TmLam lm
      then allFunHoles2 t.ident lm.body
      else allFunHoles2 prev t.body
    in concat res_body (allFunHoles2 prev t.inexpr)
 | LTmHole h ->
   [(prev, LTmHole h)]
 | tm -> sfold_Expr_Expr concat [] (smap_Expr_Expr (allFunHoles2 prev) tm)

end

lang PPrintLang = MExprPrettyPrint + LAppPrettyPrint + LHoleAstPrettyPrint
let expr2str = use PPrintLang in
  lam expr.
    match
      pprintCode 0 {nameMap = assocEmpty, strMap = assocEmpty, count = assocEmpty} expr
    with (_,str)
    then str else never

lang TestLang = MExpr + ContextAwareHoles + LAppEval + PPrintLang

mexpr

use TestLang in

-- Enable/disable printing
let printEnabled = false in
let print = if printEnabled then print else lam x. x in

-- Enable/disable eval
let evalEnabled = false in
let eval = lam expr. lam expected.
  if evalEnabled then eval {env = []} expr else expected in

-- Shorthand for symbolize
let symbolize = symbolize assocEmpty in

-- Prettyprinting
let pprint = lam ast.
  let _ = print "\n\n" in
  let _ = print (expr2str ast) in
  let _ = print "\n\n" in () in

-- Labeled application tests
let ast = app_ (var_ "foo") (int_ 1) in
let last = labelApps ast in

utest (match ast with TmApp t then t.lhs else error "error")
with (match last with TmLApp t then t.lhs else error "error") in

utest (match ast with TmApp t then t.rhs else error "error")
with (match last with TmLApp t then t.rhs else error "error") in

let _ = pprint last in

-- Transform & call graph tests
let dprintTransform = lam ast.
  -- Symbolize
  let ast = symbolize ast in
  -- Label applications
  let ast = labelApps ast in
  let _ = print "\n-------------- BEFORE TRANSFORMATION --------------" in
  let _ = pprint ast in
  let _ = print "-------------- AFTER TRANSFORMATION --------------" in
  let ast = transform [] ast in
  let _ = pprint ast in
  let _ = print "-------------- END OF TRANSFORMED AST --------------" in
  ast
in

-- Test that call graph of the ast has the string names in vs and return the
-- graph.
let callGraphTests = lam ast. lam strVs.
  let ast = labelApps (symbolize ast) in
  let g = toCallGraph ast in
  let vs = digraphVertices g in
  let symVs = map nameNoSym strVs in
  utest setIsSubsetEq nameEqStr symVs vs with true in
  g
in

-- Get a call graph using the strings of the names as vertices.
let callGraphStr = lam ng.
  let vs = digraphVertices ng in
  let es = digraphEdges ng in
  digraphAddEdges
    (map (lam t. (nameGetStr t.0, nameGetStr t.1, t.2)) es)
    (digraphAddVertices (map nameGetStr vs) (digraphEmpty eqstr eqs))
in

-- *** AST 0: a constant ***
let ast = symbolize (int_ 1) in
let tast = dprintTransform ast in
utest eval tast (int_ 1) with int_ 1 in

let g = toCallGraph ast in
utest digraphCountVertices g with 1 in
utest digraphCountEdges g with 0 in
utest digraphHasVertex _top g with true in

-- *** AST 1: One function ***
-- let foo = lam x. x in ()
let identity = let_ "foo" (lam_ "x" (None ()) (var_ "x")) in

let ast = identity in
let tast = dprintTransform ast in
utest eval tast unit_ with unit_ in
let g = callGraphTests ast ["foo", "top"] in
utest digraphCountEdges g with 0 in

-- *** AST 2: One function call ***
-- let foo = lam x. x in foo 1
let ast = bind_ identity (app_ (var_ "foo") (int_ 1)) in
let tast = dprintTransform ast in
utest eval tast (int_ 1) with int_ 1 in
-- graph: vs = [foo, top]. es = [top->foo].
let g = callGraphTests ast ["top", "foo"] in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" (callGraphStr g) with ["foo"] in

-- *** AST 3: Two functions, one function call ***
-- let foo = lam x. x in
-- let bar = lam x. (foo x) in ()
let bar = let_ "bar"
               (lam_ "x" (None ()) (app_ (var_ "foo") (var_ "x"))) in
let ast = bind_ identity bar in
let _ = dprintTransform ast in

-- graph: vs = [foo, bar, top], es = [bar->foo].
let g = callGraphTests ast ["foo", "bar", "top"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "bar" (callGraphStr g) with ["foo"] in

-- *** AST 4: 2 calls to the same function ***
-- let foo = lam x. x in
-- let bar = lam x. addi (foo x) (foo x) in
-- bar 1
let bar = let_ "bar"
               (lam_ "x" (None ())
               (addi_ (app_ (var_ "foo") (var_ "x"))
                      (app_ (var_ "foo") (var_ "x")))) in
let ast = bind_ (bind_ identity bar)
                (app_ (var_ "bar") (int_ 1)) in
let tast = dprintTransform ast in
utest eval tast (int_ 2) with int_ 2 in

let g = callGraphTests ast ["top", "foo", "bar"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in
utest digraphCountVertices g with 3 in
let gstr = callGraphStr g in
utest digraphSuccessors "bar" gstr with ["foo"] in
utest digraphSuccessors "top" gstr with ["bar"] in


-- *** AST 5: function with 2 arguments ***
--let foo = lam x. lam y. addi x y in
--foo 1 2
let ast =
    bind_
    (let_ "foo"
      (lam_ "x" (None ()) (
            lam_ "y" (None ()) (addi_ (var_ "x") (var_ "y"))
      )))
    (appf2_ (var_ "foo") (int_ 1) (int_ 2))
in
let tast = dprintTransform ast in
utest eval tast (int_ 3) with (int_ 3) in

let g = callGraphTests ast ["foo", "top"] in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" (callGraphStr g) with ["foo"] in

-- *** AST 6: inner function ***
--let foo = lam x.
--          let y = 1 in
--          let bar = lam y. addi x y in
--          bar 1
--foo 1
let ast = bind_
  (let_ "foo"
    (lam_ "x" (None ()) (
      bind_
        (let_ "y" (int_ 1))
        (bind_
          ((let_ "bar" (
              lam_ "y" (None ()) (
                bind_
                  (let_ "z" (int_ 2))
                  (addi_ (var_ "x") (var_ "y"))))))
          (app_ (var_ "bar") (int_ 1))))))
        (app_ (var_ "foo") (int_ 1))
in
let tast = dprintTransform ast in
utest eval tast (int_ 2) with int_ 2 in

let g = callGraphTests ast ["foo", "bar", "top"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 2 in

-- *** AST 7: inner functions again ***
-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in ()
let ast =
  let_ "foo" (lam_ "a" (None ()) (lam_ "b" (None ()) (
     let bar = let_ "bar" (lam_ "x" (None ())
                    (addi_ (var_ "b") (var_ "x"))) in
     let babar = let_ "babar" (int_ 3) in
     bind_ bar (
     bind_ babar (
       addi_ (app_ (var_ "bar")
                   (var_ "babar"))
             (var_ "a"))))))
in
let _ = dprintTransform ast in

let g = callGraphTests ast ["top", "foo", "bar"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 1 in
utest digraphIsSuccessor "bar" "foo" (callGraphStr g) with true in

-- *** AST 8: recursive function ***
-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
-- factorial 4
let factorial =
    reclets_add "factorial"
           (lam_ "n" (Some (TyInt {}))
                 (if_ (eqi_ (var_ "n") (int_ 0))
                      (int_ 1)
                      (muli_ (var_ "n")
                             (app_ (var_ "factorial")
                                   (subi_ (var_ "n")
                                          (int_ 1))))))
    reclets_empty
in
let ast = bind_ factorial (app_ (var_ "factorial") (int_ 2)) in
let tast = dprintTransform ast in
utest eval tast (int_ 2) with (int_ 2) in

let g = callGraphTests ast ["top", "factorial"] in
utest digraphCountEdges g with 2 in
let gstr = callGraphStr g in
utest digraphSuccessors "top" gstr with ["factorial"] in
utest digraphSuccessors "factorial" gstr with ["factorial"] in


-- *** AST 9: let with a function call ***
-- let foo = lam x. x in
-- let a = foo 1 in
-- a
let ast =
    let foo = let_ "foo" (lam_ "x" (None ()) (var_ "x")) in
    let a = let_ "a" (app_ (var_ "foo") (int_ 1)) in
    bind_ (bind_ foo a) (var_ "a")
in
let tast = dprintTransform ast in
utest eval tast (int_ 1) with int_ 1 in

let g = callGraphTests ast ["top", "foo"] in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" (callGraphStr g) with ["foo"] in


-- *** AST 10: chain of lets ***
-- let foo = lam x. x in
-- let a =
--     let b = 1 in
--     let c = lam x. foo x in
--     let d = 2 in
--     foo (c d) in
-- a
let ast =
    let foo = let_ "foo" (lam_ "x" (None ()) (var_ "x")) in
    let c = let_ "c" (lam_ "x" (None ()) (app_ (var_ "foo") (var_ "x"))) in
    let d = let_ "d" (int_ 2) in
    let a = let_ "a" (bind_ (let_ "b" (int_ 1)) (bind_ c (bind_ d (app_ (var_ "foo") (app_ (var_ "c") (var_ "d")))))) in
    let e = (var_ "a") in
    bind_ foo (bind_ a e) in
let tast = dprintTransform ast in
utest eval tast (int_ 2) with int_ 2 in

-- graph: vs = [top, foo, c], es = [c->foo, top->foo, top->c]
let g = callGraphTests ast ["foo", "top", "c"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in
let gstr = callGraphStr g in
utest digraphIsSuccessor "foo" "top" gstr with true in
utest digraphIsSuccessor "foo" "c" gstr with true in
utest digraphIsSuccessor "c" "top" gstr with true in

-- *** AST 11: mutual recursion
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
let even_odd =
    reclets_add "even" (lam_ "x" (None ())
                                 (if_ (eqi_ (var_ "x") (int_ 0))
                                      (true_)
                                      (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
   (reclets_add "odd" (lam_ "x" (None ())
                                (if_ (eqi_ (var_ "x") (int_ 1))
                                     (true_)
                                     (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
   reclets_empty)
in
let ast = bind_ even_odd (app_ (var_ "even") (int_ 2)) in
let tast = dprintTransform ast in
utest eval tast true_ with true_ in

let g = callGraphTests ast ["even", "odd"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in

-- *** AST 12: hidden function call
-- let bar = lam y. y in
-- let foo = lam f. lam x. f x in -- cannot see that foo calls bar
-- foo bar 1
let ast = bindall_ [
   let_ "bar" (lam_ "y" (None ()) (var_ "y")),
   let_ "foo" (lam_ "f" (None ()) (lam_ "x" (None ()) (app_ (var_ "f") (var_ "x")))),
   appf2_ (var_ "foo") (var_ "bar") (int_ 1)
] in
let tast = dprintTransform ast in

let g = callGraphTests ast ["bar", "foo"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 1 in

-- let foo = lam x.
--   if (LTmHole {id=s1}) then x
--   else let d = LTmHole {id=s2} in addi x d
-- in foo 42
let foo =
  let_ "foo"
       (lam_ "x" (None ())
                 (if_ ((hole_ tybool_ true_ (int_ 2))) (var_ "x")
                                     (bind_ (let_ "d" (hole_ tyint_ (int_ 1) (int_ 2)))
                                            (addi_ (var_ "x") (var_ "d")))))
in
let ast = bind_ foo (app_ (var_ "foo") (int_ 42)) in
let tast = dprintTransform ast in

let g = callGraphTests ast ["foo"] in

--let foo = lam x.
--          let d1 = LTmHole {id=s1} in
--          let bar = lam y.
--                      let d2 = LTmHole {id=s2} in
--                      addi d1 (addi d2 y) in
--          bar 1
--in foo 1
let ast = bind_
          (let_ "foo"
            (lam_ "x" (None ())
                      (bind_
                       ((bind_ (let_ "d1"(hole_ tyint_ (int_ 1) (int_ 2)))
                               (let_ "bar"
                                     (lam_ "y" (None ())
                                               (bind_ (let_ "d2" (hole_ tyint_ (int_ 3) (int_ 2)))
                                                      (addi_  (var_ "d1") (addi_ (var_ "d2") (var_ "y"))))))))
                       (app_ (var_ "bar") (int_ 1)))
            ))
          (app_ (var_ "foo") (int_ 1))
in
let tast = dprintTransform ast in

let g = callGraphTests ast ["foo", "bar"] in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 2 in

-- let bar = lam x.
--   let h = LTmHole {depth = 2, startGuess = true} in
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
let bar = let_ "bar" (lam_ "x" (None ()) (bind_ (let_ "h" (hole_ tybool_ true_ (int_ 2)))
                                                (if_ (var_ "h") (var_ "x") (addi_ (var_ "x") (int_ 1))))) in
let foo =
  reclets_add "foo" (lam_ "x" (None ()) (if_ (eqi_ (var_ "x") (int_ 1)) (app_ (var_ "foo") (int_ 2)) (app_ (var_ "bar") (var_ "x")))) reclets_empty in

let ast = bindall_ [bar, foo,
                    let_ "b1" (app_ (var_ "bar") (int_ 1)),
                    let_ "b2" (app_ (var_ "bar") (int_ 2)),
                    app_ (var_ "foo") (int_ 1)] in

let tast = dprintTransform ast in
let e = eval tast (int_ 2) in
utest e with int_ 2 in

()
