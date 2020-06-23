include "mexpr.mc"
include "pprint.mc"
include "digraph.mc"
include "string.mc"
include "ast-builder.mc"
include "eq-paths.mc"

-- This file contains implementations related to decision points. In particular,
-- it implements:
-- * A language fragment for decision points (HoleAst)
-- * An algorithm for AST -> call graph conversion (Ast2CallGraph fragment)
-- * Program transformations for programs with decision points (HolyCallGraph)

-- TODO: this file should probably be split into several ones.

lang HoleAst
  syn Expr =
  | TmHole {tp : Type,
            startGuess : Dyn,
            depth : Int}
end

lang HoleAstPrettyPrint = HoleAst + TypePrettyPrint
  sem pprintCode (indent : Int) =
  | TmHole h -> strJoin "" ["Hole (", getTypeStringCode indent h.tp, ", ",
                                      pprintCode indent h.startGuess, ", ",
                                      pprintCode indent h.depth, ")"]
end

-- Temporary workaround: uniquely labeled decision points
lang LHoleAst = HoleAst
  syn Expr =
  | LTmHole {tp : Type,
             startGuess : Dyn,
             depth : Int}

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
  sem pprintCode (indent : Int) =
  | LTmHole h -> pprintCode indent (toTmHole (LTmHole h))
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
end

lang LAppEval = LAppAst + AppEval
  sem eval (ctx : {env : Env}) =
  | TmLApp t -> eval ctx (toAppAst (TmLApp t))
end

lang LAppPrettyPrint = LAppAst + AppPrettyPrint
  sem pprintCode (indent : Int) =
  | TmLApp t ->
    let s = pprintCode indent (toAppAst (TmLApp t)) in
    s
end


-- Create a call graph from an AST.
-- * Vertices (represented as strings) are functions f defined as: let f = lam. ...
-- * There is an edge between f1 and f2 iff f1 calls f2: let f1 = lam. ... (f2 a)
-- * "top" is the top of the graph (i.e., no incoming edges)
-- * TODO: we assume that function names are unique

-- Helper functions
let handleLetVertex = use FunAst in
  lam letexpr. lam f.
    match letexpr.body with TmLam lm
    then cons letexpr.ident (f lm.body)
    else f letexpr.body

let handleLetEdge = use FunAst in
  lam letexpr. lam f. lam g. lam prev.
    match letexpr.body with TmLam lm
    then f g letexpr.ident lm.body
    else f g prev letexpr.body

lang Ast2CallGraph = LetAst + FunAst + RecLetsAst + LAppAst
  sem toCallGraph =
  | arg ->
    let top = "top" in
    let vs = findVertices arg in
    let gempty = digraphAddVertex top (digraphEmpty eqstr eqs) in
    let gvs = foldl (lam g. lam v. digraphAddVertex v g) gempty vs in
    findEdges gvs top arg

  -- Find all vertices of the call graph
  sem findVertices =
  | TmLet t ->
    let res_body = handleLetVertex t findVertices
    in concat res_body (findVertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam a. lam b. concat a (handleLetVertex b findVertices))
            [] t.bindings
    in concat res (findVertices t.inexpr)

  | tm ->
    sfold_Expr_Expr concat [] (smap_Expr_Expr findVertices tm)

  -- Find all edges of the call graph
  sem findEdges (cgraph : DiGraph) (prev : String) =
  | TmLet t ->
    -- let <fun-name> = lam. ...
    let res_body = handleLetEdge t findEdges cgraph prev
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
      foldl (lam g. lam b. digraphUnion g (handleLetEdge b findEdges g prev))
            cgraph t.bindings
    in findEdges res prev t.inexpr

  | tm ->
    sfold_Expr_Expr digraphUnion cgraph (smap_Expr_Expr (findEdges cgraph prev) tm)
end


lang ContextAwareHoles = Ast2CallGraph + LHoleAst + IntAst + SymbAst
  -- Transform the program
  sem transform =
  | tm ->
    -- Define hard coded constants
    let callCtxVar = "callCtx" in
    let callCtxTp = None () in
    let lookupTableVar = "lookupTable" in
    let lookupTableTp = None () in
    let lookupFunName = "lookup" in
    let addCallFunName = "addCall" in
    let maxDepthVar = "maxDepth" in
    let addCallFunName = "addCall" in
    let addCallFunTp = None () in

    -- Equip TmApps with unique labels
    let ltm = labelApps tm in

     -- Compute the call graph
    let callGraph = toCallGraph ltm in

    -- Do some transformations
    let transformed = transform2 (digraphVertices callGraph) "top" ltm in

    -- Define initial call context
    let defCallCtx = let_ callCtxVar callCtxTp (seq_ []) in

    -- Define initial lookup table
    let lookupTable = initLookupTable ltm in
    -- AST-ify the lookup table
    let defLookupTable =
      let_ lookupTableVar lookupTableTp
           (seq_ (map (lam t. tuple_ [t.0, (seq_ (map symb_ t.1)), t.2]) lookupTable))
    in

    -- Compute maximum depth of the decision points
    let maxDepth =
      match lookupTable with [] then 0
      else max subi (map (lam t. length t.1) lookupTable)
    in
    -- AST-ify the maxDepth variable
    let defMaxDepth = let_ maxDepthVar (None ()) (int_ maxDepth) in

    -- AST-ify filter
    -- recursive let filter = lam p. lam s.
    --   if (eqi 0 (length s)) then []
    --   else if p (head s) then
    --     let f = filter p (tail s)
    --     in cons (head s) f
    --   else (filter p (tail s))
    -- in
    let filter =
        reclets_add "filter" (None ())
                    (lam_ "p" (None ())
                          (lam_ "s" (None ())
                                (if_ (null_ (var_ "s"))
                                     (seq_ [])
                                     (if_ (app_ (var_ "p") (head_ (var_ "s")))
                                          (bind_ (let_ "f" (None ()) (appf2_ (var_ "filter") (var_ "p") (tail_ (var_ "s"))))
                                                 (cons_ (head_ (var_ "s")) (var_ "f")))
                                          (appf2_ (var_ "filter") (var_ "p") (tail_ (var_ "s")))) )))
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
      let_ "max" (None ())
           (lam_ "cmp" (None ()) (
             (lam_ "seq" (None ())
             (bindall_ [(reclets_add "work" (None ())
                                    (lam_ "e" (None ())
                                              (lam_ "seq" (None ())
                                                            (if_ (null_ (var_ "seq"))
                                                                 (var_ "e")
                                                                 (bindall_ [let_ "h" (None ()) (head_ (var_ "seq")),
                                                                            let_ "t" (None ()) (tail_ (var_ "seq")),
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
    --   else and (eq (head s1) (head s2)) (isPrefix eq (tail s1) (tail s2))
    -- in
    let isPrefix =
        reclets_add "isPrefix" (None ()) (
        (lam_ "eq" (None ())
              (lam_ "s1" (None ())
                    (lam_ "s2" (None ())
                               (if_ (null_ (var_ "s1"))
                                    (true_)
                                    (if_ (null_ (var_ "s2"))
                                         (false_)
                                         (and_ (appf2_ (var_ "eq") (head_ (var_ "s1")) (head_ (var_ "s2")))
                                               (appf3_ (var_ "isPrefix") (var_ "eq") (tail_ (var_ "s1")) (tail_ (var_ "s2")) ))) )))))
                                               reclets_empty
    in

    -- AST-ify isSuffix
    -- let isSuffix = lam eq. lam s1. lam s2.
    --     isPrefix eq (reverse s1) (reverse s2)
    -- in
    let isSuffix =
        let_ "isSuffix" (None ())
          ((lam_ "eq" (None ())
                (lam_ "s1" (None ())
                      (lam_ "s2" (None ())
                            (appf3_ (var_ "isPrefix")
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
      let_ "lookup" (None ())
           (lam_ "callCtx" (None ())
                 (lam_ "id" (None ())
                       (bindall_ [
                                  let_ "entries" (None ()) (
                                      appf2_ (var_ "filter")
                                             (lam_ "t" (None ()) (eqs_ (var_ "id") (proj_ (var_ "t") 0)))
                                             (var_ "lookupTable")),

                                  let_ "eqs" (None ()) (lam_ "x" (None ()) (lam_ "y" (None ()) (eqs_ (var_ "x") (var_ "y")))),
                                  let_ "entriesSuffix" (None ())
                                       (appf2_ (var_ "filter")
                                               (lam_ "t" (None ()) (appf3_ (var_ "isSuffix") (var_ "eqs") (proj_ (var_ "t") 1) (var_ "callCtx")))
                                               (var_ "entries")),

                                  let_ "cmp" (None ())
                                             (lam_ "t1" (None ())
                                                        (lam_ "t2" (None ())
                                                                   (appf2_ (var_ "subi")
                                                                           (length_ (proj_ (var_ "t1") 1))
                                                                           (length_ (proj_ (var_ "t2") 1))))),

                                  let_ "entryLongestSuffix" (None ()) (appf2_ (var_ "max") (var_ "cmp") (var_ "entriesSuffix")),
                                  proj_ (var_ "entryLongestSuffix") 2])))
    in
    let defLookup = bindall_ [isPrefix, isSuffix, max, filter, lookup] in

    -- Add a function call to the call context:
    -- let addCall = lam callCtx. lam lbl.
    --   if gti (length callCtx) maxDepth then
    --     snoc (tail callCtx) lbl
    --   else
    --     snoc callCtx lbl
    let defAddCall = let lblVarName = "lbl" in
      let_ addCallFunName addCallFunTp (
           lam_ callCtxVar (None ()) (
                lam_ lblVarName (None ()) (
                     if_ (lti_ (length_ (var_ callCtxVar)) (var_ maxDepthVar))
                         (snoc_ (var_ callCtxVar) (var_ lblVarName))
                         (snoc_ (tail_ (var_ callCtxVar)) (var_ lblVarName)))))
    in

    -- Put all the pieces together
    bindall_ [defLookupTable,
              defCallCtx,
              defMaxDepth,
              defAddCall,
              defLookup,
              transformed]

  -- Do some transformations (see paper for example)
  sem transform2 (fs : [String]) (prev : String) =
  -- Add call context as extra argument in function definitions
  | TmLet {body = TmLam lm, ident=ident, tpe=tpe, inexpr=inexpr} ->
    let t = {body = TmLam lm, ident=ident, tpe=tpe, inexpr=inexpr} in
    -- Is the name one of the nodes in the call graph?
    if optionIsSome (find (eqstr t.ident) fs) then
      let newBody = lam_ "callCtx" (None ())
                         (TmLam {lm with body = transform2 fs t.ident lm.body}) in
      TmLet {{t with body = newBody} with inexpr = transform2 fs prev t.inexpr}
    else TmLet {t with inexpr = transform2 fs prev t.inexpr}

  -- Same as for TmLet, but for each binding
  | TmRecLets t ->
    let handleLetExpr = lam le.
      if optionIsSome (find (eqstr le.ident) fs) then
        match le.body with TmLam lm then
          let newBody = lam_ "callCtx"  (None ())
                             (TmLam {lm with body = transform2 fs le.ident lm.body})
          in {le with body = newBody}
        else error "Internal error: this letexpr should have a TmLam in its body"
      else le
    in
    -- FIXME: Really do it for all bindings, not just the first
    TmRecLets {{t with bindings = [handleLetExpr (get t.bindings 0)]}
               with inexpr = transform2 fs prev t.inexpr}

  -- Insert call context as extra argument in function calls (not recursive ones)
  | TmLApp {lhs = TmVar v, rhs = rhs, id = id} ->
    if optionIsSome (find (eqstr v.ident) fs) then
      -- Append to call context (only if not recursive call)
      let isRecursiveCall = eqstr prev v.ident in
      let addToCallCtx = if isRecursiveCall then (var_ "callCtx")
                         else appf2_ (var_ "addCall") (var_ "callCtx") (symb_ id)
      in TmLApp {lhs = app_ (TmVar v) addToCallCtx, rhs = transform2 fs prev rhs, id = id}
    else
      TmLApp {lhs = TmVar v, rhs = transform2 fs prev rhs, id = id}

  -- Replace holes with a call to lookup function
  | LTmHole t ->
    TmApp {lhs = TmApp {lhs = var_ "lookup", rhs = var_ "callCtx"}, rhs = t.id}

  | tm -> smap_Expr_Expr (transform2 fs prev) tm

  -- Initialise lookup table as a list of triples (id, path, startGuess)
  sem initLookupTable =
  | tm ->
    let g = toCallGraph tm in
    let functionIDPairs = allFunHoles tm in
    let zip = zipWith (lam a. lam b. (a,b)) in
    foldl (lam acc. lam t.
               let fun = t.0 in
               let hole = match t.1 with LTmHole h then h else error "Internal error" in
               let depth = match hole.depth with TmConst {val = CInt n} then n.val
                           else error "Depth must be a constant integer" in
               let allPaths = eqPaths g fun depth in
               let idPathValTriples = map (lam path. (hole.id, path, hole.startGuess)) allPaths
               in concat acc idPathValTriples)
           [] functionIDPairs

  -- Return a list of pairs (function name, hole) for all holes in tm
  sem allFunHoles =
  | tm -> allFunHoles2 "top" tm

  sem allFunHoles2 (prev : String) =
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


lang TestLang = MExpr + MExprPrettyPrint + ContextAwareHoles + LAppPrettyPrint +
                LAppEval + LHoleAstPrettyPrint

mexpr

use TestLang in

-- Enable/disable printing
let printEnabled = false in
let print = if printEnabled then print else lam x. x in

let ctx = {env = []} in

-- Prettyprinting
let pprint = lam ast.
  let _ = print "\n\n" in
  let _ = print (pprintCode 0 ast) in
  let _ = print "\n\n" in () in

-- Test labeling of TmApp
let ast = app_ (var_ "foo") (int_ 1) in
let last = labelApps ast in

utest (match ast with TmApp t then t.lhs else error "error")
with (match last with TmLApp t then t.lhs else error "error") in

utest (match ast with TmApp t then t.rhs else error "error")
with (match last with TmLApp t then t.rhs else error "error") in

let _ = pprint last in

-- Tests of AST:s. For each AST we create a call graph and apply the transform.

-- *** AST 0: a constant ***
let ast = int_ 1 in
let ast = labelApps ast in

let _ = print "AST 0\n" in
let _ = pprint ast in
let _ = print "Transformed AST 0\n" in
let tast = transform ast in
let _ = pprint tast in

let g = toCallGraph ast in
utest digraphCountVertices g with 1 in
utest digraphCountEdges g with 0 in
utest digraphHasVertex "top" g with true in


-- *** AST 1: One function ***
-- let foo = lam x. x in ()
let id_func = let_ "foo"
                    (None ())
                    (lam_ "x" (None ()) (var_ "x")) in

-- print the AST
let ast = bind_ id_func unit_ in
let ast = labelApps ast in
let _ = print "AST 1\n" in
let _ = pprint ast in
let _ = print "Transformed AST 1\n" in
let tast = transform ast in
let _ = pprint tast in

let g = toCallGraph ast in
utest digraphCountVertices g with 2 in
utest digraphCountEdges g with 0 in
utest digraphHasVertex "foo" g with true in
utest digraphHasVertex "top" g with true in

-- *** AST 2: One function call ***
-- let foo = lam x. x in foo 1
let ast = bind_ id_func (app_ (var_ "foo") (int_ 1)) in
let ast = labelApps (bind_ id_func (addi_ (app_ (var_ "foo") (int_ 1)) (int_ 2))) in
let _ = print "AST 2\n" in
let _ = pprint ast in
let _ = print "Transformed AST 2\n" in
let tast = transform ast in
let _ = pprint tast in

-- graph: vs = [foo, top]. es = [top->foo].
let g = toCallGraph ast in
utest digraphHasVertices ["top", "foo"] g with true in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" g with ["foo"] in


-- *** AST 3: Two functions, one function call ***
-- let foo = lam x. x in
-- let bar = lam x. (foo x) in ()
let bar = let_ "bar"
               (None ())
               (lam_ "x" (None ()) (app_ (var_ "foo") (var_ "x"))) in
let ast = labelApps (bind_ id_func bar) in
let _ = print "AST 3\n" in
let _ = pprint ast in
let _ = print "Transformed AST 3\n" in
let tast = transform ast in
let _ = pprint tast in

-- graph: vs = [foo, bar, top], es = [bar->foo].
let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphHasVertices ["foo", "bar"] g with true in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "bar" g with ["foo"] in


-- *** AST 4: 2 calls to the same function ***
-- let foo = lam x. x in
-- let bar = lam x. addi (foo x) (foo x) in
-- bar 1
let bar = let_ "bar" (None ())
               (lam_ "x" (None ())
               (addi_ (app_ (var_ "foo") (var_ "x"))
                      (app_ (var_ "foo") (var_ "x")))) in
let ast = bind_ (bind_ id_func bar)
                (app_ (var_ "bar") (int_ 1)) in
let ast = labelApps ast in

utest eval ctx ast with int_ 2 in
let _ = print "AST 4\n" in
let _ = pprint ast in
let _ = print "Transformed AST 4\n" in
let tast = transform ast in
let _ = pprint tast in

let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in
utest digraphCountVertices g with 3 in
utest digraphHasVertices ["top", "foo", "bar"] g with true in
utest digraphSuccessors "bar" g with ["foo"] in
utest digraphSuccessors "top" g with ["bar"] in


-- *** AST 5: function with 2 arguments ***
--let foo = lam x. lam y. addi x y in
--foo 1 2
let ast =
    bind_
    (let_ "foo" (None ())
                (lam_ "x" (None ()) (
                      lam_ "y" (None ()) (addi_ (var_ "x") (var_ "y"))
                )))
    (appf2_ (var_ "foo") (int_ 1) (int_ 2))
in
let ast = labelApps ast in
let _ = print "Transformed AST 5\n" in
let tast = transform ast in
let _ = pprint tast in

let _ = print "AST 5\n" in
let _ = pprint ast in
utest eval ctx ast with (int_ 3) in

let g = toCallGraph ast in
utest digraphHasVertices ["foo", "top"] g with true in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" g with ["foo"] in


-- *** AST 6: inner function ***
--let foo = lam x.
--          let y = 1 in
--          let bar = lam y. addi x y in
--          bar 1
--foo 1
let ast = bind_
          (let_ "foo" (None ())
                      (lam_ "x" (None ()) (
                                bind_
                                  (let_ "y" (None ()) (int_ 1))
                                  (bind_
                                    ((let_ "bar" (None ()) (
                                                lam_ "y" (None ()) (
                                                          bind_
                                                          (let_ "z" (None ()) (int_ 2))
                                                          (addi_ (var_ "x") (var_ "y"))))))
                                    (app_ (var_ "bar") (int_ 1)))
                                )))
          (app_ (var_ "foo") (int_ 1))
in
let ast = labelApps ast in

let _ = print "AST 6\n" in
let _ = pprint ast in
let _ = print "Transformed AST 6\n" in
let tast = transform ast in
let _ = pprint tast in
utest eval ctx ast with int_ 2 in

let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 2 in


-- *** AST 7: inner functions again ***
-- let foo = lam a. lam b.
--     let bar = lam x. addi b x in
--     let babar = 3 in
--     addi (bar babar) a
-- in ()
let ast =
  let_ "foo" (None ()) (lam_ "a" (None ()) (lam_ "b" (None ()) (
     let bar = let_ "bar" (None ()) (lam_ "x" (None ())
                    (addi_ (var_ "b") (var_ "x"))) in
     let babar = let_ "babar" (None ()) (int_ 3) in
     bind_ bar (
     bind_ babar (
       addi_ (app_ (var_ "bar")
                   (var_ "babar"))
             (var_ "a"))))))
in
let ast = labelApps ast in

let _ = print "AST 7\n" in
let _ = pprint ast in
let _ = print "Transformed AST 7\n" in
let tast = transform ast in
let _ = pprint tast in

let g = toCallGraph ast in
utest digraphHasVertices ["top", "foo"] g with true in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 1 in
utest digraphIsSuccessor "bar" "foo" g with true in


-- *** AST 8: recursive function ***
-- recursive let factorial = lam n.
--     if eqi n 0 then
--       1
--     else
--       muli n (factorial (subi n 1))
-- in
-- factorial 4
let factorial =
    reclets_add "factorial" (Some (TyInt {}))
           (lam_ "n" (Some (TyInt {}))
                 (if_ (eqi_ (var_ "n") (int_ 0))
                      (int_ 1)
                      (muli_ (var_ "n")
                             (app_ (var_ "factorial")
                                   (subi_ (var_ "n")
                                          (int_ 1))))))
    reclets_empty
in
let ast = bind_ factorial (app_ (var_ "factorial") (int_ 4)) in
let ast = labelApps ast in

let _ = print "AST 8\n" in
let _ = pprint ast in
let _ = print "Transformed AST 8\n" in
let tast = transform ast in
let _ = pprint tast in
utest eval ctx ast with (int_ 24) in

let g = toCallGraph ast in
utest digraphHasVertices ["top", "factorial"] g with true in
utest digraphCountEdges g with 2 in
utest digraphSuccessors "top" g with ["factorial"] in
utest digraphSuccessors "factorial" g with ["factorial"] in


-- *** AST 9: let with a function call ***
-- let foo = lam x. x in
-- let a = foo 1 in
-- a
let ast =
    let foo = let_ "foo" (None ()) (lam_ "x" (None ()) (var_ "x")) in
    let a = let_ "a" (None ()) (app_ (var_ "foo") (int_ 1)) in
    bind_ (bind_ foo a) (var_ "a")
in
let ast = labelApps ast in

let _ = print "AST 9\n" in
let _ = pprint ast in
let _ = print "Transformed AST 9\n" in
let tast = transform ast in
let _ = pprint tast in
utest eval ctx ast with int_ 1 in

let g = toCallGraph ast in
utest digraphHasVertices ["top", "foo"] g with true in
utest digraphCountEdges g with 1 in
utest digraphSuccessors "top" g with ["foo"] in


-- *** AST 10: chain of lets ***
-- let foo = lam x. x in
-- let a =
--     let b = 1 in
--     let c = lam x. foo x in
--     let d = 2 in
--     foo (c d) in
-- a
let ast =
    let foo = let_ "foo" (None ()) (lam_ "x" (None ()) (var_ "x")) in
    let c = let_ "c" (None ())
                     (lam_ "x" (None ()) (app_ (var_ "foo") (var_ "x"))) in
    let d = let_ "d" (None()) (int_ 2) in
    let a = let_ "a" (None ())
                     (bind_ (let_ "b" (None ()) (int_ 1)) (bind_ c (bind_ d (app_ (var_ "foo") (app_ (var_ "c") (var_ "d")))))) in

    let e = (var_ "a") in
    bind_ foo (bind_ a e) in

let ast = labelApps ast in

let _ = print "AST 10\n" in
let _ = pprint ast in
let _ = print "Transformed AST 10\n" in
let tast = transform ast in
let _ = pprint tast in

-- graph: vs = [top, foo, c], es = [c->foo, top->foo, top->c]
utest eval ctx ast with int_ 2 in
let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in
utest digraphIsSuccessor "foo" "top" g with true in
utest digraphIsSuccessor "foo" "c" g with true in
utest digraphIsSuccessor "c" "top" g with true in


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
-- in even 6
let even_odd =
    reclets_add "even" (None ())
                       (lam_ "x" (None ())
                                 (if_ (eqi_ (var_ "x") (int_ 0))
                                      (true_)
                                      (app_ (var_ "odd") (subi_ (var_ "x") (int_ 1)))))
   (reclets_add "odd" (None ())
                      (lam_ "x" (None ())
                                (if_ (eqi_ (var_ "x") (int_ 1))
                                     (true_)
                                     (app_ (var_ "even") (subi_ (var_ "x") (int_ 1)))))
   reclets_empty)
in
let ast = bind_ even_odd (app_ (var_ "even") (int_ 6)) in
let ast = labelApps ast in

let _ = print "AST 11: mutual recursion" in
let _ = pprint ast in
let _ = print "Transformed AST 11\n" in
let tast = transform ast in
let _ = pprint tast in
utest eval ctx ast with true_ in

let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 3 in

-- *** AST 12: hidden function call
-- let bar = lam y. y in
-- let foo = lam f. lam x. f x in -- cannot see that foo calls bar
-- foo bar 1
let ast = bindall_ [
   let_ "bar" (None ()) (lam_ "y" (None ()) (var_ "y")),
   let_ "foo" (None ()) (lam_ "f" (None ())
                                  (lam_ "x" (None ()) (app_ (var_ "f") (var_ "x")))),
   appf2_ (var_ "foo") (var_ "bar") (int_ 1)
] in
let ast = labelApps ast in

let _ = print "AST 12: hidden function call" in
let _ = pprint ast in
let _ = print "Transformed AST 12\n" in
let tast = transform ast in
let _ = pprint tast in
utest eval ctx ast with int_ 1 in

let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 1 in


-- let foo = lam x.
--   if (LTmHole {id=s1}) then x
--   else let d = LTmHole {id=s2} in addi x d
-- in foo 42
let foo =
  let_ "foo"
       (None ())
       (lam_ "x" (None ())
                 (if_ ((hole_ tybool_ true_ (int_ 2))) (var_ "x")
                                     (bind_ (let_ "d" (None()) (hole_ tyint_ (int_ 1) (int_ 2)))
                                            (addi_ (var_ "x") (var_ "d")))))
in
let ast = bind_ foo (app_ (var_ "foo") (int_ 42)) in
let ast = labelApps ast in
let _ = print "If-then-else with holes\n" in
let _ = pprint ast in
let tast = transform ast in
let _ = pprint tast in

let g = toCallGraph ast in
let labelTopFoo = (get (digraphEdgesTo "foo" g) 0).2 in

--let foo = lam x.
--          let d1 = LTmHole {id=s1} in
--          let bar = lam y.
--                      let d2 = LTmHole {id=s2} in
--                      addi d1 (addi d2 y) in
--          bar 1
--in foo 1
let ast = bind_
          (let_ "foo" (None ())
                     (lam_ "x" (None ())
                               (bind_
                                ((bind_ (let_ "d1" (None ()) (hole_ tyint_ (int_ 1) (int_ 2)))
                                        (let_ "bar" (None ())
                                                    (lam_ "y" (None ())
                                                              (bind_ (let_ "d2" (None ()) (hole_ tyint_ (int_ 3) (int_ 2)))
                                                                     (addi_  (var_ "d1") (addi_ (var_ "d2") (var_ "y"))))))))
                                (app_ (var_ "bar") (int_ 1)))
                     ))
          (app_ (var_ "foo") (int_ 1))
in
let ast = labelApps ast in
let _ = print "AST with holes\n" in
let _ = pprint ast in

let _ = print "Transformed AST with holes\n" in
let tast = transform ast in
let _ = pprint tast in


let g = toCallGraph ast in
utest digraphCountVertices g with 3 in
utest digraphCountEdges g with 2 in

-- AST from the paper
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
let bar = let_ "bar" (None ()) (lam_ "x" (None ()) (bind_ (let_ "h" tybool_ (hole_ tybool_ true_ (int_ 2)))
                                                   (if_ (var_ "h") (var_ "x") (addi_ (var_ "x") (int_ 1))))) in
let foo =
  reclets_add "foo" (None ()) (lam_ "x" (None ()) (if_ (eqi_ (var_ "x") (int_ 1)) (app_ (var_ "foo") (int_ 2)) (app_ (var_ "bar") (var_ "x")))) reclets_empty in

let ast = bindall_ [bar, foo,
                    let_ "b1" tyint_ (app_ (var_ "bar") (int_ 1)),
                    let_ "b2" tyint_ (app_ (var_ "bar") (int_ 2)),
                    app_ (var_ "foo") (int_ 1)] in

let _ = print "\nAST from paper\n" in
let _ = pprint ast in

let _ = print "\nTransformed AST from paper\n" in
let tast = transform ast in
let _ = pprint tast in

-- Takes ~90 s to evaluate
--let e = eval ctx tast in
--utest e with int_ 2 in

()
