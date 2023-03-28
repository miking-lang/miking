include "mexpr/ast.mc"
include "mexpr/symbolize.mc"
include "mexpr/anf.mc"
include "mexpr/ast-builder.mc" -- for tests

include "digraph.mc"

include "name-info.mc"

-- Call graph creation for programs with holes.

-- Assumes that the AST is symbolized and in ANF.

type CallGraph = Digraph NameInfo NameInfo

let callGraphNames = lam cg.
  map (lam t : NameInfo. t.0) (digraphVertices cg)

let _callGraphNameSeq = lam seq.
  map (lam t : (NameInfo, NameInfo, NameInfo).
    ((t.0).0, (t.1).0, (t.2).0)) seq

let callGraphEdgeNames = lam cg.
  _callGraphNameSeq (digraphEdges cg)

-- The top of the call graph, has no incoming edges.
let callGraphTop = (nameSym "top", NoInfo ())

type Binding = use Ast in {ident : Name, body : Expr, info : Info}
let _handleLetVertex = use LamAst in
  lam f. lam letexpr : Binding.
    match letexpr.body with TmLam lm then
      cons (letexpr.ident, letexpr.info) (f [] lm.body)
    else f [] letexpr.body

let _handleApps = use AppAst in use VarAst in
  lam id. lam f. lam prev. lam g. lam name2info. lam app.
    recursive let appHelper = lam g. lam app.
      match app with TmApp {lhs = TmVar v, rhs = rhs} then
        let resLhs =
          if digraphHasVertex (v.ident, v.info) g then
            let correctInfo : Info = mapFindExn v.ident name2info in
            [(prev, (v.ident, correctInfo), id)]
          else []
        in concat resLhs (f g prev name2info [] rhs)
      else match app with TmApp {lhs = TmApp a, rhs = rhs} then
        let resLhs = appHelper g (TmApp a) in
        concat resLhs (f g prev name2info [] rhs)
      else match app with TmApp a then
        concat (f g prev name2info [] a.lhs) (f g prev name2info [] a.rhs)
      else never
  in appHelper g app

-- Construct a call graph from an AST. The nodes are named functions, and the
-- edges are calls to named functions. Complexity O(|V|*|F|), as we visit each
-- node exactly once and each time potentially perform a graph union operation,
-- which we assume has complexity O(|F|). V is the set of nodes in the AST and F
-- is the set of nodes in the call graph (i.e. set of functions in the AST).
lang HoleCallGraph = LetAst + AppAst + LamAst + RecLetsAst
  sem toCallGraph =
  | arg ->
    let gempty = digraphAddVertex callGraphTop
      (digraphEmpty nameInfoCmp nameInfoEq) in
    let g = digraphAddVertices (_findVertices [] arg) gempty in
    let infoMap = mapFromSeq nameCmp (digraphVertices g) in
    let edges = _findEdges g callGraphTop infoMap [] arg in
    digraphAddEdges edges g

  sem _findVertices (vertices: [NameInfo]) =
  | TmLet t ->
    concat
      (_handleLetVertex _findVertices
        {ident = t.ident, body = t.body, info = t.info})
      (_findVertices vertices t.inexpr)

  | TmRecLets t ->
    let res =
      foldl (lam acc. lam b : RecLetBinding.
               concat acc
                 (_handleLetVertex _findVertices
                   {ident = b.ident, body = b.body, info = b.info}))
            [] t.bindings
    in concat res (_findVertices vertices t.inexpr)

  | tm ->
--    sfold_Expr_Expr concat [] (smap_Expr_Expr _findVertices tm)
    sfold_Expr_Expr _findVertices vertices tm

  sem _findEdges (cg : CallGraph) (prev : NameInfo) (name2info : Map Name Info)
                 (edges : [(NameInfo, NameInfo, NameInfo)]) =
  | TmLet ({body = TmApp a} & t) ->
    let resBody = _handleApps (t.ident, t.info) _findEdges prev cg name2info t.body in
    concat resBody (_findEdges cg prev name2info edges t.inexpr)

  | TmLet ({body = TmLam lm} & t) ->
    let resBody = _findEdges cg (t.ident, t.info) name2info edges lm.body in
    concat resBody (_findEdges cg prev name2info [] t.inexpr)

  | TmRecLets t ->
    let res =
      let handleBinding = lam g. lam b : RecLetBinding.
        match b with { body = TmLam { body = lambody }, ident = ident, info = info } then
          _findEdges g (ident, info) name2info [] lambody
        else
          _findEdges g prev name2info [] b.body
      in foldl (lam acc. lam b. concat acc (handleBinding cg b)) [] t.bindings
    in concat res (_findEdges cg prev name2info edges t.inexpr)

  | tm ->
    sfold_Expr_Expr (_findEdges cg prev name2info) edges tm

end

lang TestLang = HoleCallGraph + MExprSym + MExprANF end

mexpr

use TestLang in

let anf = compose normalizeTerm symbolize in

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

()
