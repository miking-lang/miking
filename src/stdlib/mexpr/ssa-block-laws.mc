-- Tests for the laws documented in `ssa-block.mc`, checked for every
-- combination of a small, fixed set of sample values for each free
-- variable of a law.
--
-- Two `Expr`s are compared by evaluating them in a context that binds
-- the sample variables and a log (a `ref` of integers that samples
-- append to), then comparing the printed value and log. Two
-- `SSABlock`s are compared by placing them in each of a few
-- `SSABlock` contexts, finalizing, and comparing the resulting
-- `Expr`s.
--
-- Block samples are functions taking an escape block: in a block
-- context it escapes an `ssaBlock` of the context, at the `Expr`
-- level (where nothing binds a label) it is an `ssaReturn` instead.

include "ssa-block.mc"
include "pprint.mc"
include "ast-builder.mc"
include "eval.mc"
include "map.mc"
include "name.mc"
include "seq.mc"
include "string.mc"
include "bool.mc"
include "error.mc"

lang SSABlockLawTest = SSABlockLang + MExprEval + MExprPrettyPrint end

mexpr

use SSABlockLawTest in

let x = nameSym "x" in
let y = nameSym "y" in
let c = nameSym "c" in
-- Bound by `construct` samples, never ssa-bound
let z = nameSym "z" in
-- Fresh name for the fresh-variable `ssaMatch` law
let w = nameSym "w" in
let logN = nameSym "log" in

-- Untyped, but checks that every join parameter gets an ssa-binding
let opts =
  { ssaFinalizeOptsUntyped () with
    joinParam = lam args.
      if any (lam s. match s with SSADef _ then true else false) args.sources then () else
        errorSingle [args.info] (concat "No ssa-binding reaches the join parameter " (nameGetStr args.name))
  } in
let fin = lam block. lam fall. ssaFinalize opts block fall in

-- === Observation ===

let logE = lam k. lam v.
  semi_ (modref_ (nvar_ logN) (snoc_ (deref_ (nvar_ logN)) (int_ k))) v in

let observe : Expr -> String = lam tm.
  let r = nameSym "r" in
  let tm = bindall_
    [ nulet_ logN (ref_ (seq_ []))
    , nulet_ x (int_ 1), nulet_ y (int_ 2), nulet_ c (int_ 0)
    , nulet_ r tm
    ]
    (utuple_ [nvar_ r, deref_ (nvar_ logN)]) in
  mexprToString (eval (evalCtxEmpty ()) tm) in

let exprEq : Expr -> Expr -> Bool = lam l. lam r. eqString (observe l) (observe r) in

let state = addi_ (muli_ (nvar_ c) (int_ 10000))
  (addi_ (muli_ (nvar_ x) (int_ 100)) (nvar_ y)) in
let init = ssaSeq [ssaSet x (int_ 1), ssaSet y (int_ 2), ssaSet c (int_ 0)] in

-- Each context takes the hole as a function of an escape block.
let contexts : [(SSABlock -> SSABlock) -> SSABlock] =
  [ lam h. ssaSeq [init, ssaBlock h, ssaSet y (addi_ (nvar_ y) (int_ 5))]
  , lam h. ssaSeq
    [ init
    , ssaMatch (nvar_ x) (pint_ 1) (ssaSet y (int_ 3)) (ssaEmpty ())
    , ssaBlock (lam e. ssaSeq [h e, ssaRun (logE 99 (int_ 0))])
    , ssaMatch (nvar_ y) (pint_ 3) (ssaSet x (addi_ (nvar_ x) (int_ 10))) (ssaEmpty ())
    ]
  , lam h. ssaSeq
    [ init
    , ssaBlock (lam e. ssaLoop (ssaSeq
      [ ssaSet c (addi_ (nvar_ c) (int_ 1))
      , ssaMatch (gti_ (nvar_ c) (int_ 2)) ptrue_ e (ssaEmpty ())
      , h e
      ]))
    ]
  ] in

let blockEq : (SSABlock -> SSABlock) -> (SSABlock -> SSABlock) -> Bool = lam l. lam r.
  forAll (lam ctx. exprEq (fin (ctx l) state) (fin (ctx r) state)) contexts in

-- The escape used at the `Expr` level
let topExit = ssaReturn (int_ 4444) in

-- === Samples ===

let blocks : [(String, SSABlock -> SSABlock)] =
  [ ("empty", lam. ssaEmpty ())
  , ("setx", lam. ssaSet x (addi_ (nvar_ x) (int_ 1)))
  , ("sety-log", lam. ssaSet y (logE 1 (muli_ (nvar_ y) (int_ 2))))
  , ("run", lam. ssaRun (logE 2 (int_ 0)))
  , ("ret", lam. ssaReturn (addi_ (int_ 1000) (nvar_ x)))
  , ("esc", lam e. e)
  , ("match", lam.
      ssaMatch (nvar_ x) (pint_ 1) (ssaSet y (int_ 5)) (ssaRun (logE 3 (int_ 0))))
  , ("match-ret", lam.
      ssaMatch (nvar_ y) (pint_ 2) (ssaReturn (int_ 2000)) (ssaSet x (int_ 4)))
  , ("match-esc", lam e.
      ssaMatch (gti_ (nvar_ x) (int_ 3)) ptrue_ e (ssaSet y (addi_ (nvar_ y) (int_ 10))))
  , ("match-bind", lam.
      ssaMatch (addi_ (nvar_ x) (int_ 1)) (npvar_ y) (ssaEmpty ()) (ssaEmpty ()))
  , ("setpar-swap", lam.
      ssaSetPar (mapFromSeq nameCmp [(x, nvar_ y), (y, nvar_ x)]))
  , ("loop", lam. ssaBlock (lam brk. ssaLoop (ssaSeq
      [ ssaMatch (gti_ (nvar_ x) (int_ 5)) ptrue_ brk (ssaEmpty ())
      , ssaSet x (addi_ (nvar_ x) (int_ 2))
      ])))
  , ("callcc-2", lam. ssaCallCC (lam k.
      addi_ (k (ssaSet x (int_ 7))) (k (ssaSet y (int_ 8)))))
  , ("callcc-bind", lam. ssaCallCC (lam k.
      bind_ (nulet_ z (logE 4 (int_ 3)))
        (k (ssaSet x (addi_ (nvar_ z) (nvar_ x))))))
  , ("callcc-0", lam. ssaCallCC (lam. int_ 3000))
  ] in
let smallBlocks = filter
  (lam b. any (eqString b.0) ["empty", "setx", "ret", "esc", "match-ret", "callcc-2"])
  blocks in

-- Loop bodies that eventually leave the loop in every context
let loopBodies : [(String, SSABlock -> SSABlock)] =
  [ ("esc", lam e. ssaSeq
      [ ssaMatch (gti_ (nvar_ x) (int_ 5)) ptrue_ e (ssaEmpty ())
      , ssaSet x (addi_ (nvar_ x) (int_ 1))
      ])
  , ("ret", lam. ssaSeq
      [ ssaSet y (addi_ (nvar_ y) (int_ 1))
      , ssaMatch (gti_ (nvar_ y) (int_ 4)) ptrue_
          (ssaReturn (muli_ (nvar_ y) (int_ 1000))) (ssaEmpty ())
      ])
  , ("log", lam e. ssaSeq
      [ ssaRun (logE 8 (nvar_ x))
      , ssaSet x (addi_ (nvar_ x) (int_ 1))
      , ssaMatch (gti_ (nvar_ x) (int_ 4)) ptrue_ e (ssaEmpty ())
      ])
  , ("callcc", lam e. ssaSeq
      [ ssaMatch (gti_ (nvar_ x) (int_ 3)) ptrue_ e (ssaEmpty ())
      , ssaCallCC (lam k.
          addi_ (k (ssaSet x (addi_ (nvar_ x) (int_ 1))))
                (k (ssaSet x (addi_ (nvar_ x) (int_ 2)))))
      ])
  ] in

let exprs : [(String, Expr)] =
  [ ("3", int_ 3)
  , ("x", nvar_ x)
  , ("y+1", addi_ (nvar_ y) (int_ 1))
  , ("log", logE 5 (int_ 4))
  ] in
let smallExprs = filter (lam e. any (eqString e.0) ["x", "log"]) exprs in

let pats : [(String, Pat)] =
  [ ("1", pint_ 1)
  , ("3", pint_ 3)
  , ("_", pvarw_)
  , ("x", npvar_ x)
  , ("y", npvar_ y)
  ] in
let smallPats = filter (lam p. any (eqString p.0) ["1", "_", "y"]) pats in

let falls : [(String, Expr)] =
  [ ("0", int_ 0)
  , ("state", state)
  , ("log", logE 6 (nvar_ y))
  ] in

let names : [(String, Name)] = [("x", x), ("y", y)] in

let setPars : [(String, Map Name Expr)] =
  [ ("x=3", mapFromSeq nameCmp [(x, int_ 3)])
  , ("swap", mapFromSeq nameCmp [(x, nvar_ y), (y, nvar_ x)])
  , ("x=y+1,y=5", mapFromSeq nameCmp [(x, addi_ (nvar_ y) (int_ 1)), (y, int_ 5)])
  ] in

let constructs : [(String, (SSABlock -> Expr) -> Expr)] =
  [ ("none", lam. int_ 3000)
  , ("once", lam k. k (ssaSet x (int_ 6)))
  , ("twice", lam k. addi_ (k (ssaSet x (int_ 7))) (k (ssaSet y (int_ 8))))
  , ("bind", lam k. bind_ (nulet_ z (int_ 3)) (k (ssaSet x (nvar_ z))))
  , ("log-ret", lam k. logE 7 (k (ssaReturn (int_ 5))))
  ] in

-- === Combinations ===

let cross : all a. all b. [(String, a)] -> [(String, b)] -> [(String, (a, b))]
  = lam as. lam bs.
    join (map (lam a. map (lam b. (join [a.0, " ", b.0], (a.1, b.1))) bs) as) in
let failures : all a. [(String, a)] -> (a -> Bool) -> [String]
  = lam combos. lam pred.
    map (lam c. c.0) (filter (lam c. not (pred c.1)) combos) in
let eqStrs = eqSeq eqString in

-- === Laws ===

-- ssaChain a (ssaChain b c) = ssaChain (ssaChain a b) c
utest failures (cross smallBlocks (cross smallBlocks smallBlocks))
  (lam t. match t with (a, (b, c)) in
    blockEq
      (lam e. ssaChain (a e) (ssaChain (b e) (c e)))
      (lam e. ssaChain (ssaChain (a e) (b e)) (c e)))
with [] using eqStrs in

-- ssaFinalize (ssaEmpty ()) x = x
utest failures exprs (lam x. exprEq (fin (ssaEmpty ()) x) x)
with [] using eqStrs in

-- ssaChain (ssaEmpty ()) a = ssaChain a (ssaEmpty ()) = a
utest failures blocks
  (lam a.
    and (blockEq (lam e. ssaChain (ssaEmpty ()) (a e)) a)
        (blockEq (lam e. ssaChain (a e) (ssaEmpty ())) a))
with [] using eqStrs in

-- ssaFinalize (ssaReturn a) b = a
utest failures (cross exprs falls)
  (lam t. match t with (a, b) in exprEq (fin (ssaReturn a) b) a)
with [] using eqStrs in

-- ssaChain (ssaReturn x) a = ssaReturn x
utest failures (cross exprs blocks)
  (lam t. match t with (x, a) in
    blockEq (lam e. ssaChain (ssaReturn x) (a e)) (lam. ssaReturn x))
with [] using eqStrs in

-- (*) ssaReturn x = ssaCallCC (lam. x)
utest failures exprs
  (lam x. blockEq (lam. ssaReturn x) (lam. ssaCallCC (lam. x)))
with [] using eqStrs in

-- ssaFinalize (ssaChain (ssaRun x) a) b = semi_ x (ssaFinalize a b)
utest failures (cross exprs (cross blocks falls))
  (lam t. match t with (x, (a, b)) in
    exprEq
      (fin (ssaChain (ssaRun x) (a topExit)) b)
      (semi_ x (fin (a topExit) b)))
with [] using eqStrs in

-- ssaSetPar {n_1 -> x_1, ..., n_k -> x_k} =
--   ssaMatch (utuple_ [x_1, ..., x_k]) (ptuple_ [npvar_ n_1, ..., npvar_ n_k]) (ssaEmpty ()) (ssaEmpty ())
utest failures setPars
  (lam m.
    let bs = mapBindings m in
    blockEq
      (lam. ssaSetPar m)
      (lam. ssaMatch
        (utuple_ (map (lam b. b.1) bs))
        (ptuple_ (map (lam b. npvar_ b.0) bs))
        (ssaEmpty ()) (ssaEmpty ())))
with [] using eqStrs in

-- ssaFinalize (ssaChain (ssaSet n x) a) b = bind_ (nulet_ n x) (ssaFinalize a b)
utest failures (cross names (cross exprs (cross blocks falls)))
  (lam t. match t with (n, (x, (a, b))) in
    exprEq
      (fin (ssaChain (ssaSet n x) (a topExit)) b)
      (bind_ (nulet_ n x) (fin (a topExit) b)))
with [] using eqStrs in

-- (*) ssaSet n x = ssaSetPar {n -> x}
utest failures (cross names exprs)
  (lam t. match t with (n, x) in
    blockEq (lam. ssaSet n x) (lam. ssaSetPar (mapFromSeq nameCmp [(n, x)])))
with [] using eqStrs in

-- ssaFinalize (ssaMatch x p a b) c = match_ x p (ssaFinalize a c) (ssaFinalize b c)
utest failures (cross exprs (cross pats (cross smallBlocks (cross smallBlocks falls))))
  (lam t. match t with (x, (p, (a, (b, c)))) in
    exprEq
      (fin (ssaMatch x p (a topExit) (b topExit)) c)
      (match_ x p (fin (a topExit) c) (fin (b topExit) c)))
with [] using eqStrs in

-- ssaChain (ssaMatch x p a b) c = ssaMatch x p (ssaChain a c) (ssaChain b c)
utest failures (cross smallExprs (cross smallPats (cross smallBlocks (cross smallBlocks smallBlocks))))
  (lam t. match t with (x, (p, (a, (b, c)))) in
    blockEq
      (lam e. ssaChain (ssaMatch x p (a e) (b e)) (c e))
      (lam e. ssaMatch x p (ssaChain (a e) (c e)) (ssaChain (b e) (c e))))
with [] using eqStrs in

-- (*) ssaMatch x (npvar_ n) a b = ssaChain (ssaSet n x) a
utest failures (cross exprs (cross names (cross smallBlocks smallBlocks)))
  (lam t. match t with (x, (n, (a, b))) in
    blockEq
      (lam e. ssaMatch x (npvar_ n) (a e) (b e))
      (lam e. ssaChain (ssaSet n x) (a e)))
with [] using eqStrs in

-- (*) ssaMatch x pvarw_ a b = ssaChain (ssaRun x) a
utest failures (cross exprs (cross smallBlocks smallBlocks))
  (lam t. match t with (x, (a, b)) in
    blockEq
      (lam e. ssaMatch x pvarw_ (a e) (b e))
      (lam e. ssaChain (ssaRun x) (a e)))
with [] using eqStrs in

-- (*) ssaMatch x p a b = ssaChain (ssaSet n x) (ssaMatch (nvar_ n) p a b)  -- (where `n` is fresh)
utest failures (cross smallExprs (cross pats (cross smallBlocks smallBlocks)))
  (lam t. match t with (x, (p, (a, b))) in
    blockEq
      (lam e. ssaMatch x p (a e) (b e))
      (lam e. ssaChain (ssaSet w x) (ssaMatch (nvar_ w) p (a e) (b e))))
with [] using eqStrs in

-- ssaLoop a = ssaChain a (ssaLoop a)
utest failures loopBodies
  (lam a. blockEq (lam e. ssaLoop (a e)) (lam e. ssaChain (a e) (ssaLoop (a e))))
with [] using eqStrs in

-- (*) ssaChain (ssaLoop a) b = ssaLoop a
utest failures (cross loopBodies blocks)
  (lam t. match t with (a, b) in
    blockEq (lam e. ssaChain (ssaLoop (a e)) (b e)) (lam e. ssaLoop (a e)))
with [] using eqStrs in

-- ssaBlock (lam. a) = a
utest failures blocks
  (lam a. blockEq (lam e. ssaBlock (lam. a e)) a)
with [] using eqStrs in

-- ssaFinalize (ssaChain (ssaBlock f) c) x =
--   ssaFinalize (ssaChain (f (ssaChain c (ssaReturn x))) c) x
utest failures (cross blocks (cross blocks falls))
  (lam t. match t with (f, (c, x)) in
    exprEq
      (fin (ssaChain (ssaBlock f) (c topExit)) x)
      (fin (ssaChain (f (ssaChain (c topExit) (ssaReturn x))) (c topExit)) x))
with [] using eqStrs in

-- (*) ssaBlock (lam l. ssaChain l a) = ssaBlock (lam l. l) = ssaEmpty ()
utest failures blocks
  (lam a.
    and (blockEq (lam e. ssaBlock (lam l. ssaChain l (a e))) (lam. ssaEmpty ()))
        (blockEq (lam. ssaBlock (lam l. l)) (lam. ssaEmpty ())))
with [] using eqStrs in

-- ssaFinalize (ssaChain (ssaCallCC f) b) c = f (lam a. ssaFinalize (ssaChain a b) c)
utest failures (cross constructs (cross blocks falls))
  (lam t. match t with (f, (b, c)) in
    exprEq
      (fin (ssaChain (ssaCallCC f) (b topExit)) c)
      (f (lam a. fin (ssaChain a (b topExit)) c)))
with [] using eqStrs in

()
