include "ast.mc"
include "ast-builder.mc"

-- This file contains tests for the sfold and smap semantic functions
-- defined in "ast.mc". These will eventually be automatically generated,
-- and not require tests, but until then they need to be tested somewhere.
-- Normally this would be in the defining file, but the tests need to
-- construct ASTs, which is a lot easier if we have access to "ast-builder.mc".
-- "ast-builder.mc" includes "ast.mc" though, so we can't use it inside "ast.mc",
-- thus we create this file instead.

mexpr
use MExprAst in

let tmVarX = (var_ "x") in
let tmVarY = (var_ "y") in
let tmVarZ = (var_ "z") in
let tmVarU = (var_ "u") in
let tmVarW = (var_ "w") in
let map2varX = lam x. tmVarX in
let fold2seq = lam a. lam e. cons e a in

utest smap_Expr_Expr map2varX tmVarY with tmVarY in
utest sfold_Expr_Expr fold2seq [] tmVarY with [] in

let tmApp = app_ tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmApp with app_ tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmApp with [tmVarZ, tmVarY] in


let tmLam = ulam_ "x" tmApp in

utest smap_Expr_Expr map2varX tmLam with ulam_ "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLam with [tmApp] in


let tmLet = bind_ (let_ "y" tmLam) tmVarY in

utest smap_Expr_Expr map2varX tmLet with bind_ (let_ "y" tmVarX) tmVarX in
utest sfold_Expr_Expr fold2seq [] tmLet with [tmVarY, tmLam] in


let tmRecLets = bind_ (reclets_ [("x", tmApp), ("u", tmVarW)]) tmVarU in

utest smap_Expr_Expr map2varX tmRecLets
with
bind_ (reclets_ [("x", tmVarX), ("u", tmVarX)])
  tmVarX
in
utest sfold_Expr_Expr fold2seq [] tmRecLets with [tmVarU, tmVarW, tmApp] in


let tmConst1 = int_ 1 in
let tmConst2 = int_ 2 in
let tmConst3 = int_ 3 in
let tmApp11 = app_ tmConst1 tmConst2 in

utest smap_Expr_Expr (lam x. 0) tmConst1 with tmConst1 in
utest sfold_Expr_Expr fold2seq [] tmConst1 with [] in


let ite1 = if_ true_ true_ false_ in
let ite2 = if_ false_ false_ true_ in
let ite3 = if_ false_ (int_ 1) (int_ 4) in
let negateBool = lam tm. match tm with TmConst c then
                           match c.val with CBool v then
                             match v.val with true then false_ else true_
                           else tm
                         else tm
in
let countConsts = lam tm. match tm with TmConst _ then 1 else 0 in

utest smap_Expr_Expr negateBool ite1 with ite2 in
utest sfold_Expr_Expr addi 0 (smap_Expr_Expr countConsts ite3) with 3 in

let tmSeq = seq_ [tmApp11, tmConst2, tmConst3] in

utest smap_Expr_Expr map2varX tmSeq with seq_ [tmVarX, tmVarX, tmVarX] in
utest sfold_Expr_Expr fold2seq [] tmSeq with [tmConst3, tmConst2, tmApp11] in

let mkTmRecordXY = lam x. lam y. record_ [("x", x), ("y", y)] in
let tmRecordI = mkTmRecordXY tmApp11 tmConst3 in

utest smap_Expr_Expr map2varX tmRecordI
with record_ [("x", tmVarX), ("y", tmVarX)] in

utest sfold_Expr_Expr fold2seq [] tmRecordI with [tmConst3, tmApp11] in

let tmRecordUpdate = recordupdate_ tmRecordI "x" tmVarY in

utest smap_Expr_Expr map2varX tmRecordUpdate with recordupdate_ tmVarX "x" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmRecordUpdate with [tmVarY, tmRecordI] in


let tmCon = bind_ (ucondef_ "y") tmApp in

utest smap_Expr_Expr map2varX tmCon with bind_ (ucondef_ "y") tmVarX in
utest sfold_Expr_Expr fold2seq [] tmCon with [tmApp] in


let tmConApp = conapp_ "y" tmApp in

utest smap_Expr_Expr map2varX tmConApp with conapp_ "y" tmVarX in
utest sfold_Expr_Expr fold2seq [] tmConApp with [tmApp] in


let tmMatch = match_ tmApp punit_ tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmMatch
with match_ tmVarX punit_ tmVarX tmVarX in

utest sfold_Expr_Expr fold2seq [] tmMatch with [tmVarZ, tmVarY, tmApp] in

let tmUtest = utest_ tmApp tmVarY tmVarZ in

utest smap_Expr_Expr map2varX tmUtest with utest_ tmVarX tmVarX tmVarX in
utest sfold_Expr_Expr fold2seq [] tmUtest with [tmVarZ, tmVarY, tmApp] in

let pSeqTot = pseqtot_ [ptrue_, pfalse_] in

utest smap_Pat_Pat (lam x. pseqtot_ [x]) pSeqTot
with pseqtot_ [pseqtot_ [ptrue_], pseqtot_ [pfalse_]] in
utest sfold_Pat_Pat snoc [] pSeqTot with [ptrue_, pfalse_] in

let pSeqEdge = pseqedge_ [pint_ 1, pint_ 2] pwild_ [pint_ 3] in

utest smap_Pat_Pat (lam x. pseqtot_ [x]) pSeqEdge
with pseqedge_ [pseqtot_ [pint_ 1], pseqtot_ [pint_ 2]] pwild_ [pseqtot_ [pint_ 3]] in
utest sfold_Pat_Pat snoc [] pSeqEdge with [pint_ 1, pint_ 2, pint_ 3] in

let pAnd = pand_ ptrue_ pfalse_ in

utest smap_Pat_Pat pnot_ pAnd
with pand_ (pnot_ ptrue_) (pnot_ pfalse_) in
utest sfold_Pat_Pat snoc [] pAnd with [ptrue_, pfalse_] in

let pOr = por_ ptrue_ pfalse_ in

utest smap_Pat_Pat pnot_ pOr
with por_ (pnot_ ptrue_) (pnot_ pfalse_) in
utest sfold_Pat_Pat snoc [] pOr with [ptrue_, pfalse_] in

let pNot = pnot_ ptrue_ in

utest smap_Pat_Pat pnot_ pNot with pnot_ (pnot_ ptrue_) in
utest sfold_Pat_Pat snoc [] pNot with [ptrue_] in

-- recursive schemes tests
let tmConst1C = char_ (int2char 1) in
let tmConst2C = char_ (int2char 2) in
let tmConst3C = char_ (int2char 3) in
let tmApp11C = app_ tmConst1C tmConst2C in
let tmRecordC = mkTmRecordXY tmApp11C tmConst3C in

let cInt2cChar =
lam e. match e with TmConst t then
         match t.val with CInt i
           then TmConst {val = CChar {val = int2char i.val}}
         else e
       else e
in

recursive let bottomUp = lam f.
  compose f (smap_Expr_Expr (lam e. bottomUp f e))
in

recursive let topDown = lam f.
  compose (smap_Expr_Expr (lam e. topDown f e)) f
in

let countNodes = bottomUp (sfold_Expr_Expr addi 1) in

utest bottomUp identity tmVarX with tmVarX in
utest bottomUp cInt2cChar tmRecordI with tmRecordC in
utest countNodes tmVarX with 1 in
utest countNodes tmApp11C with 3 in
utest countNodes tmRecordC with 5 in

recursive let foldi = lam f. lam a. lam e.
  compose (lam a. sfold_Expr_Expr (foldi f) a e) (f a) e
in

utest foldi fold2seq [] tmVarX with [tmVarX] in
utest foldi fold2seq [] tmApp11C with [tmConst2C, tmConst1C, tmApp11C] in
utest foldi fold2seq [] tmRecordC
with [tmConst3C, tmConst2C, tmConst1C, tmApp11C, tmRecordC] in
()
