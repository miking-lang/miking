-- CPS tranformation for MExpr terms in ANF (produced by MExprANFAll in anf.mc).

include "ast.mc"
include "type.mc"
include "ast-builder.mc"
include "boot-parser.mc"
include "eq.mc"
include "anf.mc"
include "const-arity.mc"

lang CPS = LamAst + VarAst + LetAst

  sem cpsIdentity : Expr -> Expr
  sem cpsIdentity =
  | e ->
    let i = withInfo (infoTm e) in
    cpsCont (i (ulam_ "x" (var_ "x"))) e

  sem cpsCont : Expr -> Expr -> Expr
  sem cpsCont k =
  | e ->
    let e = exprCps k e in
    mapPre_Expr_Expr exprTyCps e

  sem exprCps : Expr -> Expr -> Expr

  sem exprTyCps : Expr -> Expr
  sem exprTyCps =
  | e -> e -- Default is identity function (do nothing)

  sem tyCps : Type -> Type
  sem tyCps =
  | t -> smap_Type_Type tyCps t

  sem tailCall =
  | TmLet { ident = ident, inexpr = inexpr } ->
    match inexpr with TmVar { ident = varIdent } then nameEq ident varIdent
    else false

end

-----------
-- TERMS --
-----------

lang VarCPS = CPS + VarAst + AppAst
  sem exprCps k =
  | TmVar _ & t-> withInfo (infoTm t) (app_ k t)
  | TmLet ({ body = TmVar _ } & b) ->
    TmLet { b with inexpr = exprCps k b.inexpr }
end

lang AppCPS = CPS + AppAst
  sem exprCps k =
  | TmLet { ident = ident, body = TmApp app, inexpr = inexpr } & t ->
    let i = withInfo (infoTm t) in
    if tailCall t then
      -- Optimize tail call
      i (appf2_ app.lhs k app.rhs)
    else
      let inexpr = exprCps k inexpr in
      let kName = nameSym "k" in
      let k = i (nulam_ ident inexpr) in
      bindall_ [
        i (nulet_ kName k),
        i (appf2_ app.lhs (i (nvar_ kName)) app.rhs)
      ]
end

lang LamCPS = CPS + LamAst
  sem exprCps k =
  | TmLet ({ ident = ident, body = TmLam t, inexpr = inexpr } & r) ->
    let kName = nameSym "k" in
    let i = withInfo t.info in
    let body =
      i (nulam_ kName (TmLam {t with body = exprCps (i (nvar_ kName)) t.body}))
    in
    TmLet { r with body = body, inexpr = exprCps k inexpr }

  sem exprTyCps =
  | TmLam _ & e -> smap_Expr_Type tyCps e
end

lang LetCPS = CPS + LetAst
  sem exprTyCps =
  | TmLet _ & e -> smap_Expr_Type tyCps e
end

lang RecLetsCPS = CPS + RecLetsAst + LamAst
  sem exprCps k =
  | TmRecLets t ->
    let bindings = map (lam b: RecLetBinding. { b with body =
        match b.body with TmLam t then
          let kName = nameSym "k" in
          let i = withInfo t.info in
          i (nulam_ kName
               (TmLam {t with body = exprCps (i (nvar_ kName)) t.body}))
        else errorSingle [infoTm b.body]
          "Error: Not a TmLam in TmRecLet binding in CPS transformation"
      }) t.bindings
    in TmRecLets { t with bindings = bindings, inexpr = exprCps k t.inexpr }

  sem exprTyCps =
  | TmRecLets _ & e -> smap_Expr_Type tyCps e
end

-- Wraps a direct-style function with given arity as a CPS function
let wrapDirect = use MExprAst in
  lam arity: Int. lam e: Expr.
    let i = withInfo (infoTm e) in
    recursive let vars = lam acc. lam arity.
      if lti arity 1 then acc
      else
        let arg = nameNoSym (concat "a" (int2string arity)) in
        let cont = nameNoSym (concat "k" (int2string arity)) in
        vars (cons (arg, cont) acc) (subi arity 1)
    in
    let varNames = vars [] arity in
    let inner = foldl (lam acc. lam v.
        i (app_ acc (nvar_ v.0))) e varNames in
    foldr (lam v. lam acc.
        i (nulam_ v.1 (i (nulam_ v.0 (app_ (i (nvar_ v.1)) acc))))
      ) inner varNames

lang ConstCPS = CPS + ConstAst + MExprArity
  sem exprCps k =
  | TmLet ({ body = TmConst { val = c } & body} & t) ->
    -- Constants are not in CPS, so we must wrap them all in CPS lambdas
    let body = wrapDirect (constArity c) body in
    TmLet { t with body = body, inexpr = exprCps k t.inexpr }
end

-- Thanks to ANF, we don't need to do anything at all when constructing data
-- (TmRecord, TmSeq, TmConApp, etc.)
lang SeqCPS = CPS + SeqAst
  sem exprCps k =
  | TmLet ({ body = TmSeq _ } & t) ->
    TmLet { t with inexpr = exprCps k t.inexpr }
end

lang RecordCPS = CPS + RecordAst
  sem exprCps k =
  | TmLet ({ body = TmRecord _ } & t) ->
    TmLet { t with inexpr = exprCps k t.inexpr }
end

lang TypeCPS = CPS + TypeAst
  sem exprCps k =
  | TmType t -> TmType { t with inexpr = exprCps k t.inexpr }

  sem exprTyCps =
  | TmType _ & e -> smap_Expr_Type tyCps e
end

lang DataCPS = CPS + DataAst
  sem exprCps k =
  | TmLet ({ body = TmConApp _ } & t) ->
    TmLet { t with inexpr = exprCps k t.inexpr }
  | TmConDef t ->
    TmConDef { t with inexpr = exprCps k t.inexpr }
end

lang MatchCPS = CPS + MatchAst
  sem exprCps k =
  | TmLet { ident = ident, body = TmMatch m, inexpr = inexpr } & t ->
    if tailCall t then
      -- Optimize tail call
      TmMatch { m with thn = exprCps k m.thn, els = exprCps k m.els }
    else
      let inexpr = exprCps k inexpr in
      let kName = nameSym "k" in
      let i = withInfo (infoTm t) in
      let k = i (nulam_ ident inexpr) in
      bindall_ [
        i (nulet_ kName k),
        TmMatch { m with
          thn = exprCps (i (nvar_ kName)) m.thn,
          els = exprCps (i (nvar_ kName)) m.els
        }
      ]
end

-- Not much needs to be done here thanks to ANF
lang UtestCPS = CPS + UtestAst
  sem exprCps k =
  | TmUtest t -> TmUtest { t with next = exprCps k t.next }

end

lang NeverCPS = CPS + NeverAst
  sem exprCps k =
  | TmLet ({ body = TmNever _ } & t) ->
    TmLet { t with inexpr = exprCps k t.inexpr }
end

lang ExtCPS = CPS + ExtAst
  sem exprCps k =
  | TmExt t ->
    let arity = arityFunType t.tyIdent in
    let i = withInfo t.info in
    TmExt { t with
      inexpr = bindall_
        [ i (nulet_ t.ident (wrapDirect arity (i (nvar_ t.ident)))),
          exprCps k t.inexpr ]
    }
end

-----------
-- TYPES --
-----------

lang FunTypeCPS = CPS + FunTypeAst
  sem tyCps =
  -- Function type a -> b becomes (b -> res) -> a -> res
  | TyArrow ({ from = from, to = to } & b) ->
    let i = tyWithInfo b.info in
    let from = tyCps from in
    let to = tyCps to in
    let resTyName = nameSym "r" in
    let cont = i (tyarrow_ to (i (ntyvar_ resTyName))) in
    i (ntyall_ resTyName
        (i (tyarrow_ cont
              (TyArrow { b with from = from, to = (i (ntyvar_ resTyName)) }))))
end

---------------
-- MEXPR CPS --
---------------

lang MExprCPS =
  CPS + VarCPS + AppCPS + LamCPS + LetCPS + RecLetsCPS + ConstCPS + SeqCPS +
  RecordCPS + TypeCPS + DataCPS + MatchCPS + UtestCPS + NeverCPS + ExtCPS +

  FunTypeCPS
end

-----------
-- TESTS --
-----------

lang Test = MExprCPS + BootParser + MExprEq + MExprANFAll + MExprPrettyPrint
end
mexpr
use Test in

let _parse =
  parseMExprString { defaultBootParserParseMExprStringArg with allowFree = true }
in
let _cps = lam e. cpsIdentity (normalizeTerm (_parse e)) in

-- Simple base cases
utest _cps "
  a
" with _parse "
  (lam x. x) a
"
using eqExpr in

utest _cps "
  a b
" with _parse "
  a (lam x. x) b
"
using eqExpr in

utest _cps "
  let x = 1 in
  let y = x in
  let z = y in
  z
" with _parse "
  let x = 1 in
  let y = x in
  let z = y in
  (lam x. x) z
"
using eqExpr in

-- Recursive lets
let recletsTest = _cps "
  recursive
    let f1 = lam a. lam b. b
    let f2 = lam b. b
  in
  let x = f1 1 2 in
  let y = f2 3 in
  and x y
" in
-- print (mexprToString recletsTest);
utest recletsTest with _parse "
  recursive
    let f1 = lam k. lam a. let t = lam k1. lam b. k1 b in k t
    let f2 = lam k2. lam b. k2 b
  in
  let t1 = 1 in
  let k3 = lam t2.
    let t3 = 2 in
    let k4 = lam x.
      let t4 = 3 in
      let k5 = lam y.
        let k6 = lam t5.
          (lam x. x) y
        in
        and k6 x
      in
      f2 k5 t4
    in
    t2 k4 t3
  in
  f1 k3 t1
"
using eqExpr in

-- Constants
utest _cps "
  addi 1 2
" with _parse "
  let t = lam k1. lam a1. k1 (lam k2. lam a2. k2 (addi a1 a2)) in
  let t1 = 1 in
  let k = lam t2.
    let t3 = 2 in
    t2 (lam x. x) t3
  in
  t k t1
"
using eqExpr in

-- Sequences
let seqtest = _cps "
  [a b, c, d, e]
" in
-- print (mexprToString seqtest);
utest seqtest with _parse "
  let k = lam t.
    let t1 = [ t, c, d, e ] in
    (lam x. x) t1
  in
  a k b
"
using eqExpr in

-- Records
let rectest = _cps "
  { k1 = a, k2 = b, k3 = c d }
" in
-- print (mexprToString rectest);
utest rectest with _parse "
  let k = lam t.
    let t1 = { k1 = a, k2 = b, k3 = t } in
    (lam x. x) t1
  in
  c k d
"
using eqExpr in

-- Types
-- NOTE(dlunde,2022-06-02): Not supported in eqExpr?

-- Data/constructors
let datatest = _cps "
  Constructor (a b)
" in
-- print (mexprToString rectest);
utest datatest with _parse "
  let k = lam t.
    let t1 = Constructor t in
    (lam x. x) t1
  in
  a k b
"
using eqExpr in

-- Match
let matchtest = _cps "
  let x1 =
    match a b with (p1 | 3 | 7) & p3 then
      c d
    else
      false
  in
  or x1 false
" in
-- print (mexprToString matchtest);
utest matchtest with _parse "
  let k = lam t.
    let k1 = lam x1.
      let k2 = lam t2.
        let t3 = false in
        t2 (lam x. x) t3
      in
      or k2 x1
    in
    match t with (p1 | (3 | 7)) & p3 then
      c k1 d
    else
      let t1 = false in
      k1 t1
  in
  a k b
"
using eqExpr in

-- Utest
let utesttest = _cps "
  utest a b with c using d e in
  let x = f g in
  y
" in
-- print (mexprToString utesttest);
utest utesttest with _parse "
  let k =
    lam t.
      let k1 =
        lam t1.
          utest t with c using t1 in
          let k2 = lam x. (lam x. x) y in
          f k2 g
      in
      d k1 e
  in
  a k b
"
using eqExpr in

-- Never
utest _cps "
  never
" with _parse "
  let t = never in
  (lam x. x) t
"
using eqExpr in

-- Externals
let externaltest = _cps "
  external f : Float -> Float in
  let x = f g in
  y
" in
-- print (mexprToString externaltest);
utest externaltest with _parse "
  external f : Float -> Float in
  let f1 = lam k1. lam a1. k1 (f a1) in
  let k = lam x. (lam x. x) y in
  f1 k g
"
using eqExpr in

-- Types (not supported in equality, check the string output from pprint)
let typestest = _cps "
  external e : Float -> Float in
  let f: Float -> Float = lam x: Float. e x in
  let g: (Float -> Float) -> Float = lam h: (Float -> Float). h 1.0 in
  recursive let h : all a. a -> a = lam y: a. y in
  g f
" in
-- print (mexprToString typestest);
utest mexprToString typestest with
"external e : (Float) -> (Float)
in
let e =
  lam k11.
    lam a1.
      k11
        (e
           a1)
in
let f: all r4. ((Float) -> (r4)) -> ((Float) -> (r4)) =
  lam k2.
    lam x: Float.
      e
        k2
        x
in
let g: all r1. ((Float) -> (r1)) -> ((all r2. ((Float) -> (r2)) -> ((Float) -> (r2))) -> (r1)) =
  lam k1.
    lam h: all r3. ((Float) -> (r3)) -> ((Float) -> (r3)).
      let t =
        1.
      in
      h
        k1
        t
in
recursive
  let h: all a. all r. ((a) -> (r)) -> ((a) -> (r)) =
    lam k.
      lam y: a.
        k
          y
in
g
  (lam x.
     x)
  f"
in

()
