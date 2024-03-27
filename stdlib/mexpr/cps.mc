-- CPS tranformation for MExpr terms in ANF (produced by MExprANFAll in anf.mc).
-- Includes both full and partial versions.
--
-- The partial version takes a list of names as arguments. These names signal
-- which ANF expressions (i.e., `let`s) should be CPS transformed. *** Note
-- that the transformation leaves no guarantees that the partial transformation
-- is correct ***.  Instead, users must make sure that the list of names (below
-- called "marked" names) given to the transfomation is sound. The rules are as
-- follows:
--
-- 1. If `a` is marked for a let expression
--    ```
--      let a = <expr> in
--    ```
--    you must ensure that the names of _all_ enclosing `match` expressions up
--    until the innermost `lambda` are marked. The `lambda` itself must also be
--    marked.
--
-- 2. For all applications
--    ```
--      let a = b c in
--    ```
--    you must ensure that if there is a function (lambda, constant,
--    external, ...) defined somewhere as, e.g.,
--    ```
--      let f = (lam x. ...) in
--    ```
--    with `f` marked and such that `lam x. ...` can occur at position `b`,
--    _all other functions_ that can occur at `b` must also be marked.
--    Furthermore, `a` must be marked. It is tricky to determine all functions
--    that can occur at `b`, and this is best handled with a separate
--    control-flow analysis (see `cfa.mc`).

include "ast.mc"
include "type.mc"
include "ast-builder.mc"
include "boot-parser.mc"
include "eq.mc"
include "anf.mc"
include "const-arity.mc"
include "const-types.mc"

type CPSEnv = {

  -- Predicate that determines which names to CPS transform
  transform: Name -> Bool,

  -- If the CPS transformation is partial or not (true if transform = lam. true)
  partial: Bool

}

let _cpsEnvDefault = {
  transform = lam. true,
  partial = false
}

lang CPS = LamAst + VarAst + LetAst

  sem cpsFullIdentity : Expr -> Expr
  sem cpsFullIdentity =
  | e ->
    let id = withInfo (infoTm e) (ulam_ "x" (var_ "x")) in
    cpsFullCont id e

  sem cpsFullCont : Expr -> Expr -> Expr
  sem cpsFullCont k =
  | e ->
    let env = _cpsEnvDefault in
    let e = exprCps env (Some k) e in
    mapPre_Expr_Expr (exprTyCps env) e

  sem cpsPartialIdentity : (Name -> Bool) -> Expr -> Expr
  sem cpsPartialIdentity transformFun =
  | e ->
    let id = withInfo (infoTm e) (ulam_ "x" (var_ "x")) in
    cpsPartialCont transformFun id e

  sem cpsPartialCont : (Name -> Bool) -> Expr -> Expr -> Expr
  sem cpsPartialCont transformFun k =
  | e ->
    let env = { _cpsEnvDefault with transform = transformFun, partial = true } in
    let e = exprCps env (Some k) e in
    mapPre_Expr_Expr (exprTyCps env) e

  sem exprCps : CPSEnv -> Option Expr -> Expr -> Expr

  sem exprTyCps : CPSEnv -> Expr -> Expr
  sem exprTyCps env =
  | e -> e -- Default is to do nothing

  sem tyCps : CPSEnv -> Type -> Type
  sem tyCps env =
  | t -> smap_Type_Type (tyCps env) t

  sem tailCall =
  | TmLet { ident = ident, inexpr = inexpr } ->
    match inexpr with TmVar { ident = varIdent } then nameEq ident varIdent
    else false

  sem transform : CPSEnv -> Name -> Bool
  sem transform env =
  | n -> env.transform n

end

-----------
-- TERMS --
-----------

lang VarCPS = CPS + VarAst + AppAst
  sem exprCps env k =
  | TmVar _ & t ->
    match k with Some k then withInfo (infoTm t) (app_ k t) else t
  | TmLet ({ body = TmVar _ } & b) ->
    TmLet { b with inexpr = exprCps env k b.inexpr }
end

lang AppCPS = CPS + AppAst
  sem exprCps env k =
  | TmLet ({ ident = ident, body = TmApp app, inexpr = inexpr } & b) & t ->
    if not (transform env ident) then
      TmLet { b with inexpr = exprCps env k inexpr }
    else
      let i = withInfo (infoTm t) in
      let opt =
        match k with Some k then
          if tailCall t then Some k
          else None ()
        else None () in
      match opt with Some k then
        -- Optimize tail call with available continuation
        i (appf2_ app.lhs k app.rhs)
      else
        let inexpr = exprCps env k inexpr in
        let kName = nameSym "k" in
        let k = i (nulam_ ident inexpr) in
        bindall_ [
          i (nulet_ kName k),
          i (appf2_ app.lhs (i (nvar_ kName)) app.rhs)
        ]
end

lang LamCPS = CPS + LamAst
  sem exprCps env k =
  | TmLet ({ ident = ident, body = TmLam t, inexpr = inexpr } & r) ->
    if not (or (transform env ident) (transform env t.ident)) then
      TmLet { r with
        body = TmLam { t with body = exprCps env (None ()) t.body },
        inexpr = exprCps env k inexpr
      }
    else
      let kName = nameSym "k" in
      let i = withInfo t.info in
      let body =
        i (nulam_ kName
             (TmLam {t with body = exprCps env (Some (i (nvar_ kName))) t.body}))
      in
      TmLet { r with body = body, inexpr = exprCps env k inexpr }

  sem exprTyCps env =
  | TmLam _ & e -> smap_Expr_Type (tyCps env) e
end

lang LetCPS = CPS + LetAst
  sem exprTyCps env =
  | TmLet _ & e -> smap_Expr_Type (tyCps env) e
end

lang RecLetsCPS = CPS + RecLetsAst + LamAst
  sem exprCps env k =
  | TmRecLets t ->
    let bindings = map (lam b: RecLetBinding. { b with body =
        match b.body with TmLam t then
          if not (or (transform env b.ident) (transform env t.ident)) then
            TmLam { t with body = exprCps env (None ()) t.body }
          else
            let kName = nameSym "k" in
            let i = withInfo t.info in
            i (nulam_ kName
                 (TmLam { t with body = exprCps env (Some (i (nvar_ kName))) t.body }))
        else errorSingle [infoTm b.body]
          "Error: Not a TmLam in TmRecLet binding in CPS transformation"
      }) t.bindings
    in TmRecLets { t with bindings = bindings, inexpr = exprCps env k t.inexpr }

  sem exprTyCps env =
  | TmRecLets _ & e -> smap_Expr_Type (tyCps env) e
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

lang ConstCPS = CPS + ConstAst + MExprArity + TyConst
  sem exprCps env k =
  | TmLet ({ ident = ident, body = TmConst { val = c } & body} & t) ->
    if not (transform env ident) then
      TmLet { t with inexpr = exprCps env k t.inexpr }
    else
      if isHigherOrderFunType (tyConst c) then
        -- TODO(dlunde,2022-09-19): Add support for higher-order constant
        -- functions. Not sure how though, as constant functions are opaque
        -- (i.e., we cannot force them to accept CPS functions as argument)
        errorSingle [infoTm body]
          "Higher-order constant functions not yet supported in CPS transformation"
      else
        -- Constants are not in CPS, so we must wrap them in CPS lambdas
        let body = wrapDirect (constArity c) body in
        TmLet { t with body = body, inexpr = exprCps env k t.inexpr }
end

-- Thanks to ANF, we don't need to do anything at all when constructing data
-- (TmRecord, TmSeq, TmConApp, etc.)
lang SeqCPS = CPS + SeqAst
  sem exprCps env k =
  | TmLet ({ body = TmSeq _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
end

lang RecordCPS = CPS + RecordAst
  sem exprCps env k =
  | TmLet ({ body = TmRecord _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmLet ({ body = TmRecordUpdate _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
end

lang TypeCPS = CPS + TypeAst
  sem exprCps env k =
  | TmType t -> TmType { t with inexpr = exprCps env k t.inexpr }

  sem exprTyCps env =
  | TmType _ & e -> smap_Expr_Type (tyCps env) e
end

lang DataCPS = CPS + DataAst + AllTypeAst + FunTypeAst
  sem exprCps env k =
  | TmLet ({ body = TmConApp _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
  | TmConDef t ->
    TmConDef { t with inexpr = exprCps env k t.inexpr }

  -- We do not transform the top-level arrow type of the condef (due to
  -- the nested smap_Type_Type), as data values are constructed as usual even
  -- in CPS.
  -- NOTE(dlunde,2022-07-13): We currently ignore TyAll wrapping the top-level
  -- arrow type.
  -- NOTE(dlunde,2022-07-13): Issues can arise here if the top-level arrow type
  -- of a condef is a type variable that was defined earlier with TmType. It is
  -- then CPS transformed.
  sem exprTyCps env =
  | TmConDef t & e ->
    recursive let rec = lam ty.
      match ty with TyAll b then TyAll { b with ty = rec b.ty }
      else match ty with TyArrow _ & t then smap_Type_Type (tyCps env) t
      else errorSingle [t.info]
        "Error in CPS: Problem with TmConDef in exprTyCps"
    in smap_Expr_Type rec e
end

lang MatchCPS = CPS + MatchAst
  sem exprCps env k =
  | TmLet ({ ident = ident, body = TmMatch m, inexpr = inexpr } & b) & t ->
    if not (transform env ident) then
      TmLet { b with
        body = TmMatch { m with
          thn = exprCps env (None ()) m.thn,
          els = exprCps env (None ()) m.els
        },
        inexpr = exprCps env k inexpr
      }
    else
      let opt = match k with Some k then tailCall t else false in
      if opt then
        -- Optimize tail call with available continuation
        TmMatch { m with thn = exprCps env k m.thn, els = exprCps env k m.els }
      else
        let inexpr = exprCps env k inexpr in
        let kName = nameSym "k" in
        let i = withInfo (infoTm t) in
        let k = i (nulam_ ident inexpr) in
        bindall_ [
          i (nulet_ kName k),
          TmMatch { m with
            thn = exprCps env (Some (i (nvar_ kName))) m.thn,
            els = exprCps env (Some (i (nvar_ kName))) m.els
          }
        ]
end

-- Not much needs to be done here thanks to ANF
lang UtestCPS = CPS + UtestAst
  sem exprCps env k =
  | TmUtest t -> TmUtest { t with next = exprCps env k t.next }

end

lang NeverCPS = CPS + NeverAst
  sem exprCps env k =
  | TmLet ({ body = TmNever _ } & t) ->
    TmLet { t with inexpr = exprCps env k t.inexpr }
end

lang ExtCPS = CPS + ExtAst
  sem exprCps env k =
  | TmExt t ->
    errorSingle [t.info]
      "Error in CPS: Should not happen due to ANF transformation"
  | TmExt ({ inexpr = TmLet ({ ident = ident, body = TmLam _, inexpr = inexpr } & tl) } & t) ->
    if not (transform env ident) then
      TmExt { t with inexpr = TmLet { tl with inexpr = exprCps env k inexpr } }
    else
      -- We know that ANF adds a let that eta expands the external just after its
      -- definition. Here, we simply replace this eta expansion with its CPS
      -- equivalent
      let arity = arityFunType t.tyIdent in
      let i = withInfo t.info in
      TmExt { t with
        inexpr = bindall_
          [ i (nulet_ t.ident (wrapDirect arity (i (nvar_ t.ident)))),
            exprCps env k inexpr ]
      }
end

-----------
-- TYPES --
-----------

lang FunTypeCPS = CPS + FunTypeAst
  sem tyCps env =
  -- Function type a -> b becomes (b -> res) -> a -> res
  | TyArrow ({ from = from, to = to } & b) ->
    let i = tyWithInfo b.info in
    if env.partial then
      -- NOTE(dlunde,2022-06-14): It is not obvious how to transform the types
      -- when the CPS transformation is partial. For now, we simply replace
      -- arrow types with unknown and rely on the type checker to infer the new
      -- correct CPS types.
      (i tyunknown_)
    else
      let from = tyCps env from in
      let to = tyCps env to in
      -- NOTE(dlunde,2022-06-08): We replace all continuation return types with
      -- the unknown type. No polymorphism should be needed, as all of these
      -- unknown types should ultimately be the same type: the return type of the
      -- program (I think). This can easily be inferred by the type checker.
      let cont = i (tyarrow_ to (i tyunknown_)) in
      (i (tyarrow_ cont
          (TyArrow { b with from = from, to = (i tyunknown_) })))
end

---------------
-- MEXPR CPS --
---------------

lang MExprCPS =
  CPS + VarCPS + AppCPS + LamCPS + LetCPS + RecLetsCPS + ConstCPS + SeqCPS +
  RecordCPS + TypeCPS + DataCPS + MatchCPS + UtestCPS + NeverCPS + ExtCPS +

  FunTypeCPS +

  MExprConstType
end

-----------
-- TESTS --
-----------

lang Test = MExprCPS + BootParser + MExprEq + MExprANFAll + MExprPrettyPrint
end
mexpr
use Test in

let _parse =
  parseMExprStringExn { defaultBootParserParseMExprStringArg with allowFree = true }
in

-------------------------
-- TESTS FOR FULL CPS  --
-------------------------

let _cps = lam e. cpsFullIdentity (normalizeTerm (_parse e)) in

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
  addi x y
" in
-- printLn (mexprToString recletsTest);
utest recletsTest with _parse "
  recursive
    let f1 = lam k. lam a. let t = lam k1. lam b. k1 b in k t
    let f2 = lam k2. lam b. k2 b
  in
  let t1 = 1 in
  let k3 =
    lam t2.
      let t3 = 2 in
      let k4 =
        lam x.
          let t4 = 3 in
          let k5 =
            lam y.
              let t5 = lam k11. lam a1. k11 (lam k21. lam a2. k21 (addi a1 a2)) in
              let k6 = lam t6.  t6 (lam x. x) y in
              t5 k6 x
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
  external f : Float -> Float -> Float in
  let x = f a b in
  x
" in
-- print (mexprToString externaltest);
utest externaltest with _parse "
  external f : Float -> Float -> Float in
  let f = lam k1. lam a1. k1 (lam k2. lam a2. k2 (f a1 a2)) in
  let k = lam t. t (lam x. x) b in
  f k a
"
using eqExpr in

-- Types (not supported in equality, check the string output from pprint)
let typestest = _cps "
  external e : Float -> Float in
  let f: Float -> Float = lam x: Float. e x in
  let g: (Float -> Float) -> Float = lam h: (Float -> Float). h 1.0 in
  recursive let h : all a. a -> a = lam y: a. y in
  type T in
  con C : (all x. x -> x) -> T in
  g f
" in
-- print (mexprToString typestest);
utest mexprToString typestest with
"external e : Float -> Float
in
let e = lam k11.
    lam a1.
      k11 (e a1) in
let f: (Float -> Unknown) -> Float -> Unknown = lam k2.
    lam x: Float.
      e k2 x
in
let g: (Float -> Unknown) -> ((Float -> Unknown) -> Float -> Unknown) -> Unknown =
  lam k1.
    lam h: (Float -> Unknown) -> Float -> Unknown.
      let t = 1. in
      h k1 t
in
recursive
  let h: all a. (a -> Unknown) -> a -> Unknown = lam k.
      lam y: a.
        k y
in
type T
in
con C: (all x. (x -> Unknown) -> x -> Unknown) -> T in
g (lam x.
     x) f"
in

----------------------------
-- TESTS FOR PARTIAL CPS  --
----------------------------

let _cps = lam names. lam e.
  let names = setOfSeq nameCmp (map nameNoSym names) in
  let transformFun = lam n. setMem n names in
  cpsPartialIdentity transformFun (normalizeTerm (_parse e))
in

-- Variables
utest _cps [] "a" with _parse "(lam x. x) a" using eqExpr in
utest _cps ["a"] "a" with _parse "(lam x. x) a" using eqExpr in

-- Applications
utest _cps [] "let t = a b in t"
with _parse "let t = a b in (lam x. x) t"
using eqExpr in

utest _cps ["t"] "let t = a b in t"
with _parse "a (lam x. x) b"
using eqExpr in

-- Recursive lets
let recletsTest = "
  recursive
    let f1 = lam a. let t = lam b. b in t
    let f2 = lam c. c
  in
  let x = f1 1 2 in
  let y = f2 3 in
  addi x y
" in
-- printLn (mexprToString (_cps [] recletsTest));
utest _cps [] recletsTest with _parse "
  recursive
    let f1 = lam a. let t = lam b. b in t
    let f2 = lam c. c
  in
  let t1 = 1 in
  let t2 = f1 t1 in
  let t3 = 2 in
  let x = t2 t3 in
  let t4 = 3 in
  let y = f2 t4 in
  let t5 = addi in
  let t6 = t5 x in
  let t7 = t6 y in
  (lam x. x) t7
" using eqExpr in
-- printLn (mexprToString (_cps ["b", "t", "x"] recletsTest));
utest _cps ["b", "t", "x"] recletsTest with _parse "
  recursive
    let f1 = lam a. let t = lam k. lam b. k b in t
    let f2 = lam c. c
  in
  let t1 = 1 in
  let t2 = f1 t1 in
  let t3 = 2 in
  let k1 =
    lam x.
      let t4 = 3 in
      let y = f2 t4 in
      let t5 = addi in
      let t6 = t5 x in
      let t7 = t6 y in
      (lam x. x) t7
  in
  t2 k1 t3
" using eqExpr in

let constexttest = "
  external e: Float -> Float -> Float in
  let c = addi in
  let f1 = (lam x1. let f2 = lam x2. x2 in f2) in
  res
" in
-- printLn (mexprToString (_cps [] constexttest));
utest _cps [] constexttest with _parse "
external e : Float -> Float -> Float in
let e = lam a1. lam a2. e a1 a2 in
let c = addi in
let f1 = lam x1. let f2 = lam x2. x2 in f2 in
(lam x. x) res
" using eqExpr in
-- printLn (mexprToString (_cps ["e","c","f1","f2"] constexttest));
utest _cps ["e","c","f1","f2"] constexttest with _parse "
  external e : Float -> Float -> Float in
  let e = lam k11. lam a1. k11 (lam k2. lam a2. k2 (e a1 a2)) in
  let c = lam k11. lam a1. k11 (lam k2. lam a2. k2 (addi a1 a2)) in
  let f1 = lam k. lam x1. let f2 = lam k1. lam x2. k1 x2 in k f2 in
  (lam x. x) res
" using eqExpr in

()

