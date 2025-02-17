-- ANF transformation for MExpr programs, adapted from Figure 9 in Flanagan et
-- al. (1993).

include "name.mc"
include "stringid.mc"

include "ast.mc"
include "type.mc"
include "ast-builder.mc"
include "boot-parser.mc"
include "pprint.mc"
include "symbolize.mc"
include "eq.mc"
include "info.mc"
include "error.mc"
include "map.mc"

lang ANF = LetAst + VarAst + UnknownTypeAst

  -- By default, everything is lifted (except variables)
  sem liftANF =
  | TmVar _ -> false
  | t /- : Expr -/ -> true

  sem normalizeTerm =
  | m -> normalizeName (lam x. x) m

  sem normalize (k : Expr -> Expr) =
  -- Intentionally left blank

  sem bind (k : Expr -> Expr) =
  | n ->
    let ident = nameSym "t" in
    let var = TmVar {
      ident = ident,
      ty = tyTm n,
      info = infoTm n,
      frozen = false
    } in
    let inexpr = k var in
    TmLet {ident = ident,
           tyAnnot = TyUnknown {info = infoTm n},
           tyBody = tyTm n,
           body = n,
           inexpr = inexpr,
           ty = tyTm inexpr,
           info = infoTm n }

  sem normalizeName (k : Expr -> Expr) =
  | m -> normalize (lam n. if (liftANF n) then bind k n else k n) m

end

lang VarANF = ANF + VarAst

  sem normalize (k : Expr -> Expr) =
  | TmVar t -> k (TmVar t)

end

-- Version that simplifies multiple-argument applications by not binding every
-- intermediate closure to a variable.
lang AppANF = ANF + AppAst

  sem normalize (k : Expr -> Expr) =
  | TmApp t -> normalizeNames k (TmApp t)

  sem normalizeNames (k : Expr -> Expr) =
  | TmApp t ->
    normalizeNames
      (lam l. normalizeName (lam r. k (TmApp {{t with lhs = l}
                                                 with rhs = r})) t.rhs)
      t.lhs
  | t -> normalizeName k t

end

-- Version that lifts out each individual application
lang AppANFAll = ANF + AppAst

  sem normalize (k : Expr -> Expr) =
  | TmApp t ->
    normalizeName (lam l.
      normalizeName (lam r.
        k (TmApp {{t with lhs = l}
                     with rhs = r})
        )
      t.rhs)
    t.lhs

end

lang NormalizeLams
  sem normalizeLams =
end

-- Version analogous to AppANF, where each individual lambda is not name-bound.
lang LamANF = ANF + NormalizeLams + LamAst

  sem normalize (k : Expr -> Expr) =
  | TmLam _ & t -> k (normalizeLams t)

  sem normalizeLams =
  | TmLam t -> TmLam { t with body = normalizeLams t.body }
  | t -> normalizeTerm t

end

-- Version where each individual lambda is name-bound.
lang LamANFAll = ANF + NormalizeLams + LamAst

  sem normalize (k : Expr -> Expr) =
  | TmLam _ & t -> k (normalizeLams t)

  sem normalizeLams =
  | TmLam t -> TmLam { t with body = normalizeTerm t.body }

end

-- Records and record updates can be seen as sequences of applications.
lang RecordANF = ANF + RecordAst

  sem normalize (k : Expr -> Expr) =
  | TmRecord t ->
    mapMapK
      (lam e. lam k. normalizeName k e)
      t.bindings
      (lam bs. k (TmRecord {t with bindings = bs}))

  | TmRecordUpdate t ->
    normalizeName
      (lam vrec.
        normalizeName
          (lam vvalue.
            k (TmRecordUpdate {{t with rec = vrec}
                                  with value = vvalue}))
        t.value)
      t.rec

end

lang LetANF = ANF + LetAst

  sem normalize (k : Expr -> Expr) =
  | TmLet t ->
    normalize
      (lam n1. (TmLet {{t with body = n1}
                          with inexpr = normalizeName k t.inexpr}))
      t.body

end

lang TypeANF = ANF + TypeAst

  sem normalize (k : Expr -> Expr) =
  | TmType t ->
    TmType {t with inexpr = normalizeName k t.inexpr}
end

lang RecLetsANFBase = ANF + NormalizeLams + RecLetsAst + LamAst

  sem normalize (k : Expr -> Expr) =
  -- We do not allow lifting things outside of reclets, since they might
  -- inductively depend on what is being defined.
  | TmRecLets t ->
    let bindings = map (
      lam b: RecLetBinding. { b with body =
        match b.body with TmLam _ & t then normalizeLams t
        else errorSingle [infoTm b.body]
          "Error: Not a TmLam in TmRecLet binding in ANF transformation"
      }
    )
    t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = normalize k t.inexpr}

end

-- Analogous to LamANF and LamANFAll
lang RecLetsANF = RecLetsANFBase + LamANF end
lang RecLetsANFAll = RecLetsANFBase + LamANFAll end

lang ConstANF = ANF + ConstAst

  sem normalize (k : Expr -> Expr) =
  | TmConst t -> k (TmConst t)

end

lang DataANF = ANF + DataAst

  sem normalize (k : Expr -> Expr) =
  | TmConDef t ->
    TmConDef {t with inexpr = normalize k t.inexpr}

  | TmConApp t ->
    normalizeName
      (lam b. k (TmConApp {t with body = b})) t.body

end

lang MatchANF = ANF + MatchAst

  sem normalize (k : Expr -> Expr) =
  | TmMatch t ->
    normalizeName
      (lam t2. k (TmMatch {{{t with target = t2}
                               with thn = normalizeTerm t.thn}
                               with els = normalizeTerm t.els}))
      t.target

end

lang UtestANF = ANF + UtestAst

  sem normalize (k : Expr -> Expr) =
  | TmUtest t -> let tusing = optionMap normalizeTerm t.tusing in
    normalizeName
      (lam test.
         normalizeName
           (lam expected.
             let inner = lam x.
               match x with (tusing, tonfail) in
               TmUtest {
                 t with test = test,
                 expected = expected,
                 next = normalize k t.next,
                 tusing = tusing,
                 tonfail = tonfail
               }
              in
             switch (t.tusing, t.tonfail)
             case (Some tusing, Some tonfail) then
               normalizeName
                 (lam tusing.
                   normalizeName
                     (lam tonfail. inner (Some tusing, Some tonfail))
                     tonfail)
                 tusing
             case (Some tusing, None ()) then
               normalizeName (lam tusing. inner (Some tusing, None ())) tusing
             case (None (), Some tonfail) then
               normalizeName (lam tonfail. inner (None (), Some tonfail)) tonfail
             case (None (), None ()) then inner (None (), None())
             end)
           t.expected)
      t.test

end

lang SeqANF = ANF + SeqAst

  sem normalize (k : Expr -> Expr) =
  | TmSeq t ->
    mapK (lam e. lam k. normalizeName k e) t.tms (lam ts. k (TmSeq {t with tms = ts}))

end

lang NeverANF = ANF + NeverAst

  sem normalize (k : Expr -> Expr) =
  | TmNever t -> k (TmNever t)

end

lang ExtANF = ANF + ExtAst + FunTypeAst + UnknownTypeAst + LamAst + AppAst

  sem normalize (k : Expr -> Expr) =
  | TmExt ({inexpr = inexpr} & t) ->
    -- NOTE(dlunde,2022-06-14): Externals must always be fully applied
    -- (otherwise the parser throws an error). To make this compatible with
    -- ANF, we eta expand definitions of externals. In this way, the only
    -- application of the external is in the body of the eta expansion (where
    -- it is always fully applied).
    --
    let arity = arityFunType t.tyIdent in
    let i = withInfo t.info in

    -- Introduce variable names for each external parameter
    recursive let vars = lam acc. lam arity.
      match acc with (acc, tyIdent) in
      if lti arity 1 then acc
      else
        let arg = nameNoSym (concat "a" (int2string arity)) in
        match
          match tyIdent with TyArrow {from = from, to = to} then
            (from, to)
          else (TyUnknown {info = t.info}, tyIdent)
        with (argTy, innerTy) in
        vars (snoc acc (arg, argTy), innerTy) (subi arity 1)
    in
    let varNameTypes : [(Name, Type)] = vars ([], t.tyIdent) arity in

    -- Variable for the external itself
    let extId = TmVar {
      ident = t.ident, ty = t.tyIdent,
      info = t.info, frozen = false}
    in

    -- The body of the eta expansion
    match
      foldl
        (lam acc. lam v.
          match acc with (acc, tyIdent) in
          match v with (id, ty) in
          let appTy =
            match tyIdent with TyArrow {to = to} then
              to
            else TyUnknown {info = t.info} in
          let app = TmApp {
            lhs = acc,
            rhs = TmVar {ident = id, ty = ty, info = t.info, frozen = false},
            ty = appTy,
            info = t.info} in
          (app, appTy))
        (extId, t.tyIdent)
        varNameTypes
    with (inner, _) in

    let etaExpansion =
      foldr
        (lam v. lam acc.
          match v with (id, ty) in
          TmLam {
            ident = id, tyAnnot = TyUnknown {info = t.info}, tyParam = ty,
            body = acc, ty = TyArrow {from = ty, to = tyTm acc, info = t.info},
            info = t.info})
        inner varNameTypes in
    TmExt { t with
      inexpr = TmLet {
        ident = t.ident, tyAnnot = TyUnknown {info = t.info},
        tyBody = t.tyIdent, body = etaExpansion, inexpr = normalize k t.inexpr,
        ty = tyTm t.inexpr, info = t.info} }

end

-- The default ANF transformation for MExpr. Only lifts non-values, and does
-- not lift individual terms in sequences of lambdas or applications.
lang MExprANF =
  VarANF + AppANF + LamANF + RecordANF + LetANF + TypeANF + RecLetsANF +
  ConstANF + DataANF + MatchANF + UtestANF + SeqANF + NeverANF + ExtANF

  sem liftANF =
  | TmLam _ -> false
  | TmConst _ -> false
  | TmNever _ -> false
  | TmRecord r ->
    if mapIsEmpty r.bindings then false
    else true

end

-- Full ANF transformation. Lifts everything.
lang MExprANFAll =
  VarANF + AppANFAll + LamANFAll + RecordANF + LetANF + TypeANF + RecLetsANFAll +
  ConstANF + DataANF + MatchANF + UtestANF + SeqANF + NeverANF + ExtANF
end

-----------
-- TESTS --
-----------

lang TestBase = MExprSym + MExprPrettyPrint end

lang TestANF = MExprANF + MExprEq + BootParser end

lang TestANFAll = MExprANFAll + MExprEq + BootParser end

mexpr

use TestBase in

let debug = false in
let _testConstr = lam normalizeTerm. lam expr.
  (if debug then
    printLn "--- BEFORE ANF ---";
    printLn (expr2str expr);
    print "\n"
  else ());
  let expr = symbolize expr in
  let expr = normalizeTerm expr in
  (if debug then
    printLn "--- AFTER ANF ---";
    printLn (expr2str expr);
    print "\n"
  else ());
  expr
in

use TestANF in

let _test = _testConstr normalizeTerm in
let _parse = parseMExprStringKeywordsExn [] in

let basic = _parse "
  let f = (lam x. x) in
  addi (addi 2 2) (let x = 1 in f x)
" in
utest _test basic with _parse "
  let f = (lam x. x) in
  let t = addi 2 2 in
  let x1 = 1 in
  let t1 = f x1 in
  let t2 = addi t t1 in
  t2
" using eqExpr in


let ext = _parse "
  let f = (lam x. x) in
  let x = 3 in
  addi (addi 2 x) (let x = 1 in f x)
" in
utest _test ext with _parse "
  let f = (lam x. x) in
  let x1 = 3 in
  let t = addi 2 x1 in
  let x2 = 1 in
  let t1 = f x2 in
  let t2 = addi t t1 in
  t2
" using eqExpr in

let lambda = _parse "
  (lam x. let y = 3 in addi x y) 4
" in
utest _test lambda with _parse "
  let t = (lam x. let y = 3 in let t1 = addi x y in t1) 4 in
  t
" using eqExpr in

let apps = _parse "
  (1 (2 3)) (4 (5 6))
" in
utest _test apps with _parse "
  let x = 2 3 in
  let x1 = 5 6 in
  let x2 = 4 x1 in
  let x3 = 1 x x2 in
  x3
" using eqExpr in

let record = _parse "
  {a = 1 (2 3), b = 4, c = 5 6}
" in
-- printLn (mexprToString (_test record));
utest _test record with _parse "
  let t = 5 6 in
  let t1 = 2 3 in
  let t2 = 1 t1 in
  let t3 = { a = t2, b = 4, c = t } in
  t3
" using eqExpr in

let rupdate = _parse "
  {{a = 1 (2 3), b = 4, c = 5 6} with b = 7}
" in
utest _test rupdate with _parse "
  let t = 5 6 in
  let t1 = 2 3 in
  let t2 = 1 t1 in
  let t3 = { a = t2, b = 4, c = t } in
  let t4 = { t3 with b = 7 } in
  t4
" using eqExpr in

let factorial = _parse "
  recursive let fact = lam n. if eqi n 0 then 1 else muli n (fact (subi n 1)) in
  ()
" in
-- printLn (mexprToString (_test factorial));
utest _test factorial with _parse "
  recursive let fact = lam n.
    let t = eqi n 0 in
    let t1 = if t then 1 else
      let t2 = subi n 1 in
      let t3 = fact t2 in
      let t4 = muli n t3 in
      t4
    in
    t1
  in
  ()
" using eqExpr in

let const = _parse "1" in
utest _test const with const using eqExpr in

let data = _parse "
  con A: Unknown in A (1 2)
" in
utest _test data with _parse "
  con A: Unknown in
  let t = 1 2 in
  let t1 = A t in
  t1
" using eqExpr in

let seq = _parse " [1 (2 3), 4, 5 6] " in
utest _test seq with _parse "
  let t1 = 2 3 in
  let t2 = 1 t1 in
  let t3 = 5 6 in
  let t4 = [t2, 4, t3] in
  t4
" using eqExpr in

let smatch = _parse "
  if 1 2 then 3 else 4
" in
utest _test smatch with _parse "
  let t = 1 2 in
  let t1 = if t then 3 else 4 in
  t1
" using eqExpr in

let simple = _parse "let x = 1 in x" in
utest _test simple with simple using eqExpr in

let simple2 = _parse "1 (let x = 1 in x)" in
utest _test simple2 with _parse "
  let x = 1 in
  let t = 1 x in
  t
" using eqExpr in

let inv1 = _parse "let x = 1 2 in x" in
utest _test inv1 with inv1 using eqExpr in

let nested = _parse "lam x. lam x. lam x. x" in
utest _test nested with nested using eqExpr in

let nestedreclet = _parse "
  recursive let f = lam a. lam b. lam c. 1 in
  ()
" in
utest _test nestedreclet with _parse "
  recursive let f = lam a. lam b. lam c. 1 in
  ()
" using eqExpr in

-- Tests for full ANF
use TestANFAll in

let _test = _testConstr normalizeTerm in

let appseq = _parse "addi 1 2" in
utest _test appseq with _parse "
  let t = addi in
  let t1 = 1 in
  let t2 = t t1 in
  let t3 = 2 in
  let t4 = t2 t3 in
  t4
" using eqExpr in

let lamseq = _parse "lam x. lam y. lam z. 1" in
-- printLn (mexprToString (_test lamseq));
utest _test lamseq with _parse "
  let t = lam x.
    let t1 = lam y.
      let t2 = lam z.
        let t3 = 1 in
        t3
      in
      t2
    in
    t1
  in
  t
" using eqExpr in

-- Externals
let ext = _parse "
  external e: Int -> Float -> Int in
  e 1 2.
" in
-- printLn (mexprToString (_test ext));
utest _test ext with _parse "
external e : Int -> Float -> Int in
let e: Int -> Float -> Int = lam a1.  lam a2.  e a1 a2 in
let t = 1 in
let t1 = e t in
let t2 = 2. in
let t3 = t1 t2 in
t3
" using eqExpr in

()
