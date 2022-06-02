-- ANF transformation for MExpr programs, adapted from Figure 9 in Flanagan et
-- al. (1993).

include "name.mc"
include "stringid.mc"

include "ast.mc"
include "ast-builder.mc"
include "pprint.mc"
include "symbolize.mc"
include "eq.mc"
include "info.mc"
include "error.mc"

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

-- Version analogous to AppANF, where each individual lambda is not name-bound.
lang LamANF = ANF + LamAst

  sem normalize (k : Expr -> Expr) =
  | TmLam _ & t -> k (normalizeLams t)

  sem normalizeLams =
  | TmLam t -> TmLam { t with body = normalizeLams t.body }
  | t -> normalizeTerm t

end

-- Version where each individual lambda is name-bound.
lang LamANFAll = ANF + LamAst

  sem normalize (k : Expr -> Expr) =
  | TmLam _ & t -> k (normalizeLams t)

  sem normalizeLams =
  | TmLam t -> TmLam { t with body = normalizeTerm t.body }

end

-- Records and record updates can be seen as sequences of applications.
lang RecordANF = ANF + RecordAst

  sem normalize (k : Expr -> Expr) =
  | TmRecord t ->
    let acc = lam bs. k (TmRecord {t with bindings = bs}) in
    let f =
      (lam acc. lam k. lam e.
         (lam bs.
            normalizeName
              (lam v. acc (mapInsert k v bs))
              e))
    in
    let tmp = mapFoldWithKey f acc t.bindings in
    tmp (mapEmpty (mapGetCmpFun t.bindings))

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

lang RecLetsANFBase = ANF + RecLetsAst + LamAst

  sem normalizeLams =
  -- Intentionally left blank

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
    TmUtest {{{{t with test = normalizeTerm t.test}
                 with expected = normalizeTerm t.expected}
                 with next = normalize k t.next}
                 with tusing = tusing}

end

lang SeqANF = ANF + SeqAst

  sem normalize (k : Expr -> Expr) =
  | TmSeq t ->
    let acc = lam ts. k (TmSeq {t with tms = ts}) in
    let f =
      (lam acc. lam e.
         (lam ts.
            normalizeName
              (lam v. acc (cons v ts))
              e))
    in
    (foldl f acc t.tms) []

end

lang NeverANF = ANF + NeverAst

  sem normalize (k : Expr -> Expr) =
  | TmNever t -> k (TmNever t)

end

lang ExtANF = ANF + ExtAst

  sem normalize (k : Expr -> Expr) =
  | TmExt ({inexpr = inexpr} & t) ->
    TmExt {t with inexpr = normalize k t.inexpr}

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

end

-- Full ANF transformation. Lifts everything
lang MExprANFAll =
  VarANF + AppANFAll + LamANFAll + RecordANF + LetANF + TypeANF + RecLetsANFAll +
  ConstANF + DataANF + MatchANF + UtestANF + SeqANF + NeverANF + ExtANF
end

-----------
-- TESTS --
-----------

lang TestBase = MExprSym + MExprPrettyPrint end

lang TestANF = MExprANF + MExprEq end

lang TestANFAll = MExprANFAll + MExprEq end

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

let basic =
  bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (ulet_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in
utest _test basic with
  bindall_ [
    ulet_ "f" (ulam_ "x" (var_ "x")),
    ulet_ "t" (addi_ (int_ 2) (int_ 2)),
    ulet_ "x1" (int_ 1),
    ulet_ "t1" (app_ (var_ "f") (var_ "x1")),
    ulet_ "t2" (addi_ (var_ "t") (var_ "t1")),
    var_ "t2"
  ]
using eqExpr in


let ext =
  bindall_
    [ulet_ "f" (ulam_ "x" (var_ "x")),
     ulet_ "x" (int_ 3),
     (addi_ (addi_ (int_ 2) (var_ "x")))
       (bind_ (ulet_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))] in
utest _test ext with
  bindall_ [
    ulet_ "f" (ulam_ "x" (var_ "x")),
    ulet_ "x1" (int_ 3),
    ulet_ "t" (addi_ (int_ 2) (var_ "x1")),
    ulet_ "x2" (int_ 1),
    ulet_ "t1" (app_ (var_ "f") (var_ "x2")),
    ulet_ "t2" (addi_ (var_ "t") (var_ "t1")),
    var_ "t2"
  ]
using eqExpr in

let lambda =
  app_
    (ulam_ "x" (bind_ (ulet_ "y" (int_ 3)) (addi_ (var_ "x") (var_ "y"))))
    (int_ 4)
in
utest _test lambda with
  bindall_ [
    ulet_ "t"
      (app_
        (ulam_ "x" (bindall_ [
          (ulet_ "y" (int_ 3)),
          (ulet_ "t1" (addi_ (var_ "x") (var_ "y"))),
          (var_ "t1")
        ]))
        (int_ 4)),
    var_ "t"
  ]
using eqExpr in

let apps =
  app_ (app_ (int_ 1) (app_ (int_ 2) (int_ 3))) (app_ (int_ 4) (app_ (int_ 5) (int_ 6)))
in
utest _test apps with
  bindall_ [
    ulet_ "x"  (app_ (int_ 2) (int_ 3)),
    ulet_ "x1" (app_ (int_ 5) (int_ 6)),
    ulet_ "x2" (app_ (int_ 4) (var_ "x1")),
    ulet_ "x3" (app_ (app_ (int_ 1) (var_ "x")) (var_ "x2")),
    var_ "x3"
  ]
using eqExpr in

let record =
  urecord_ [
    ("a",(app_ (int_ 1) (app_ (int_ 2) (int_ 3)))),
    ("b", (int_ 4)),
    ("c", (app_ (int_ 5) (int_ 6)))
  ]
in
let rupdate = recordupdate_ record "b" (int_ 7) in

let factorial =
  ureclet_ "fact"
    (ulam_ "n"
      (if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))
in
utest _test factorial with
  bindall_ [
    ureclet_ "fact"
      (ulam_ "n" (bindall_ [
        ulet_ "t" (eqi_ (var_ "n") (int_ 0)),
        ulet_ "t1" (if_ (var_ "t")
          (int_ 1)
          (bindall_ [
            ulet_ "t2" (subi_ (var_ "n") (int_ 1)),
            ulet_ "t3" (app_ (var_ "fact") (var_ "t2")),
            ulet_ "t4" (muli_ (var_ "n") (var_ "t3")),
            var_ "t4"
          ])
        ),
        var_ "t1"
      ])),
    ulet_ "t5" uunit_,
    var_ "t5"
  ]
using eqExpr in

let const = (int_ 1) in
utest _test const with
  (int_ 1)
using eqExpr in

let data = bind_ (ucondef_ "A") (conapp_ "A" (app_ (int_ 1) (int_ 2))) in
utest _test data with
  bindall_ [
    (ucondef_ "A"),
    ulet_ "t" (app_ (int_ 1) (int_ 2)),
    ulet_ "t1" (conapp_ "A" (var_ "t")),
    var_ "t1"
  ]
using eqExpr in

let seq =
  seq_ [
    (app_ (int_ 1) (app_ (int_ 2) (int_ 3))),
    (int_ 4),
    (app_ (int_ 5) (int_ 6))
  ]
in
utest _test seq with
  bindall_ [
    ulet_ "t" (app_ (int_ 5) (int_ 6)),
    ulet_ "t1" (app_ (int_ 2) (int_ 3)),
    ulet_ "t2" (app_ (int_ 1) (var_ "t1")),
    ulet_ "t3" (seq_ [var_ "t2", (int_ 4), var_ "t"]),
    var_ "t3"
  ]
using eqExpr in

let smatch = if_ (app_ (int_ 1) (int_ 2)) (int_ 3) (int_ 4) in
utest _test smatch with
  bindall_ [
    ulet_ "t" (app_ (int_ 1) (int_ 2)),
    ulet_ "t1" (if_ (var_ "t") (int_ 3) (int_ 4)),
    var_ "t1"
  ]
using eqExpr in

let simple = bind_ (ulet_ "x" (int_ 1)) (var_ "x") in
utest _test simple with simple using eqExpr in

let simple2 = app_ (int_ 1) simple in
utest _test simple2 with
  bindall_ [
    ulet_ "x" (int_ 1),
    ulet_ "t" (app_ (int_ 1) (var_ "x")),
    var_ "t"
  ]
using eqExpr in

let inv1 = bind_ (ulet_ "x" (app_ (int_ 1) (int_ 2))) (var_ "x") in
utest _test inv1 with inv1 using eqExpr in

let nested = ulam_ "x" (ulam_ "x" (ulam_ "x" (var_ "x"))) in
utest _test nested with
  (ulam_ "x" (ulam_ "x" (ulam_ "x" (var_ "x"))))
using eqExpr in

let nestedreclet =
  ureclet_ "f"
    (ulam_ "a"
      (ulam_ "b"
        (ulam_ "c" (int_ 1)))) in
utest _test nestedreclet with
  ureclet_ "f"
    (ulam_ "a"
      (ulam_ "b"
        (ulam_ "c" (int_ 1))))
using eqExpr in

let constant = int_ 1 in
utest _test constant with int_ 1
using eqExpr in

-- Tests for full ANF
use TestANFAll in

let _test = _testConstr normalizeTerm in

let appseq = addi_ (int_ 1) (int_ 2) in
utest _test appseq with
  bindall_ [
    ulet_ "t" (uconst_ (CAddi {})),
    ulet_ "t1" (int_ 1),
    ulet_ "t2" (app_ (var_ "t") (var_ "t1")),
    ulet_ "t3" (int_ 2),
    ulet_ "t4" (app_ (var_ "t2") (var_ "t3")),
    var_ "t4"
  ]
using eqExpr in

let lamseq = ulam_ "x" (ulam_ "y" (ulam_ "z" (int_ 1))) in
utest _test lamseq with
  let ulet_ = lam s. lam body. lam inexpr. bind_ (ulet_ s body) inexpr in
  ulet_ "t" (
    ulam_ "x" (
      ulet_ "t1" (
        ulam_ "y" (
          ulet_ "t2" (
            ulam_ "z" (
              ulet_ "t3" (int_ 1) (var_ "t3")
            )
          ) (var_ "t2")
        )
      ) (var_ "t1")
    )
  ) (var_ "t")
using eqExpr in

()
