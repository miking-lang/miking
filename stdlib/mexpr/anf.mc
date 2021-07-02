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

lang ANF = LetAst + VarAst + UnknownTypeAst
  sem isValue =
  -- Intentionally left blank

  sem normalizeTerm =
  | m -> normalizeName (lam x. x) m

  sem normalize (k : Expr -> Expr) =
  -- Intentionally left blank

  sem bind (k : Expr -> Expr) =
  | n ->
    let ident = nameSym "t" in
    let var = TmVar {
      ident = ident,
      ty = ty n,
      info = NoInfo {}
    } in
    let inexpr = k var in
    TmLet {ident = ident,
           tyBody = ty n,
           body = n,
           inexpr = inexpr,
           ty = ty inexpr,
           info = NoInfo{}}

  sem normalizeName (k : Expr -> Expr) =
  | m -> normalize (lam n. if (isValue n) then k n else bind k n) m

end

lang VarANF = ANF + VarAst
  sem isValue =
  | TmVar _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmVar t -> k (TmVar t)

end

-- This simplifies multiple-argument applications by not binding every
-- intermediate closure to a variable. I'm not yet sure if this makes static
-- analysis easier or more difficult.
lang AppANF = ANF + AppAst
  sem isValue =
  | TmApp _ -> false

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

lang LamANF = ANF + LamAst
  sem isValue =
  | TmLam _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmLam {ident = ident, ty = ty, tyIdent = tyIdent, body = body, info = info} ->
    k (TmLam {ident = ident, body = normalizeTerm body,
              ty = ty, tyIdent = tyIdent, info = info})

end

-- Records and record updates can be seen as sequences of applications.
lang RecordANF = ANF + RecordAst
  sem isValue =
  | TmRecord t ->
    if mapIsEmpty t.bindings then true
    else false
  | TmRecordUpdate _ -> false

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
  sem isValue =
  | TmLet _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmLet t ->
    normalize
      (lam n1. (TmLet {{t with body = n1}
                          with inexpr = normalizeName k t.inexpr}))
      t.body

end

lang TypeANF = ANF + TypeAst
  sem isValue =
  | TmType _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmType {ident = ident, tyIdent = tyIdent, inexpr = m1, ty = ty, info = info} ->
    TmType {ident = ident, tyIdent = tyIdent, ty = ty,
            inexpr = normalizeName k m1, info = info}

end

lang RecLetsANF = ANF + RecLetsAst
  sem isValue =
  | TmRecLets _ -> false

  sem normalize (k : Expr -> Expr) =
  -- We do not allow lifting things outside of reclets, since they might
  -- inductively depend on what is being defined.
  | TmRecLets t ->
    let bindings = map (lam b : RecLetBinding. {b with body = normalizeTerm b.body}) t.bindings in
    TmRecLets {{t with bindings = bindings}
                  with inexpr = normalize k t.inexpr}
end

lang ConstANF = ANF + ConstAst
  sem isValue =
  | TmConst _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmConst t -> k (TmConst t)

end

lang DataANF = ANF + DataAst
  sem isValue =
  | TmConDef _ -> false
  | TmConApp _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmConDef t ->
    TmConDef {t with inexpr = normalize k t.inexpr}

  | TmConApp t ->
    normalizeName
      (lam b. k (TmConApp {t with body = b})) t.body

end

lang MatchANF = ANF + MatchAst
  sem isValue =
  | TmMatch _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmMatch t ->
    normalizeName
      (lam t2. k (TmMatch {{{t with target = t2}
                               with thn = normalizeTerm t.thn}
                               with els = normalizeTerm t.els}))
      t.target

end

lang UtestANF = ANF + UtestAst
  sem isValue =
  | TmUtest _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmUtest t -> let tusing = optionMap normalizeTerm t.tusing in
    TmUtest {{{{t with test = normalizeTerm t.test}
                 with expected = normalizeTerm t.expected}
                 with next = normalize k t.next}
                 with tusing = tusing}

end

lang SeqANF = ANF + SeqAst
  sem isValue =
  | TmSeq _ -> false

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
  sem isValue =
  | TmNever _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmNever t -> k (TmNever t)

end

lang ExtANF = ANF + ExtAst
  sem isValue =
  | TmExt _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmExt ({inexpr = inexpr} & t) ->
    TmExt {t with inexpr = normalize k t.inexpr}
end

lang MExprANF =
  VarANF + AppANF + LamANF + RecordANF + LetANF + TypeANF + RecLetsANF +
  ConstANF + DataANF + MatchANF + UtestANF + SeqANF + NeverANF + ExtANF

-----------
-- TESTS --
-----------

lang TestLang =  MExprANF + MExprSym + MExprPrettyPrint + MExprEq

mexpr
use TestLang in

let eqExpr : Expr -> Expr -> Bool =
  lam l : Expr. lam r : Expr.
  eqExpr l r
in

let _anf = compose normalizeTerm symbolize in

let basic =
  bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (ulet_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in
utest _anf basic with
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
utest _anf ext with
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
utest _anf lambda with
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
utest _anf apps with
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
utest _anf factorial with
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
utest _anf const with
  (int_ 1)
using eqExpr in

let data = bind_ (ucondef_ "A") (conapp_ "A" (app_ (int_ 1) (int_ 2))) in
utest _anf data with
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
utest _anf seq with
  bindall_ [
    ulet_ "t" (app_ (int_ 5) (int_ 6)),
    ulet_ "t1" (app_ (int_ 2) (int_ 3)),
    ulet_ "t2" (app_ (int_ 1) (var_ "t1")),
    ulet_ "t3" (seq_ [var_ "t2", (int_ 4), var_ "t"]),
    var_ "t3"
  ]
using eqExpr in

let smatch = if_ (app_ (int_ 1) (int_ 2)) (int_ 3) (int_ 4) in
utest _anf smatch with
  bindall_ [
    ulet_ "t" (app_ (int_ 1) (int_ 2)),
    ulet_ "t1" (if_ (var_ "t") (int_ 3) (int_ 4)),
    var_ "t1"
  ]
using eqExpr in

let simple = bind_ (ulet_ "x" (int_ 1)) (var_ "x") in
utest _anf simple with simple using eqExpr in

let simple2 = app_ (int_ 1) simple in
utest _anf simple2 with
  bindall_ [
    ulet_ "x" (int_ 1),
    ulet_ "t" (app_ (int_ 1) (var_ "x")),
    var_ "t"
  ]
using eqExpr in

let inv1 = bind_ (ulet_ "x" (app_ (int_ 1) (int_ 2))) (var_ "x") in
utest _anf inv1 with inv1 using eqExpr in


let debug = false in

let debugPrint = lam t.
    let s = symbolize t in
    let n = normalizeTerm s in
    printLn "--- BEFORE ANF ---";
    printLn (expr2str s);
    print "\n";
    printLn "--- AFTER ANF ---";
    printLn (expr2str n);
    print "\n";
    ()
in

if debug then
  map debugPrint [
    basic,
    ext,
    lambda,
    apps,
    record,
    rupdate,
    factorial,
    const,
    data,
    seq,
    smatch,
    simple,
    simple2
  ]
else ()
