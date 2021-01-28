-- ANF transformation for MExpr programs, adapted from Figure 9 in Flanagan et
-- al. (1993).

include "name.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"
include "mexpr/eq.mc"

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
      ty = TyUnknown {},
      fi = NoInfo {}
    } in
    TmLet {ident = ident, ty = TyUnknown {},
           body = n, inexpr = k var}

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

lang FunANF = ANF + FunAst
  sem isValue =
  | TmLam _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmLam {ident = ident, ty = ty, body = body} ->
    k (TmLam {ident = ident, ty = ty, body = normalizeTerm body})

end

-- Records and record updates can be seen as sequences of applications.
lang RecordANF = ANF + RecordAst
  sem isValue =
  | TmRecord _ -> false
  | TmRecordUpdate _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmRecord t ->
    let acc = lam bs. k (TmRecord {t with bindings = bs}) in
    let f =
      (lam acc. lam k. lam e.
         (lam bs.
            normalizeName
              (lam v. acc (assocInsert {eq=eqString} k v bs))
              e))
    in
    (assocFold {eq=eqString} f acc t.bindings) assocEmpty

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
  | TmLet {ident = ident, ty = ty, body = m1, inexpr = m2} ->
    normalize
      (lam n1. (TmLet {ident = ident, ty = ty,
                       body = n1, inexpr = normalizeName k m2}))
      m1

end

lang TypeANF = ANF + TypeAst
  sem isValue =
  | TmType _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmType {ident = ident, ty = ty, inexpr = m1} ->
    TmType {ident = ident, ty = ty, inexpr = normalizeName k m1}

end

lang RecLetsANF = ANF + RecLetsAst
  sem isValue =
  | TmRecLets _ -> false

  sem normalize (k : Expr -> Expr) =
  -- We do not allow lifting things outside of reclets, since they might
  -- inductively depend on what is being defined.
  | TmRecLets {bindings = bindings, inexpr = inexpr} ->
    let bindings = map (lam b. {b with body = normalizeTerm b.body}) bindings in
    TmRecLets {bindings = bindings, inexpr = normalize k inexpr}
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
  | TmConDef {ident = ident, ty = ty, inexpr = inexpr} ->
    TmConDef {ident = ident, ty = ty, inexpr = normalize k inexpr}

  | TmConApp {ident = ident, body = body } ->
    normalizeName
      (lam b. k (TmConApp {ident = ident, body = b})) body

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
  | TmUtest {test = test, expected = expected, next = next} ->
    TmUtest {test = normalizeTerm test,
             expected = normalizeTerm expected,
             next = normalize k next}

end

lang SeqANF = ANF + SeqAst
  sem isValue =
  | TmSeq _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmSeq {tms = tms} ->
    let acc = lam ts. k (TmSeq {tms = ts}) in
    let f =
      (lam acc. lam e.
         (lam ts.
            normalizeName
              (lam v. acc (cons v ts))
              e))
    in
    (foldl f acc tms) []

end

lang NeverANF = ANF + NeverAst
  sem isValue =
  | TmNever _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmNever t -> k (TmNever t)

end

lang MExprANF =
  VarANF + AppANF + FunANF + RecordANF + LetANF + TypeANF + RecLetsANF +
  ConstANF + DataANF + MatchANF + UtestANF + SeqANF + NeverANF

-----------
-- TESTS --
-----------

lang TestLang =  MExprANF + MExprSym + MExprPrettyPrint + MExprEq

mexpr
use TestLang in

let _anf = compose normalizeTerm symbolize in

let basic =
  bind_ (ulet_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (ulet_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in

utest _anf basic
with
  bindall_ [
    ulet_ "f" (ulam_ "x" (var_ "x")),
    ulet_ "t" (addi_ (int_ 2) (int_ 2)),
    ulet_ "x1" (int_ 1),
    ulet_ "t1" (app_ (var_ "f") (var_ "x1")),
    ulet_ "t2" (addi_ (var_ "t") (var_ "t1")),
    var_ "t2"
  ]
using eqExpr in

-- TODO(dlunde,2020-10-21): Convert below to proper utests (as for basic above)

let ext =
  bindall_
    [ulet_ "f" (ulam_ "x" (var_ "x")),
     ulet_ "x" (int_ 3),
     (addi_ (addi_ (int_ 2) (var_ "x")))
       (bind_ (ulet_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))] in

let lambda =
  app_
    (ulam_ "x" (bind_ (ulet_ "y" (int_ 3)) (addi_ (var_ "x") (var_ "y"))))
    (int_ 4)
in

let apps =
  app_ (app_ (int_ 1) (app_ (int_ 2) (int_ 3))) (app_ (int_ 4) (app_ (int_ 5) (int_ 6)))
in

let record =
  record_ [
    ("a",(app_ (int_ 1) (app_ (int_ 2) (int_ 3)))),
    ("b", (int_ 4)),
    ("c", (app_ (int_ 5) (int_ 6)))
  ]
in

let rupdate =
  recordupdate_ record "b" (int_ 7) in

let factorial =
  ureclet_ "fact"
    (ulam_ "n"
      (if_ (eqi_ (var_ "n") (int_ 0))
        (int_ 1)
        (muli_ (var_ "n") (app_ (var_ "fact") (subi_ (var_ "n") (int_ 1))))))
in

let const = (int_ 1) in

let data = bind_ (ucondef_ "A") (conapp_ "A" (app_ (int_ 1) (int_ 2))) in

let seq =
  seq_ [
    (app_ (int_ 1) (app_ (int_ 2) (int_ 3))),
    (int_ 4),
    (app_ (int_ 5) (int_ 6))
  ]
in

let smatch = if_ (app_ (int_ 1) (int_ 2)) (int_ 3) (int_ 4) in

let simple = bind_ (ulet_ "x" (int_ 1)) (var_ "x") in

let simple2 = app_ (int_ 1) simple in

let inv1 = bind_ (ulet_ "x" (app_ (int_ 1) (int_ 2))) (var_ "x") in
utest _anf inv1 with inv1 using eqExpr in


let debug = false in

let debugPrint = lam t.
  let s = symbolize t in
  let n = normalizeTerm s in
  if debug then
    let _ = printLn "--- BEFORE ANF ---" in
    let _ = printLn (expr2str s) in
    let _ = print "\n" in
    let _ = printLn "--- AFTER ANF ---" in
    let _ = printLn (expr2str n) in
    let _ = print "\n" in
    ()
  else () in

let _ =
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
in
()
