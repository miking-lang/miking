-- ANF transformation for MExpr programs, adapted from Figure 9 in Flanagan et
-- al. (1993).

include "name.mc"

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

lang ANF = LetAst + VarAst
  sem isValue =
  -- Intentionally left blank

  sem normalizeTerm =
  | m -> normalize (lam x. x) m

  sem normalize (k : Expr -> Expr) =
  -- Intentionally left blank

  sem bind (k : Expr -> Expr) =
  | n ->
    let ident = nameSym "t" in
    (TmLet {ident = ident, body = n, inexpr = k (TmVar {ident = ident})})

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
  | TmApp t -> normalizeNames (lam app. bind k app) (TmApp t)

  sem normalizeNames (k : Expr -> Expr) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    normalizeNames
      (lam l. normalizeName (lam r. k (TmApp {lhs = l, rhs = r})) rhs)
      lhs
  | t -> normalizeName k t

end

lang FunANF = ANF + FunAst
  sem isValue =
  | TmLam _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmLam {ident = ident, tpe = tpe, body = body} ->
    k (TmLam {ident = ident, tpe = tpe, body = normalizeTerm body})

end

-- Records and record updates can be seen as sequences of applications.
lang RecordANF = ANF + RecordAst
  sem isValue =
  | TmRecord _ -> false
  | TmRecordUpdate _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmRecord {bindings = bindings} ->
    let acc = lam bs. bind k (TmRecord {bindings = bs}) in
    let f =
      (lam acc. lam k. lam e.
         (lam bs.
            normalizeName
              (lam v. acc (assocInsert {eq=eqstr} k v bs))
              e))
    in
    (assocFold {eq=eqstr} f acc bindings) assocEmpty

  | TmRecordUpdate {rec = rec, key = key, value = value} ->
    normalizeName
      (lam vrec.
        normalizeName
          (lam vvalue.
            let ru = (TmRecordUpdate {rec = vrec, key = key, value = vvalue}) in
            bind k ru)
        value)
      rec

end

lang LetANF = ANF + LetAst
  sem isValue =
  | TmLet _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmLet {ident = ident, body = m1, inexpr = m2} ->
    normalize
      (lam n1. (TmLet {ident = ident, body = n1, inexpr = normalize k m2}))
      m1

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
  | TmConDef {ident = ident, tpe = tpe, inexpr = inexpr} ->
    TmConDef {ident = ident, tpe = tpe, inexpr = normalize k inexpr}

  | TmConApp {ident = ident, body = body } ->
    normalizeName
      (lam b. bind k (TmConApp {ident = ident, body = b})) body

end

lang MatchANF = ANF + MatchAst
  sem isValue =
  | TmMatch _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmMatch {target = target, pat = pat, thn = thn, els = els} ->
    normalizeName
      (lam t. bind k (TmMatch {target = t, pat = pat, thn = normalizeTerm thn,
                                                      els = normalizeTerm els}))
      target

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
    let acc = lam ts. bind k (TmSeq {tms = ts}) in
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

  VarANF + AppANF + FunANF + RecordANF + LetANF + RecLetsANF + ConstANF
  + DataANF + MatchANF + UtestANF + SeqANF + NeverANF

  + MExprSym

  + MExprPrettyPrint

mexpr
use MExprANF in

let basic =
  bind_ (let_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (let_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in

let ext =
  bindall_
    [let_ "f" (ulam_ "x" (var_ "x")),
     let_ "x" (int_ 3),
     (addi_ (addi_ (int_ 2) (var_ "x")))
       (bind_ (let_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))] in

let lambda =
  app_
    (ulam_ "x" (bind_ (let_ "y" (int_ 3)) (addi_ (var_ "x") (var_ "y"))))
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
  reclet_ "fact"
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

let debug = false in

let debugPrint = lam t.
  if debug then
    let _ = printLn "--- BEFORE ANF ---" in
    let t = symbolize assocEmpty t in
    let _ = printLn (expr2str t) in
    let _ = print "\n" in
    let _ = printLn "--- AFTER ANF ---" in
    let t = normalizeTerm t in
    let _ = printLn (expr2str t) in
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
     smatch
   ]
in
()
