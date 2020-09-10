-- ANF transformation for MExpr programs, adapted from Figure 9 in Flanagan et
-- al. (1993).

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

lang ANF
  sem normalizeTerm =
  | m -> normalize (lam x. x) m

  sem normalize (k : Expr -> Expr) =
  -- Intentionally left blank

end

lang VarANF = ANF + VarSym
  sem isValue =
  | TmVar _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmVar t -> k (TmVar t)

end

lang AppANF = ANF + AppSym + LetAst + VarAst
  sem isValue =
  | TmApp _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmApp t -> normalizeNames k (TmApp t)

  sem normalizeNames (k : Expr -> Expr) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    normalizeNames
      (lam l. normalizeName (lam r. k (TmApp {lhs = l, rhs = r})) rhs)
      lhs
  | t -> normalizeName k t

  sem normalizeName (k : Expr -> Expr) =
  | m ->
    normalize
      (lam n. if (isValue n) then k n else
         let ident = nameSym "t" in
           (TmLet {ident = ident, body = n,
                   inexpr = k (TmVar {ident = ident})}))
      m
end

lang FunANF = ANF + FunSym
  sem isValue =
  | TmLam _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmLam {ident = ident, tpe = tpe, body = body} ->
    k (TmLam {ident = ident, tpe = tpe, body = normalizeTerm body})

end

lang LetANF = ANF + LetSym
  sem isValue =
  | TmLet _ -> false

  sem normalize (k : Expr -> Expr) =
  | TmLet {ident = ident, body = m1, inexpr = m2} ->
    normalize
      (lam n1. (TmLet {ident = ident, body = n1, inexpr = normalize k m2}))
      m1

end

lang ConstANF = ANF + ConstSym
  sem isValue =
  | TmConst _ -> true

  sem normalize (k : Expr -> Expr) =
  | TmConst t -> k (TmConst t)

end

lang MExprANF =
  VarANF + AppANF + FunANF + LetANF + ConstANF

mexpr
use MExprANF in

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
  else ()
in

let basic =
  bind_ (let_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (let_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in

let _ = debugPrint basic in

let ext =
  bindall_
    [let_ "f" (ulam_ "x" (var_ "x")),
     let_ "x" (int_ 3),
     (addi_ (addi_ (int_ 2) (var_ "x")))
       (bind_ (let_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))] in

let _ = debugPrint ext in

()
