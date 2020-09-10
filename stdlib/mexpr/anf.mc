-- ANF transformation for MExpr programs

include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/pprint.mc"
include "mexpr/symbolize.mc"

lang MExprANF = MExprSym
  sem isValue =
  | TmLam _ -> true
  | TmVar _ -> true
  | TmConst _ -> true
  | _ -> false

  sem normalizeTerm =
  | m -> normalize (lam x. x) m

  sem normalize (k : Expr -> Expr) =
  | TmLam {ident = ident, tpe = tpe, body = body} ->
    k (TmLam {ident = ident, tpe = tpe, body = normalizeTerm body})

  | TmLet {ident = ident, body = m1, inexpr = m2} ->
    normalize
      (lam n1. (TmLet {ident = ident, body = n1, inexpr = normalize k m2}))
      m1

  | TmApp t -> normalizeNames k (TmApp t)

  | TmVar t -> k (TmVar t)
  | TmConst t -> k (TmConst t)

  sem normalizeName (k : Expr -> Expr) =
  | m ->
    normalize
      (lam n. if (isValue n) then k n else
         let ident = nameSym "t" in
           (TmLet {ident = ident, body = n,
                   inexpr = k (TmVar {ident = ident})}))
      m

  sem normalizeNames (k : Expr -> Expr) =
  | TmApp {lhs = lhs, rhs = rhs} ->
    normalizeNames
      (lam l. normalizeName (lam r. k (TmApp {lhs = l, rhs = r})) rhs)
      lhs
  | t -> normalizeName k t

end

mexpr
use MExprANF in

let _anf = (lam t. normalizeTerm (symbolize assocEmpty t)) in

let basic =
  bind_ (let_ "f" (ulam_ "x" (var_ "x")))
  (addi_ (addi_ (int_ 2) (int_ 2))
    (bind_ (let_ "x" (int_ 1)) (app_ (var_ "f") (var_ "x")))) in

let _ = printLn (expr2str basic) in
let _ = print "\n------\n" in
let _ = printLn (expr2str (_anf basic)) in

()
