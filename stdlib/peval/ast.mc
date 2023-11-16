include "mexpr/keyword-maker.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/type-check.mc"
include "mexpr/eval.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"
include "mexpr/mexpr.mc"

include "peval/peval.mc"
include "error.mc"
include "list.mc"


lang SpecializeAst =
  KeywordMaker + MExprAst + MExprParser + MExprPrettyPrint + MExprSym
  + MExprEq + Eval + PrettyPrint + MExprTypeCheck + LamEval


  syn Expr =
  | TmSpecialize {e: Expr, info: Info}

  -- States that the new terms are indeed mapping from keywords
  sem isKeyword =
  | TmSpecialize _ -> true

  -- Defines the new mapping from keyword to new terms
  sem matchKeywordString (info: Info) =
  | "specialize" -> Some (1, lam lst. TmSpecialize {e = get lst 0,
                                          info = info})
  sem tyTm =
  | TmSpecialize t -> tyTm t.e

  sem infoTm =
  | TmSpecialize t -> t.info

  sem withType (ty : Type) =
  | TmSpecialize t -> TmSpecialize {t with e = withType ty t.e}

  sem typeCheckExpr (env : TCEnv) =
  | TmSpecialize t ->
    let e = typeCheckExpr env t.e in
    TmSpecialize {t with e = e}

  sem smapAccumL_Expr_Expr f acc =
  | TmSpecialize t ->
    match f acc t.e with (acc, e) in
    (acc, TmSpecialize {t with e = e})

  -- Equality of the new terms
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmSpecialize r ->
    match lhs with TmSpecialize l then
      eqExprH env free l.e r.e
    else None ()

  sem eval (ctx : EvalCtx) =
  | TmSpecialize e ->
    switch eval ctx e.e
    case clos & TmClos _ then
      let res = use MExprPEval in peval clos in
        match res with TmLam _ then
          eval (evalCtxEmpty ()) res -- TmClos ...
        else res
    case x then x
    end

  sem isAtomic =
  | TmSpecialize _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmSpecialize t ->
    match printParen indent env t.e with (env, e) in
    (env, join ["specialize", pprintNewline indent , e])

end

let specialize_ = lam e.
  use SpecializeAst in
  TmSpecialize {e = e, info = NoInfo ()}


lang TestLang = SpecializeAst
end

mexpr

use TestLang in

let addfn_ = ulam_ "acc" (ulam_ "i" (addi_ (var_ "acc") (var_ "i"))) in

let expr = app_ (var_ "specialize") addfn_ in
utest makeKeywords expr with specialize_ (addfn_) using eqExpr in

let expr = app_ (var_ "specialize") (app_ addfn_ (int_ 3)) in
utest makeKeywords expr with specialize_ (app_ addfn_ (int_ 3)) using eqExpr in

let arg = (appf2_ addfn_ (int_ 3) (int_ 4)) in
let expr = app_ (var_ "specialize") arg  in
utest makeKeywords expr with specialize_ arg using eqExpr in

let expr = app_ (var_ "specialize") (int_ 3) in
utest makeKeywords expr with specialize_ (int_ 3) using eqExpr in


()
