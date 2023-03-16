include "mexpr/keyword-maker.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/type-check.mc"
include "mexpr/type-annot.mc"
include "mexpr/eval.mc"
include "mexpr/info.mc"
include "mexpr/eq.mc"

include "peval/peval.mc"
include "error.mc"
include "list.mc"


lang PEvalAst = KeywordMaker + MExpr + MExprEq + Eval + PrettyPrint
                + MExprTypeCheck + LamEval + TypeAnnot + MExprPEval

  syn Expr =
  | TmPEval {e: Expr, info: Info}

  -- States that the new terms are indeed mapping from keywords
  sem isKeyword =
  | TmPEval _ -> true

  -- Defines the new mapping from keyword to new terms
  sem matchKeywordString (info: Info) =
  | "peval" -> Some (1, lam lst. TmPEval {e = get lst 0,
                                          info = info})
  sem tyTm = 
  | TmPEval t -> tyTm t.e

  sem infoTm =
  | TmPEval t -> t.info

  sem withType (ty : Type) =
  | TmPEval t -> TmPEval {t with e = withType ty t.e}

  sem typeCheckExpr (env : TCEnv) = 
  | TmPEval t -> 
    let e = typeCheckExpr env t.e in
    TmPEval {t with e = e}

  sem typeAnnotExpr (env : TypeEnv) = 
  | TmPEval t -> 
    let e = typeAnnotExpr env t.e in
    TmPEval {t with e = e}

  sem smapAccumL_Expr_Expr f acc =
  | TmPEval t ->
    match f acc t.e with (acc, e) in
    (acc, TmPEval {t with e = e})

  -- Equality of the new terms
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmPEval r ->
      match lhs with TmPEval l then
        eqExprH env free l.e r.e
      else None ()

  sem eval (ctx : EvalCtx) = 
  | TmPEval e -> 
  switch eval ctx e.e 
    case clos & TmClos {ident=i, body=b, env=envi} then
        match peval clos with res then
            match res with TmLam t then
                eval ctx res -- TmClos ...
            else res
        else never
    case x then x
  end 

  sem isAtomic = 
  | TmPEval _ -> false

  sem pprintCode (indent : Int) (env : PprintEnv) =
  | TmPEval t ->
    match printParen indent env t.e with (env, e) in
     (env, join ["peval", pprintNewline indent , e])

end

let peval_ = lam e.
  use PEvalAst in 
  TmPEval {e = e, info = NoInfo ()}


lang TestLang = PEvalAst + MExprEval
end 

mexpr 

use TestLang in

let addfn_ = ulam_ "acc" (ulam_ "i" (addi_ (var_ "acc") (var_ "i"))) in

let expr = app_ (var_ "peval") addfn_ in
utest makeKeywords expr with peval_ (addfn_) using eqExpr in 

let expr = app_ (var_ "peval") (app_ addfn_ (int_ 3)) in
utest makeKeywords expr with peval_ (app_ addfn_ (int_ 3)) using eqExpr in

let arg = (appf2_ addfn_ (int_ 3) (int_ 4)) in
let expr = app_ (var_ "peval") arg  in
utest makeKeywords expr with peval_ arg using eqExpr in

let expr = app_ (var_ "peval") (int_ 3) in
utest makeKeywords expr with peval_ (int_ 3) using eqExpr in


()
