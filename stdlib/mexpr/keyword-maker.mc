-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Language fragment KeywordMaker makes it possible to define new keywords
-- in a DSL by just using variables and applications. These new keywords
-- are then used when constructing new terms in the DSL. 
-- See fragment _testKeywordMaker for an example.

include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/mexpr.mc"
include "mexpr/ast-builder.mc"
include "mexpr/eq.mc"

-- The base fragment that includes the keyword maker, but
-- no checks for incorrect bindings in e.g. let or lam. 
-- See the separate fragments to include this.
lang KeywordMakerBase = VarAst + AppAst 
  sem isKeyword = 
  | _ -> false

  sem matchKeywordString (info: Info) =
  | _ -> None ()

  sem makeKeywords (args: [Expr]) =
  | TmApp r ->
     let rhs = makeKeywords [] r.rhs in
     let lhs = makeKeywords (cons rhs args) r.lhs in
     if isKeyword lhs then lhs
     else TmApp {{r with lhs = lhs} with rhs = rhs}
  | TmVar r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some (noArgs, f) then
       if eqi noArgs (length args) then
       f args
       else infoErrorExit r.info (join ["Unexpected number of arguments for construct '", ident, "'. ",
            "Expected ", int2string noArgs, " arguments, but found ", int2string (length args), "."])
     else TmVar r
  | expr -> smap_Expr_Expr (makeKeywords []) expr
end


-- Includes a check that a keyword cannot be used as a binding variable in a lambda
lang KeywordLam = KeywordMakerBase + LamAst
  sem makeKeywords (args: [Expr]) =
  | TmLam r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a lambda expressions."])
     else TmLam {r with body = makeKeywords [] r.body}
end


-- Includes a check that a keyword cannot be used as a binding variable in a let expression
lang KeywordLet = KeywordMakerBase + LetAst
  sem makeKeywords (args: [Expr]) =
  | TmLet r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a let expressions."])
     else
       TmLet {{r with body = makeKeywords [] r.body} with inexpr = makeKeywords [] r.inexpr} 
end


-- Includes a check that a keyword cannot be used inside a pattern (inside match)
lang KeywordMatch = KeywordMakerBase + MatchAst + NamedPat
  sem matchKeywordPat =
  | PatNamed r ->
      match r.ident with PName name then
        let ident = nameGetStr name in
        match matchKeywordString r.info ident with Some _ then
          infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used inside a pattern."])
        else PatNamed r
      else PatNamed r
  | pat -> smap_Pat_Pat matchKeywordPat pat

  sem makeKeywords (args: [Expr]) =
  | TmMatch r -> 
      TmMatch {{{{r with target = makeKeywords [] r.target}
                    with pat = matchKeywordPat r.pat}
                    with thn = makeKeywords [] r.thn}
                    with els = makeKeywords [] r.els}
end                  


-- The keyword maker fragment, that includes all checks
lang KeywordMaker = KeywordMakerBase + KeywordLam + KeywordLet + KeywordMatch


-- A test fragment that is used to test the approach. This
-- fragment can be used as a template when using the keyword maker.
lang _testKeywordMaker = KeywordMaker + MExpr + MExprEq

  -- Example terms that will be used to represent the values of the
  -- the keyword expressions (the new language constructs). The term
  -- first demonstrates a construct without arguments, and the second term
  -- an example where the construct has exactly 2 arguments.
  syn Expr =
  | TmNoArgs {info: Info}
  | TmTwoArgs {arg1: Expr, arg2: Expr, info: Info}

  -- States that the new terms are indeed mapping from keywords
  sem isKeyword =
  | TmNoArgs _ -> true
  | TmTwoArgs _ -> true

  -- Defines the new mapping from keyword to new terms
  sem matchKeywordString (info: Info) =
  | "noargs" -> Some (0, lam lst. TmNoArgs{info = info})
  | "twoargs" -> Some (2, lam lst. TmTwoArgs{arg1 = get lst 0, arg2 = get lst 1, info = info})

  -- smap for the new terms
  sem smap_Expr_Expr (f : Expr -> a) =
  | TmNoArgs t -> TmNoArgs t
  | TmTwoArgs t -> TmTwoArgs {{t with arg1 = f t.arg1} with arg2 = f t.arg2}

  -- Equality of the new terms
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmNoArgs _ ->
      match lhs with TmNoArgs _ then Some free else None ()
  | TmTwoArgs r ->     
      match lhs with TmTwoArgs l then
        match eqExprH env free l.arg1 r.arg1 with Some free then
          eqExprH env free l.arg2 r.arg2
        else None ()
      else None ()
end


mexpr

-- Test cases for the example fragment
use _testKeywordMaker in

let noargs_ = TmNoArgs {info = NoInfo()} in
let twoargs_ = lam x. lam y. TmTwoArgs {arg1 = x, arg2 = y, info = NoInfo()} in

-- In the first three utests, replace "ok" with "twoargs" to generate error message
-- that demonstrates that keywords cannot be used inside lambdas, lets, and patterns.

let expr = ulam_ "ok" true_ in  
utest makeKeywords [] expr with expr using eqExpr in

let expr = bind_ (ulet_ "ok" true_) false_ in 
utest makeKeywords [] expr with expr using eqExpr in

let expr = match_ true_  (pvar_ "ok") true_ false_ in
utest makeKeywords [] expr with expr using eqExpr in

let expr = ulam_ "x" (var_ "noargs") in
utest makeKeywords [] expr with ulam_ "x" noargs_ using eqExpr in

let expr = ulam_ "x" (app_ (app_ (var_ "twoargs") (true_)) false_) in
utest makeKeywords [] expr with ulam_ "x" (twoargs_ true_ false_) using eqExpr in

()












