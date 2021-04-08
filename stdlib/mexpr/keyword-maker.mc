-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Language fragment KeywordMaker makes it possible to define new keywords
-- in a DSL by just using variables and applications. These new keywords
-- are then used when constructing new terms in the DSL. 
-- See fragment _testKeywordMaker for an example.
-- Note that also keywords starting with capital letters are allowed,
-- using MCore's constructor definition.

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

  sem makeKeywordError (info: Info) (n1: Int) (n2: Int) =
  | ident -> infoErrorExit info (join ["Unexpected number of arguments for construct '",
             ident, "'. ", "Expected ", int2string n1,
             " arguments, but found ", int2string n2, "."])

  sem makeKeywords (args: [Expr]) =
  | TmApp r ->
     let rhs = makeKeywords [] r.rhs in
     let lhs = makeKeywords (cons rhs args) r.lhs in
     if isKeyword lhs then lhs
     else TmApp {{r with lhs = lhs} with rhs = rhs}
  | TmVar r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some (noArgs, f) then
       if eqi noArgs (length args) then f args
       else makeKeywordError r.info noArgs (length args) ident
     else TmVar r
  | expr -> smap_Expr_Expr (makeKeywords []) expr
end

-- Support for keywords starting with capital letter. Uses ConApp and ConDef
lang KeywordMakerData = KeywordMakerBase + DataAst
  sem makeKeywords (args: [Expr]) =
  | TmConApp r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some (noArgs, f) then
       let args = cons r.body args in
       if eqi noArgs (length args) then f args
       else makeKeywordError r.info noArgs (length args) ident
     else TmConApp r
  | TmConDef r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident,
       "' cannot be used in a constructor definition."])
     else TmConDef {r with inexpr = makeKeywords [] r.inexpr}
end   

-- Includes a check that a keyword cannot be used as a binding variable in a lambda
lang KeywordMakerLam = KeywordMakerBase + LamAst
  sem makeKeywords (args: [Expr]) =
  | TmLam r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a lambda expressions."])
     else TmLam {r with body = makeKeywords [] r.body}
end


-- Includes a check that a keyword cannot be used as a binding variable in a let expression
lang KeywordMakerLet = KeywordMakerBase + LetAst
  sem makeKeywords (args: [Expr]) =
  | TmLet r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a let expressions."])
     else
       TmLet {{r with body = makeKeywords [] r.body} with inexpr = makeKeywords [] r.inexpr} 
end


-- Includes a check that a keyword cannot be used inside a pattern (inside match)
lang KeywordMakerMatch = KeywordMakerBase + MatchAst + NamedPat
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
lang KeywordMaker = KeywordMakerBase + KeywordMakerLam + KeywordMakerLet +
                    KeywordMakerMatch + KeywordMakerData


-- A test fragment that is used to test the approach. This
-- fragment can be used as a template when using the keyword maker.
lang _testKeywordMaker = KeywordMaker + MExpr + MExprEq

  -- Example terms that will be used to represent the values of the
  -- the keyword expressions (the new language constructs). The term
  -- first demonstrates a construct without arguments, and the third term
  -- an example where the construct has exactly 2 arguments. The second
  -- and forth terms show that a keyword also can start with a capital letter.
  -- Note that the special case of a keyword with capital letter with zero arguments
  -- is not allowed because MCore does not support constructors with zero arguments.
  syn Expr =
  | TmNoArgs {info: Info}
  | TmOneArg {arg1: Expr, info: Info}
  | TmTwoArgs {arg1: Expr, arg2: Expr, info: Info}
  | TmThreeArgs {arg1: Expr, arg2: Expr, arg3: Expr, info: Info}

  -- States that the new terms are indeed mapping from keywords
  sem isKeyword =
  | TmNoArgs _ -> true
  | TmOneArg _ -> true
  | TmTwoArgs _ -> true
  | TmThreeArgs _ -> true

  -- Defines the new mapping from keyword to new terms
  sem matchKeywordString (info: Info) =
  | "noargs" -> Some (0, lam lst. TmNoArgs{info = info})
  | "OneArg" -> Some (1, lam lst. TmOneArg{arg1 = get lst 0, info = info})
  | "twoargs" -> Some (2, lam lst. TmTwoArgs{arg1 = get lst 0, arg2 = get lst 1, info = info})
  | "ThreeArgs" -> Some (3, lam lst. TmThreeArgs{arg1 = get lst 0, arg2 = get lst 1,
                                                 arg3 = get lst 2, info = info})

  -- smap for the new terms
  sem smap_Expr_Expr (f : Expr -> a) =
  | TmNoArgs t -> TmNoArgs t
  | TmOneArg t -> TmOneArg {t with arg1 = f t.arg1}
  | TmTwoArgs t -> TmTwoArgs {{t with arg1 = f t.arg1} with arg2 = f t.arg2}
  | TmThreeArgs t -> TmThreeArgs {{{t with arg1 = f t.arg1}
                                      with arg2 = f t.arg2} with arg3 = f t.arg3}

  -- Equality of the new terms
  sem eqExprH (env : EqEnv) (free : EqEnv) (lhs : Expr) =
  | TmNoArgs _ ->
      match lhs with TmNoArgs _ then Some free else None ()
  | TmOneArg r ->     
      match lhs with TmOneArg l then
        eqExprH env free l.arg1 r.arg1
      else None ()
  | TmTwoArgs r ->     
      match lhs with TmTwoArgs l then
        match eqExprH env free l.arg1 r.arg1 with Some free then
          eqExprH env free l.arg2 r.arg2
        else None ()
      else None ()
  | TmThreeArgs r ->     
      match lhs with TmThreeArgs l then
        match eqExprH env free l.arg1 r.arg1 with Some free then
          match eqExprH env free l.arg2 r.arg2 with Some free then
            eqExprH env free l.arg3 r.arg3
          else None ()
        else None ()
      else None ()
end


mexpr

-- Test cases for the example fragment
use _testKeywordMaker in

let noargs_ = TmNoArgs {info = NoInfo()} in
let onearg_ = lam x. TmOneArg {arg1 = x, info = NoInfo()} in
let twoargs_ = lam x. lam y. TmTwoArgs {arg1 = x, arg2 = y, info = NoInfo()} in
let threeargs_ = lam x. lam y. lam z.
                 TmThreeArgs {arg1 = x, arg2 = y, arg3 = z, info = NoInfo()} in

-- In the first three utests, replace "ok" with "twoargs" to generate error message
-- that demonstrates that keywords cannot be used inside lambdas, lets, and patterns.
-- Same with the forth, replace "Ok" with "OneArg"

let expr = ulam_ "ok" true_ in  
utest makeKeywords [] expr with expr using eqExpr in

let expr = bind_ (ulet_ "ok" true_) false_ in 
utest makeKeywords [] expr with expr using eqExpr in

let expr = match_ true_  (pvar_ "ok") true_ false_ in
utest makeKeywords [] expr with expr using eqExpr in

let expr = ucondef_ "Ok" in 
utest makeKeywords [] expr with expr using eqExpr in

let expr = ulam_ "x" (var_ "noargs") in
utest makeKeywords [] expr with ulam_ "x" noargs_ using eqExpr in

let expr = ulam_ "x" (conapp_ "OneArg" (true_))  in
utest makeKeywords [] expr with ulam_ "x" (onearg_ true_) using eqExpr in

let expr = ulam_ "x" (app_ (app_ (var_ "twoargs") (true_)) false_) in
utest makeKeywords [] expr with ulam_ "x" (twoargs_ true_ false_) using eqExpr in

let expr = ulam_ "x" (app_ (app_ (conapp_ "ThreeArgs" (true_)) (false_)) true_) in
utest makeKeywords [] expr
with ulam_ "x" (threeargs_ true_ false_ true_) using eqExpr in

()












