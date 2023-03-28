-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Language fragment KeywordMaker makes it possible to define new keywords
-- in a DSL by just using variables and applications. These new keywords
-- are then used when constructing new terms in the DSL.
-- See fragment _testKeywordMaker for an example.
-- Note that also keywords starting with capital letters are allowed,
-- using MCore's constructor definition.

include "ast.mc"
include "info.mc"
include "error.mc"
include "ast-builder.mc"
include "eq.mc"

-- The base fragment that includes the keyword maker, but
-- no checks for incorrect bindings in e.g. let or lam.
-- See the separate fragments to include this.
lang KeywordMakerBase = VarAst + AppAst + ConTypeAst + AppTypeAst
  sem isKeyword =
  | _ -> false

  sem isTypeKeyword =
  | _ -> false

  sem matchKeywordString (info: Info) =
  | _ -> None ()

  sem matchTypeKeywordString : Info -> String -> Option (Int, [Type] -> Type)
  sem matchTypeKeywordString (info: Info) =
  | _ -> None ()

  sem makeKeywordError : all a. Info -> Int -> Int -> String -> a
  sem makeKeywordError (info: Info) (n1: Int) (n2: Int) =
  | ident -> errorSingle [info] (join ["Unexpected number of arguments for construct '",
             ident, "'. ", "Expected ", int2string n1,
             " arguments, but found ", int2string n2, "."])

  sem makeKeywords : Expr -> Expr
  sem makeKeywords =
  | expr ->
    let expr = makeExprKeywords [] expr in
    let expr = mapPre_Expr_Expr (lam expr.
        smap_Expr_Type (makeTypeKeywords []) expr
      ) expr
    in expr

  sem makeExprKeywords (args: [Expr]) =
  | TmApp r ->
     let rhs = makeExprKeywords [] r.rhs in
     let lhs = makeExprKeywords (cons rhs args) r.lhs in
     if isKeyword lhs then lhs
     else TmApp {r with lhs = lhs, rhs = rhs}
  | TmVar r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some n then
       match n with (noArgs, f) then
         if eqi noArgs (length args) then f args
         else makeKeywordError r.info noArgs (length args) ident
       else never
     else TmVar r
  | expr -> smap_Expr_Expr (makeExprKeywords []) expr

  sem makeTypeKeywords : [Type] -> Type -> Type
  sem makeTypeKeywords args =
  | TyApp r ->
    let rhs = makeTypeKeywords [] r.rhs in
    let lhs = makeTypeKeywords (cons rhs args) r.lhs in
    if isTypeKeyword lhs then lhs
    else TyApp {r with lhs = lhs, rhs = rhs}
  | TyCon r ->
    let ident = nameGetStr r.ident in
    match matchTypeKeywordString r.info ident with Some n then
       match n with (noArgs, f) then
         if eqi noArgs (length args) then f args
         else makeKeywordError r.info noArgs (length args) ident
       else never
     else TyCon r
  | ty -> smap_Type_Type (makeTypeKeywords []) ty

end

-- Support for keywords starting with capital letter. Uses ConApp and ConDef
lang KeywordMakerData = KeywordMakerBase + DataAst
  sem makeExprKeywords (args: [Expr]) =
  | TmConApp r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some n then
       match n with (noArgs, f) then
         let args = cons r.body args in
         if eqi noArgs (length args) then f args
         else makeKeywordError r.info noArgs (length args) ident
       else never
     else TmConApp r
  | TmConDef r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       errorSingle [r.info] (join ["Keyword '", ident,
       "' cannot be used in a constructor definition."])
     else TmConDef {r with inexpr = makeExprKeywords [] r.inexpr}
end

lang KeywordMakerType = KeywordMakerBase + TypeAst
  sem makeExprKeywords (args: [Expr]) =
  | TmType r ->
     let ident = nameGetStr r.ident in
     match matchTypeKeywordString r.info ident with Some _ then
       errorSingle [r.info] (join ["Type keyword '", ident,
       "' cannot be used in a type definition."])
     else TmType {r with inexpr = makeExprKeywords [] r.inexpr}
end

-- Includes a check that a keyword cannot be used as a binding variable in a lambda
lang KeywordMakerLam = KeywordMakerBase + LamAst
  sem makeExprKeywords (args: [Expr]) =
  | TmLam r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       errorSingle [r.info] (join ["Keyword '", ident, "' cannot be used in a lambda expressions."])
     else TmLam {r with body = makeExprKeywords [] r.body}
end


-- Includes a check that a keyword cannot be used as a binding variable in a let expression
lang KeywordMakerLet = KeywordMakerBase + LetAst
  sem makeExprKeywords (args: [Expr]) =
  | TmLet r ->
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       errorSingle [r.info] (join ["Keyword '", ident, "' cannot be used in a let expressions."])
     else
       TmLet {{r with body = makeExprKeywords [] r.body} with inexpr = makeExprKeywords [] r.inexpr}
end


-- Includes a check that a keyword cannot be used inside a pattern (inside match)
lang KeywordMakerMatch = KeywordMakerBase + MatchAst + NamedPat
  sem matchKeywordPat =
  | PatNamed r ->
      match r.ident with PName name then
        let ident = nameGetStr name in
        match matchKeywordString r.info ident with Some _ then
          errorSingle [r.info] (join ["Keyword '", ident, "' cannot be used inside a pattern."])
        else PatNamed r
      else PatNamed r
  | pat -> smap_Pat_Pat matchKeywordPat pat

  sem makeExprKeywords (args: [Expr]) =
  | TmMatch r ->
      TmMatch {{{{r with target = makeExprKeywords [] r.target}
                    with pat = matchKeywordPat r.pat}
                    with thn = makeExprKeywords [] r.thn}
                    with els = makeExprKeywords [] r.els}
end


-- The keyword maker fragment, that includes all checks
lang KeywordMaker = KeywordMakerBase + KeywordMakerLam + KeywordMakerLet +
                    KeywordMakerMatch + KeywordMakerData + KeywordMakerType
end

-- A test fragment that is used to test the approach. This
-- fragment can be used as a template when using the keyword maker.
lang _testKeywordMaker = KeywordMaker + MExprEq

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

  syn Type =
  | TyNoArgs {info: Info}
  | TyOneArg {arg1: Type, info: Info}
  | TyTwoArgs {arg1: Type, arg2: Type, info: Info}
  | TyThreeArgs {arg1: Type, arg2: Type, arg3: Type, info: Info}

  -- States that the new terms are indeed mapping from keywords
  sem isKeyword =
  | TmNoArgs _ -> true
  | TmOneArg _ -> true
  | TmTwoArgs _ -> true
  | TmThreeArgs _ -> true

  sem isTypeKeyword =
  | TyNoArgs _ -> true
  | TyOneArg _ -> true
  | TyTwoArgs _ -> true
  | TyThreeArgs _ -> true

  -- Defines the new mapping from keyword to new terms
  sem matchKeywordString (info: Info) =
  | "noargs" -> Some (0, lam lst. TmNoArgs{info = info})
  | "OneArg" -> Some (1, lam lst. TmOneArg{arg1 = get lst 0, info = info})
  | "twoargs" -> Some (2, lam lst. TmTwoArgs{arg1 = get lst 0, arg2 = get lst 1, info = info})
  | "ThreeArgs" -> Some (3, lam lst. TmThreeArgs{arg1 = get lst 0, arg2 = get lst 1,
                                                 arg3 = get lst 2, info = info})

  sem matchTypeKeywordString (info: Info) =
  | "TyNoArgs" -> Some (0, lam lst. TyNoArgs{info = info})
  | "TyOneArg" -> Some (1, lam lst. TyOneArg{arg1 = get lst 0, info = info})
  | "TyTwoArgs" -> Some (2, lam lst. TyTwoArgs{arg1 = get lst 0, arg2 = get lst 1, info = info})
  | "TyThreeArgs" -> Some (3, lam lst. TyThreeArgs{arg1 = get lst 0, arg2 = get lst 1,
                                                 arg3 = get lst 2, info = info})

  -- smap for the new terms
  sem smap_Expr_Expr (f : Expr -> Expr) =
  | TmNoArgs t -> TmNoArgs t
  | TmOneArg t -> TmOneArg {t with arg1 = f t.arg1}
  | TmTwoArgs t -> TmTwoArgs {{t with arg1 = f t.arg1} with arg2 = f t.arg2}
  | TmThreeArgs t -> TmThreeArgs {{{t with arg1 = f t.arg1}
                                      with arg2 = f t.arg2} with arg3 = f t.arg3}

  sem smap_Type_Type (f : Type -> Type) =
  | TyNoArgs t -> TyNoArgs t
  | TyOneArg t -> TyOneArg {t with arg1 = f t.arg1}
  | TyTwoArgs t -> TyTwoArgs {{t with arg1 = f t.arg1} with arg2 = f t.arg2}
  | TyThreeArgs t -> TyThreeArgs {{{t with arg1 = f t.arg1}
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

  sem eqTypeH (typeEnv : EqTypeEnv) (free : EqTypeFreeEnv) (lhs : Type) =
  | TyNoArgs _ ->
      match unwrapType lhs with TyNoArgs _ then Some free
      else None ()
  | TyOneArg r ->
      match unwrapType lhs with TyOneArg l then
        eqTypeH typeEnv free l.arg1 r.arg1
      else None ()
  | TyTwoArgs r ->
      match unwrapType lhs with TyTwoArgs l then
        match eqTypeH typeEnv free l.arg1 r.arg1 with Some free then
          eqTypeH typeEnv free l.arg2 r.arg2
        else None ()
      else None ()
  | TyThreeArgs r ->
      match unwrapType lhs with TyThreeArgs l then
        match eqTypeH typeEnv free l.arg1 r.arg1 with Some free then
          match eqTypeH typeEnv free l.arg2 r.arg2 with Some free then
            eqTypeH typeEnv free l.arg3 r.arg3
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
utest makeKeywords expr with expr using eqExpr in

let expr = bind_ (ulet_ "ok" true_) false_ in
utest makeKeywords expr with expr using eqExpr in

let expr = match_ true_  (pvar_ "ok") true_ false_ in
utest makeKeywords expr with expr using eqExpr in

let expr = ucondef_ "Ok" in
utest makeKeywords expr with expr using eqExpr in

let expr = ulam_ "x" (var_ "noargs") in
utest makeKeywords expr with ulam_ "x" noargs_ using eqExpr in

let expr = ulam_ "x" (conapp_ "OneArg" (true_))  in
utest makeKeywords expr with ulam_ "x" (onearg_ true_) using eqExpr in

let expr = ulam_ "x" (app_ (app_ (var_ "twoargs") (true_)) false_) in
utest makeKeywords expr with ulam_ "x" (twoargs_ true_ false_) using eqExpr in

let expr = ulam_ "x" (app_ (app_ (conapp_ "ThreeArgs" (true_)) (false_)) true_) in
utest makeKeywords expr
with ulam_ "x" (threeargs_ true_ false_ true_) using eqExpr in

let tynoargs_ = TyNoArgs {info = NoInfo()} in
let tyonearg_ = lam x. TyOneArg {arg1 = x, info = NoInfo()} in
let tytwoargs_ = lam x. lam y. TyTwoArgs {arg1 = x, arg2 = y, info = NoInfo()} in
let tythreeargs_ = lam x. lam y. lam z.
                 TyThreeArgs {arg1 = x, arg2 = y, arg3 = z, info = NoInfo()} in

let expr = lam_ "x" (tycon_ "NoArgs") true_ in
utest makeKeywords expr with lam_ "x" tynoargs_ true_ using eqExpr in

let expr = lam_ "x" (tyapp_ (tycon_ "OneArg") tybool_) true_ in
utest makeKeywords expr with lam_ "x" (tyonearg_ tybool_) true_ using eqExpr in

let expr = lam_ "x" (tyapp_ (tyapp_ (tycon_ "TwoArgs") tybool_) tyint_) true_ in
utest makeKeywords expr with lam_ "x" (tytwoargs_ tybool_ tyint_) true_ using eqExpr in

let expr = lam_ "x" (tyapp_ (tyapp_ (tyapp_ (tycon_ "ThreeArgs") tybool_) tyint_) tybool_) true_ in
utest makeKeywords expr
with lam_ "x" (tythreeargs_ tybool_ tyint_ tybool_) true_ using eqExpr in

()
