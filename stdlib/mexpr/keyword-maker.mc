-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--

include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/mexpr.mc"
include "mexpr/ast-builder.mc"


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
       if eqi (noArgs (length args)) then f args
       else infoErrorExit r.info (join ["Unexpected number of arguments for keyword '", ident, "'."])
     else TmVar r
  | expr -> smap_Expr_Expr (makeKeywords []) expr
end


lang KeywordLam = KeywordMakerBase + LamAst
  sem makeKeywords (args: [Expr]) =
  | TmLam r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a lambda expressions."])
     else TmLam {r with body = makeKeywords [] r.body}
end


lang KeywordLet = KeywordMakerBase + LetAst
  sem makeKeywords (args: [Expr]) =
  | TmLet r ->
     dprint "*********** 1";
     let ident = nameGetStr r.ident in
     dprint ["*********** 2", ident, r.info, matchKeywordString r.info ident];
     match matchKeywordString r.info ident with Some _ then
       dprint "*********** 3";
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a let expressions."])
     else
       dprint ["*********** 4", makeKeywords [] r.body];
       dprint ["*********** 5", makeKeywords [] r.inexpr];
--       let x = TmLet {{r with body = makeKeywords [] r.body} with inexpr = makeKeywords [] r.inexpr} in 
--       let x = TmLet {r with body = makeKeywords [] r.body} in 
       let x = TmLet r in 
       dprint "*********** 6";
       x       
end



lang KeywordMaker = KeywordMakerBase + KeywordLam + KeywordLet


lang _testKeywordMaker = KeywordMaker + MExpr
  syn Expr =
  | TmNoArgs {info: Info}
  | TmTwoArgs {arg1: Expr, arg2: Expr, info: Info}

  sem isKeyword =
  | TmNoArgs _ -> true
  | TmTwoArgs _ -> true

  sem matchKeywordString (info: Info) =
  | "noargs" -> Some (0, lam lst. TmNoArgs{info = info})
  | "twoargs" -> Some (2, lam lst. TmTwoArgs{arg1 = get lst 0, arg2 = lst 1, info = info})

  sem smap_Expr_Expr (f : Expr -> a) =
  | TmNoArgs t -> TmNoArgs t
  | TmTwoArgs t -> TmTwoArgs {{t with arg1 = f t.arg1} with arg2 = f t.arg2}
end

mexpr


use _testKeywordMaker in

--let expr = ulam_ "x" true_ in  -- replace "x" with "noargs" to generate error message
--utest makeKeywords [] expr with expr in
let expr = ulet_ "x" true_ in  -- replace "x" with "twoargs" to generate error message
let xx = makeKeywords [] expr in
print "\n\n";
--dprint expr;
--print "\n\n";
--dprint xx;
--utest makeKeywords [] expr with expr in
dprint unit_;
utest unit_ with unit_ in


()


/-
LetAst_TmLet {
  tyBody = (UnknownTypeAst_TyUnknown {info = (NoInfo ())}),
  inexpr = (RecordAst_TmRecord {
               bindings = map,
               info = (NoInfo ()),
               ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})
            }),
  ident = (("x"),symb(26162)),
  info = (NoInfo ()),
  body = (ConstAst_TmConst {
            info = (NoInfo ()),
            val = (BoolAst_CBool {val = true}),
            ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})
          }),
  ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})
}

LetAst_TmLet {tyBody = (UnknownTypeAst_TyUnknown {info = (NoInfo ())}),inexpr = (RecordAst_TmRecord {bindings = map,info = (NoInfo ()),ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})}),ident = (("x"),symb(26162)),info = (NoInfo ()),body = (ConstAst_TmConst {info = (NoInfo ()),val = (BoolAst_CBool {val = true}),ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})}),ty = (UnknownTypeAst_TyUnknown {info = (NoInfo ())})} OK
Unit testing SUCCESSFUL after executing 0 tests.
-/










