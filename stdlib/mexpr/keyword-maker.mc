

-- TODO: Handle pattern variables as well using smap

include "mexpr/ast.mc"
include "mexpr/info.mc"
include "mexpr/mexpr.mc"
include "mexpr/ast-builder.mc"


lang KeywordMaker = VarAst + AppAst + LetAst + LamAst

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
  | TmLet r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a let expressions."])
     else TmLet {{r with body = makeKeywords [] r.body} with inexpr = makeKeywords [] r.inexpr}
  | TmLam r -> 
     let ident = nameGetStr r.ident in
     match matchKeywordString r.info ident with Some _ then
       infoErrorExit r.info (join ["Keyword '", ident, "' cannot be used in a lambda expressions."])
     else TmLam {r with body = makeKeywords [] r.body}
  | expr -> smap_Expr_Expr (makeKeywords []) expr

end




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

let expr = ulam_ "x" true_ in  -- replace "x" with "noargs" to generate error message
utest makeKeywords [] expr with expr in
--let expr = ulet_ "x" true_ in  -- replace "x" with "twoargs" to generate error message
--utest makeKeywords [] expr with expr in


()
