
include "mexpr/ast.mc"
include "mexpr/pprint.mc"

mexpr
use MExprPrettyPrint in
let example_ast =
    TmLet ("foo", None,
      TmLam ("a", None, TmLam ("b", None,
        TmLet ("bar", None,
          TmLam ("x", None,
            TmApp (
              TmApp (
                TmVar "addi",
                TmVar "b"
              ),
              TmVar "x"
            )
          ),
          TmLet ("babar", None,
            TmConst (CInt 3),
            TmApp (
              TmApp (
                TmVar "addi",
                TmApp (
                  TmVar "bar",
                  TmVar "babar"
                )
              ),
              TmVar "a"
            )
          )
        )
      )),
      TmConst CUnit
    )
in

--let _ = print "\n" in
--let _ = print (pprintCode 0 example_ast) in
--let _ = print "\n\n" in
--let _ = print (pprintAst 0 example_ast) in
--let _ = print "\n" in

utest geqi (length (pprintAst 0 example_ast)) 0 with true in
utest geqi (length (pprintCode 0 example_ast)) 0 with true in
()
