include "stdlib.mc"
include "mexpr/symbolize.mc"
include "mexpr/boot-parser.mc"
include "mexpr/type-check.mc"


lang MExprLoadRuntime = BootParser + MExprSym + MExprTypeCheck

  sem loadRuntime : String -> Expr
  sem loadRuntime =
  | file ->
      let args = defaultBootParserParseMCoreFileArg in
      let utestRuntimeFile = concat stdlibLoc file in
      let ast = typeCheck (symbolize (parseMCoreFile args utestRuntimeFile)) in
      ast

  sem mergeWithHeader : Expr -> Expr -> Expr
  sem mergeWithHeader ast =
  | TmDecl x ->
    TmDecl {x with inexpr = mergeWithHeader ast x.inexpr, ty = tyTm ast}
  | _ -> ast

end
