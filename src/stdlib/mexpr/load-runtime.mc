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
  | TmLet t ->
    TmLet {t with inexpr = mergeWithHeader ast t.inexpr,
                  ty = tyTm ast}
  | TmRecLets t ->
    TmRecLets {t with inexpr = mergeWithHeader ast t.inexpr,
                      ty = tyTm ast}
  | TmType t ->
    TmType {t with inexpr = mergeWithHeader ast t.inexpr,
                   ty = tyTm ast}
  | TmConDef t ->
    TmConDef {t with inexpr = mergeWithHeader ast t.inexpr,
                     ty = tyTm ast}
  | TmUtest t ->
    TmUtest {t with next = mergeWithHeader ast t.next, ty = tyTm ast}
  | TmExt t ->
    TmExt {t with inexpr = mergeWithHeader ast t.inexpr,
                  ty = tyTm ast}
  | _ -> ast

end

