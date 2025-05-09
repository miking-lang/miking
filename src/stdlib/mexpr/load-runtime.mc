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
  | TmDecl {decl = DeclLet t} ->
    TmDecl {decl = DeclLet {t with inexpr = mergeWithHeader ast t.inexpr,
                  ty = tyTm ast}}
  | TmDecl {decl = DeclRecLets t} ->
    TmDecl {decl = DeclRecLets {t with inexpr = mergeWithHeader ast t.inexpr,
                      ty = tyTm ast}}
  | TmDecl {decl = DeclType t} ->
    TmDecl {decl = DeclType {t with inexpr = mergeWithHeader ast t.inexpr,
                   ty = tyTm ast}}
  | TmDecl {decl = DeclConDef t} ->
    TmDecl {decl = DeclConDef {t with inexpr = mergeWithHeader ast t.inexpr,
                     ty = tyTm ast}}
  | TmDecl {decl = DeclUtest t} ->
    TmDecl {decl = DeclUtest {t with next = mergeWithHeader ast t.next, ty = tyTm ast}}
  | TmDecl {decl = DeclExt t} ->
    TmDecl {decl = DeclExt {t with inexpr = mergeWithHeader ast t.inexpr,
                  ty = tyTm ast}}
  | _ -> ast

end

