include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "common.mc"

-- Inspired by MCoreCompileLang
lang JavaScriptCompileLang =
  BootParser +
  MExprSym +
  MExprUtestTrans
end

let javascriptCompile : Expr -> String -> Bool =
  lam ast : Expr. lam sourcePath: String.
  printLn sourcePath
  true