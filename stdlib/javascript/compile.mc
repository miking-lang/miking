include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "sys.mc"
include "common.mc"

--== Helper functions ==--

-- let filename = lam path.
--   match strLastIndex '/' path with Some idx then
--     subsequence path (addi idx 1) (length path)
--   else path

-- let dirname = lam path.
--   match strLastIndex '/' path with Some idx then
--     subsequence path 0 idx
--   else ""

let filepathWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename


let pprintMcore : Expr -> String =
  lam ast.
  use MExprPrettyPrint in
  expr2str ast


-- Inspired by MCoreCompileLang
lang JavaScriptCompileLang =
  BootParser +
  MExprSym +
  MExprUtestTrans
end

let javascriptCompile : Expr -> String -> Bool =
  lam ast : Expr. lam sourcePath: String.
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  printLn targetPath;
  printLn (pprintMcore ast);
  true