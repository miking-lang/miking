-- Defines functions for compiling an MCore program to JS.
-- Used in the src/main/compile.mc file.

include "javascript/compile.mc"

let platformMapJS = mapFromSeq cmpString
  [("generic", CompileJSTP_Generic ())
  ,("node", CompileJSTP_Node ())
  ,("bun", CompileJSTP_Bun ())
  ,("web", CompileJSTP_Web ())]

let compileMCoreToJS : use Ast in CompileJSOptions -> Expr -> String -> String =
  lam opts. lam ast. lam sourcePath.
  let outfile = javascriptCompileFile opts ast sourcePath in
  printLn (concat "Successfully compiled file to: " outfile);
  outfile


let parseJSTarget : String -> CompileJSTargetPlatform =
  lam target.
  match mapLookup target platformMapJS with Some p then
    printLn (concat "Target JavaScript platform: " target); p
  else error (join ["Invalid value for --js-target: '", target, "'\nAccepted values: ", strJoin ", " (mapKeys platformMapJS)])
