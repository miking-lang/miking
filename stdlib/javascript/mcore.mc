-- Defines functions for compiling an MCore program to JS.
-- Used in the src/main/compile.mc file.

include "javascript/compile.mc"

let platformMapJS = mapFromSeq cmpString
  [("generic", CompileJSTP_Normal ())
  ,("node", CompileJSTP_Node ())
  ,("web", CompileJSTP_Web ())]

let compileMCoreToJS : String -> Expr -> String -> String =
  lam target. lam ast. lam sourcePath.
  match mapLookup target platformMapJS with Some p then
    printLn (concat "Target JavaScript platform: " target);
    let outfile = javascriptCompileFile { compileJSOptionsEmpty with targetPlatform = p } ast sourcePath in
    printLn (concat "Successfully compiled file to: " outfile);
    outfile
  else
    error (join ["Invalid value for --js-target: '", target, "'\nAccepted values: ", strJoin ", " (mapKeys platformMapJS)])
