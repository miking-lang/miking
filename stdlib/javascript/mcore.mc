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
    javascriptCompileFile { compileJSOptionsEmpty with targetPlatform = p } ast sourcePath
  else
    error (join ["Invalid value for --js-target: '", target, "'\nAccepted values: ", strJoin ", " (mapKeys platformMapJS)])
