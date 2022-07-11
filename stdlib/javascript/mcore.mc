-- Defines functions for compiling an MCore program to JS.
-- Used in the src/main/compile.mc file.

include "javascript/compile.mc"


let compileMCoreToJS : Option String -> Expr -> String -> String =
  lam target. lam ast. lam sourcePath.
  let runtimePrint = lam s. printLn (join ["Compiling to JavaScript targeting ", s, " environment..."]) in
  let platform = switch target
    case Some ("node")    then runtimePrint "the node";       CompileJSTP_Node ()
    case Some ("web")     then runtimePrint "a web browser";  CompileJSTP_Web  ()
    case Some ("generic") then runtimePrint "a generic";      CompileJSTP_Normal ()
    case Some (e) then error (join ["Invalid value for --js-target: '", e, "'"])
    case _ then runtimePrint "a generic"; CompileJSTP_Normal ()
  end in
  let res = javascriptCompileFile { compileJSOptionsEmpty with targetPlatform = platform } ast sourcePath in
  printLn (join ["Successfully compiled to JavaScript in ", res]);
  res
