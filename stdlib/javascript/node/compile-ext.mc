include "javascript/util.mc"
include "javascript/intrinsics.mc"
include "javascript/compile-ext-base.mc"
include "mexpr/info.mc"

include "option.mc"
include "error.mc"

lang CompileJSNodeExt = CompileJSExt

  sem refNode : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem refNode p i =
  | e ->
    match p with CompileJSTP_Node () then Some (externalRefNode e)
    else errorSingle [i] (join ["Unsupported external '", e, "' when compiling to JavaScript and not targeting node."])

  sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem compileExt p i = -- No externals for node yet.

end
