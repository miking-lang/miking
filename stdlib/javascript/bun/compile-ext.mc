include "javascript/util.mc"
include "javascript/intrinsics.mc"
include "javascript/compile-ext-base.mc"
include "mexpr/info.mc"

include "option.mc"
include "error.mc"

lang CompileJSBunExt = CompileJSExt

  sem refBun : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem refBun p i =
  | e ->
    match p with CompileJSTP_Bun () then Some (externalRefBun e)
    else errorSingle [i] (join ["Unsupported external '", e, "' when compiling to JavaScript and not targeting bun."])

  sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem compileExt p i = -- No externals for bun yet.
  -- TODO: Add external implementations for `stdlib/ext/file-ext.mc`

end
