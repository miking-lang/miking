include "javascript/util.mc"
include "javascript/intrinsics.mc"
include "javascript/compile-ext-base.mc"
include "mexpr/info.mc"

include "option.mc"
include "error.mc"

lang CompileJSWebExt = CompileJSExt

  sem refWeb : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem refWeb p i =
  | e ->
    match p with CompileJSTP_Web () then Some (externalRefWeb e)
    else errorSingle [i] (join ["Unsupported external '", e, "' when compiling to JavaScript and not targeting the web."])

  sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem compileExt p i =
  -- External implementations for `javascript/web/dom-api-ext.mc`
  | "getDocument" -> refWeb p i "getDocument"

end
