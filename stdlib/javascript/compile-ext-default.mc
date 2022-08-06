include "javascript/ast.mc"
include "javascript/util.mc"
include "javascript/compile-ext-base.mc"
include "mexpr/info.mc"

include "option.mc"

-- Import the standard externals library.
include "javascript/generic/compile-ext.mc"
include "javascript/node/compile-ext.mc"
include "javascript/web/compile-ext.mc"

lang CompileJSDefaultExt = CompileJSExt + CompileJSGenExt + CompileJSWebExt + CompileJSNodeExt

sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
sem compileExt p i =
| _ -> None () -- Return None if the extension is not implemented by the standard library.

end
