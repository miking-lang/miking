include "javascript/util.mc"
include "javascript/ast.mc"
include "mexpr/info.mc"

include "option.mc"

lang CompileJSExt = JSExprAst

sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
sem compileExt p i = -- Empty placeholder for actual externals.

end
