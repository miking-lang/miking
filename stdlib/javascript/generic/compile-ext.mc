include "javascript/util.mc"
include "javascript/intrinsics.mc"
include "javascript/compile-ext-base.mc"
include "mexpr/info.mc"

include "option.mc"

lang CompileJSGenExt = CompileJSExt

  sem refGen : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem refGen p i =
  | e -> Some (externalRefGen e)

  sem compileExt : CompileJSTargetPlatform -> Info -> String -> Option JSExpr
  sem compileExt p i =
  | "externalExp"   -> refGen p i "exp"
  | "externalLog"   -> refGen p i "log"
  | "externalAtan"  -> refGen p i "atan"
  | "externalSin"   -> refGen p i "sin"
  | "externalCos"   -> refGen p i "cos"
  | "externalAtan2" -> refGen p i "ata"
  | "externalPow"   -> refGen p i "pow"
  | "externalSqrt"  -> refGen p i "sqrt"

end
