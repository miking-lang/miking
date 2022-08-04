include "option.mc"
include "name.mc"

--------------------
-- COMPILER TYPES --
--------------------

-- Supported JS runtime targets
type CompileJSTargetPlatform
con CompileJSTP_Normal : () -> CompileJSTargetPlatform
con CompileJSTP_Web    : () -> CompileJSTargetPlatform
con CompileJSTP_Node   : () -> CompileJSTargetPlatform

-- JS Compiler options
type CompileJSOptions = {
  targetPlatform : CompileJSTargetPlatform,
  debugMode : Bool,
  optimizations : Bool
}

let compileJSOptionsEmpty : CompileJSOptions = {
  targetPlatform = CompileJSTP_Normal (),
  debugMode = false,
  optimizations = true
}

type CompileJSContext = {
  options : CompileJSOptions,
  currentFunction: Option (Name, Info),
  recursiveFunctions: Set Name
}

-- Empty compile JS environment
let compileJSCtxEmpty = {
  options = compileJSOptionsEmpty,
  currentFunction = None (),
  recursiveFunctions = setEmpty nameCmp
}
