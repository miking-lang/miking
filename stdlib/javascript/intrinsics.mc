include "mexpr/ast.mc"
include "mexpr/const-arity.mc"
include "javascript/ast.mc"


-- Fragments used by the intrinsic functions
lang CompileJSOptimizedIntrinsics = JSExprAst + MExprAst + MExprArity
end

-- Compile intrinsic function template (MExpr_JS_Intrinsics.[name])
let intrinsic : Name -> String -> [JSExpr] -> JSExpr =
  use CompileJSOptimizedIntrinsics in
  lam runtime. lam name. lam args.
    -- If there is at least one argument, apply the intrinsic function
    -- to the arguments.
    if gti (length args) 0 then
      JSEApp {
        fun = JSEMember {
          expr = JSEVar { id = runtime },
          id = name
        },
        args = args,
        curried = true
      }
    else -- No arguments, return the function itself
      JSEMember {
        expr = JSEVar { id = runtime },
        id = name
      }

let optimizedOpIntrinsic : Name -> Const -> String -> [JSExpr] -> ([JSExpr] -> JSEBinOp) -> JSExpr =
  use CompileJSOptimizedIntrinsics in
  lam runtime. lam const. lam name. lam args. lam opFun.
    -- Check if the arguments is fully applied (have the same length as constArity(const))
    -- If so, then optimize the intrinsic and return an in-place operation
    -- Otherwise, return a partially applied intrinsic
    if eqi (length args) (constArity const) then opFun args
    else intrinsic runtime name args


---------------------------------------------------
--- Namespaces for the exisitng runtime targets ---
---------------------------------------------------

let intrGenNS = nameSym "MExpr_JS_Intrinsics"
let intrWebNS = nameSym "MExpr_Web_JS_Intrinsics"
let intrNodeNS = nameSym "MExpr_Node_JS_Intrinsics"

let jsIntrinsicsFile_generic = "stdlib/javascript/intrinsics.js"
let jsIntrinsicsFile_web = "stdlib/javascript/web/intrinsics.js"
let jsIntrinsicsFile_node = "stdlib/javascript/node/intrinsics.js"

let intrinsicGen = intrinsic intrGenNS
let intrinsicWeb = intrinsic intrWebNS
let intrinsicNode = intrinsic intrNodeNS

let optimizedOpIntrinsicGen = optimizedOpIntrinsic intrGenNS
let optimizedOpIntrinsicWeb = optimizedOpIntrinsic intrinsicWeb
let optimizedOpIntrincNode = optimizedOpIntrinsic intrinsicNode
