include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "mexpr/const-arity.mc"
include "javascript/ast.mc"


-- Fragments used by the intrinsic functions
lang CompileJSOptimizedIntrinsics = JSExprAst + MExprAst + MExprArity + MExprPrettyPrint

  -- Compile intrinsic function
  sem intrinsicFromString : Name -> String -> [JSExpr] -> JSExpr
  sem intrinsicFromString runtime name =
  | [] -> JSEMember {
    expr = JSEVar { id = runtime },
    id = name
  }
  | args -> JSEApp {
    fun = JSEMember {
      expr = JSEVar { id = runtime },
      id = name
    },
    args = args,
    curried = true
  }

  sem intrinsic : Name -> Const -> [JSExpr] -> JSExpr
  sem intrinsic runtime const =
  | args ->
    -- Get the name of the intrinsic function
    let name = getConstStringCode 0 const in
    intrinsicFromString runtime name args


  sem optimizedOpIntrinsic : Name -> Const -> [JSExpr] -> ([JSExpr] -> JSExpr) -> JSExpr
  sem optimizedOpIntrinsic runtime const args =
  | opFun ->
    -- Check if the arguments is fully applied (have the same length as constArity(const))
    -- If so, then optimize the intrinsic and return an in-place operation
    -- Otherwise, return a partially applied intrinsic
    if eqi (length args) (constArity const) then opFun args
    else intrinsic runtime const args


  sem optimizedIntrinsic : Name -> Const -> [JSExpr] -> ([JSExpr] -> JSExpr) -> JSExpr
  sem optimizedIntrinsic runtime const args =
  | opFun ->
    -- Check if the arguments is fully applied (have the same length as constArity(const))
    -- If so, then optimize the intrinsic and return an in-place operation
    -- Otherwise, return a partially applied intrinsic
    if eqi (length args) (constArity const) then opFun args
    else intrinsic runtime const args

end

---------------------------------------------------
--- Namespaces for the exisitng runtime targets ---
---------------------------------------------------

let intrGenNS   = nameSym "MExpr_JS_Intrinsics"
let intrWebNS   = nameSym "MExpr_Web_JS_Intrinsics"
let intrNodeNS  = nameSym "MExpr_Node_JS_Intrinsics"

let jsIntrinsicsFile_generic  = "stdlib/javascript/intrinsics.js"
let jsIntrinsicsFile_web      = "stdlib/javascript/web/intrinsics.js"
let jsIntrinsicsFile_node     = "stdlib/javascript/node/intrinsics.js"

let intrinsicGen  = use CompileJSOptimizedIntrinsics in intrinsic intrGenNS
let intrinsicWeb  = use CompileJSOptimizedIntrinsics in intrinsic intrWebNS
let intrinsicNode = use CompileJSOptimizedIntrinsics in intrinsic intrNodeNS

let optimizedIntrinsicGen = use CompileJSOptimizedIntrinsics in optimizedIntrinsic intrGenNS
let optimizedIntrinsicWeb = use CompileJSOptimizedIntrinsics in optimizedIntrinsic intrWebNS
let optimizedIntrinsicNode  = use CompileJSOptimizedIntrinsics in optimizedIntrinsic intrNodeNS
