include "mexpr/ast.mc"
include "mexpr/const-arity.mc"
include "javascript/ast.mc"

-- Fragments used by the intrinsic functions
lang CompileJSOptimizedIntrinsics = JSExprAst + MExprAst + MExprArity
end

-- Compile intrinsic function template (MExpr_JS_Intrinsics.[name])
let intrinsic : String -> [JSExpr] -> JSExpr =
  use CompileJSOptimizedIntrinsics in
  lam name. lam args.
    -- If there is at least one argument, apply the intrinsic function
    -- to the arguments.
    if gti (length args) 0 then
      JSEApp {
        fun = JSEMember {
          expr = JSEVar { name = "MExpr_JS_Intrinsics" },
          id = nameSym name
        },
        args = args,
        curried = true
      }
    else -- No arguments, return the function itself
      JSEMember {
        expr = JSEVar { name = "MExpr_JS_Intrinsics" },
        id = nameSym name
      }

let optimizedIntrinsic : Const -> String -> [JSExpr] -> ([JSExpr] -> JSEBinOp) -> JSExpr =
  use CompileJSOptimizedIntrinsics in
  lam const. lam name. lam args. lam opFun.
    -- Check if the arguments is fully applied (have the same length as constArity(const))
    -- If so, then optimize the intrinsic and return an in-place operation
    -- Otherwise, return a partially applied intrinsic
    if eqi (length args) (constArity const) then opFun args
    else _intrinsic name args
