include "mexpr/ast.mc"
include "mexpr/pprint.mc"
include "mexpr/const-arity.mc"
include "javascript/ast.mc"
include "stdlib.mc"


-- Fragments used by the intrinsic functions
lang JSIntrinsic = JSExprAst + MExprAst + MExprArity + MExprPrettyPrint

  -- Compile intrinsic function withing the given runtime environment,
  -- identifier name and arguments.
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

  -- Intrinsic directly from a constant literal
  sem intrinsic : Name -> Const -> [JSExpr] -> JSExpr
  sem intrinsic runtime const =
  | args -> intrinsicFromString runtime (getConstStringCode 0 const) args

  -- Intrinsic with custom name
  sem optimizedIntrinsicWithString : Name -> Const -> String -> [JSExpr] -> ([JSExpr] -> JSExpr) -> JSExpr
  sem optimizedIntrinsicWithString runtime const str args =
  | opFun ->
    -- Check if the arguments is fully applied (have the same length as constArity(const))
    -- If so, then optimize the intrinsic and return an in-place operation
    -- Otherwise, return a partially applied intrinsic
    if eqi (length args) (constArity const) then opFun args
    else intrinsicFromString runtime str args

  -- Intrinsic with same name as the const literal
  sem optimizedIntrinsic : Name -> Const -> [JSExpr] -> ([JSExpr] -> JSExpr) -> JSExpr
  sem optimizedIntrinsic runtime const args =
  | opFun -> optimizedIntrinsicWithString runtime const (getConstStringCode 0 const) args opFun

end

---------------------------------------------------
--- Namespaces for the exisitng runtime targets ---
---------------------------------------------------

let intrGenNS   = nameSym "MExpr_JS_Intrinsics"
let intrWebNS   = nameSym "MExpr_Web_JS_Intrinsics"
let intrNodeNS  = nameSym "MExpr_Node_JS_Intrinsics"
let intrBunNS   = nameSym "MExpr_Bun_JS_Intrinsics"

let jsIntrinsicsFile_generic  = concat stdlibLoc "/javascript/generic/intrinsics.js"
let jsIntrinsicsFile_web      = concat stdlibLoc "/javascript/web/intrinsics.js"
let jsIntrinsicsFile_node     = concat stdlibLoc "/javascript/node/intrinsics.js"
let jsIntrinsicsFile_bun      = concat stdlibLoc "/javascript/bun/intrinsics.js"

let intrinsicGen  = use JSIntrinsic in intrinsic intrGenNS
let intrinsicWeb  = use JSIntrinsic in intrinsic intrWebNS
let intrinsicNode = use JSIntrinsic in intrinsic intrNodeNS
let intrinsicBun = use JSIntrinsic in intrinsic intrBunNS

let optimizedIntrinsicGen   = use JSIntrinsic in optimizedIntrinsic intrGenNS
let optimizedIntrinsicWeb   = use JSIntrinsic in optimizedIntrinsic intrWebNS
let optimizedIntrinsicNode  = use JSIntrinsic in optimizedIntrinsic intrNodeNS
let optimizedIntrinsicBun   = use JSIntrinsic in optimizedIntrinsic intrBunNS

let optimizedIntrinsicGenStr  = use JSIntrinsic in optimizedIntrinsicWithString intrGenNS
let optimizedIntrinsicWebStr  = use JSIntrinsic in optimizedIntrinsicWithString intrWebNS
let optimizedIntrinsicNodeStr = use JSIntrinsic in optimizedIntrinsicWithString intrNodeNS
let optimizedIntrinsicBunStr  = use JSIntrinsic in optimizedIntrinsicWithString intrBunNS


let intrinsicStrGen  = use JSIntrinsic in intrinsicFromString intrGenNS
let intrinsicStrWeb  = use JSIntrinsic in intrinsicFromString intrWebNS
let intrinsicStrNode = use JSIntrinsic in intrinsicFromString intrNodeNS
let intrinsicStrBun  = use JSIntrinsic in intrinsicFromString intrBunNS

let externalRefGen  = use JSIntrinsic in lam n. intrinsicStrGen  n []
let externalRefWeb  = use JSIntrinsic in lam n. intrinsicStrWeb  n []
let externalRefNode = use JSIntrinsic in lam n. intrinsicStrNode n []
let externalRefBun  = use JSIntrinsic in lam n. intrinsicStrBun  n []
