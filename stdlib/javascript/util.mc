
include "map.mc"
include "option.mc"
include "name.mc"
include "set.mc"

include "mexpr/ast.mc"
include "javascript/ast.mc"


--------------------
-- COMPILER TYPES --
--------------------

-- Supported JS runtime targets
type CompileJSTargetPlatform
con CompileJSTP_Generic : () -> CompileJSTargetPlatform
con CompileJSTP_Node    : () -> CompileJSTargetPlatform
con CompileJSTP_Bun     : () -> CompileJSTargetPlatform
con CompileJSTP_Web     : () -> CompileJSTargetPlatform

-- JS Compiler options
type CompileJSOptions = {
  targetPlatform : CompileJSTargetPlatform,
  debugMode : Bool,
  generalOptimizations : Bool,
  tailCallOptimizations: Bool
}

type RecursiveFunctionRegistry = {
  map: Map Name Name,
  suffix: String
}

type CompileJSContext = {
  options : CompileJSOptions,
  currentFunction: Option (Name, Info),
  recursiveFunctions: RecursiveFunctionRegistry,
  declarations: Set Name -- Block-scoped identifiers that need to be declared/defined
}


--------------------------
-- TCO HELPER FUNCTIONS --
--------------------------

-- Functions to keep track of recursive function names
-- and update the registry with new names if they not found.
-- * The key in the registry is the original function name.
-- * The value is the recursive variant of the function name (_rec$ suffix).

let emptyRFR = lam suffix. {
  map = mapEmpty nameCmp,
  suffix = suffix
}

let setRFR : Name -> RecursiveFunctionRegistry -> RecursiveFunctionRegistry =
  lam name. lam rfr : RecursiveFunctionRegistry.
    let str = nameGetStr name in
    let newName = concat str (rfr.suffix) in
    let recName = nameSym newName in
    { rfr with map = mapInsert name recName rfr.map }

let getRFR : Name -> RecursiveFunctionRegistry -> Option Name =
  lam name. lam rfr : RecursiveFunctionRegistry.
  mapLookup name rfr.map

recursive let extractRFR : use Ast in RecursiveFunctionRegistry -> Expr -> RecursiveFunctionRegistry =
  use MExprAst in
  lam rfr : RecursiveFunctionRegistry. lam e.
  match e with TmRecLets t then
    let rfr = foldl (lam rfr: RecursiveFunctionRegistry. lam b: RecLetBinding.
      match b with { ident = ident, body = body } in
      match body with TmLam _ then (setRFR ident rfr) else rfr
    ) rfr t.bindings in
    extractRFR rfr t.inexpr
  else sfold_Expr_Expr extractRFR rfr e
end

let extractRFRctx : use Ast in CompileJSContext -> Expr -> CompileJSContext =
  lam ctx : CompileJSContext. lam e.
  { ctx with recursiveFunctions = extractRFR ctx.recursiveFunctions e }

--------------------------
-- VARIABLE DECLARATION --
--------------------------

let compileDeclarations : use JSExprAst in CompileJSContext -> (CompileJSContext, JSExpr) =
  use JSExprAst in
  lam ctx : CompileJSContext.
  if setIsEmpty (ctx.declarations) then (ctx, JSENop {})
  else
    let ctx2 = { ctx with declarations = setEmpty nameCmp } in
    (ctx2, JSEDec { ids = setToSeq ctx.declarations })

let combineDeclarations : CompileJSContext -> CompileJSContext -> CompileJSContext =
  lam ctx : CompileJSContext. lam ctx2 : CompileJSContext.
  { ctx with declarations = setUnion ctx.declarations ctx2.declarations }

------------------------
-- COMPILER FUNCTIONS --
------------------------

-- Check for unit type
let _isUnitTy: use Ast in Type -> Bool = use RecordTypeAst in lam ty: Type.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields else false

let _isCharSeq: use Ast in [Expr] -> Bool = use MExprAst in lam tms: [Expr].
  if null tms then false -- Empty list is not a char sequence
  else forAll (
    lam c : Expr.
      match c with TmConst { val = CChar _ } then true else false
  ) tms

-- First, always check if the terms are characters using _isCharSeq
let _charSeq2String: use Ast in [Expr] -> String = use MExprAst in lam tms: [Expr].
  let toChar = lam expr.
    match expr with TmConst { val = CChar { val = val } } in val
  in map toChar tms -- String is a list of characters

let _isCharPatSeq: use Ast in [Pat] -> Bool = use MExprAst in lam pats: [Pat].
  if null pats then false -- Empty list is not a char sequence
  else forAll (
    lam c : Pat.
      match c with PatChar _ then true else false
  ) pats

-- First, always check if the terms are characters using _isCharPatSeq
let _charPatSeq2String: use Ast in [Pat] -> String = use MExprAst in lam pats: [Pat].
  let toChar = lam pat.
    match pat with PatChar { val = val } in val
  in map toChar pats -- String is a list of characters


-------------------------------
-- OPERATOR HELPER FUNCTIONS --
-------------------------------

let _binOp : use JSExprAst in JSBinOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args. JSEBinOp { op = op, lhs = head args, rhs = last args }

let _unOp : use JSExprAst in JSUnOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args. JSEUnOp { op = op, rhs = head args }

let _assign : use JSExprAst in JSExpr -> JSExpr -> JSExpr = use JSExprAst in
  lam lhs. lam rhs. JSEBinOp { op  = JSOAssign {}, lhs = lhs, rhs = rhs }

-- Multi binary operator folding into nested binary operators.
-- Assume length of args is 2 or more.
let _binOpM : use JSExprAst in JSBinOp -> [JSExpr] -> JSExpr = use JSExprAst in
  lam op. lam args.
  recursive let f = (lam args : [JSExpr]. lam acc : JSExpr.
    if null args then acc
    else f (tail args) (_binOp op [acc, head args])
  ) in
  f (tail args) (head args)


----------------------------------
-- EMPTY COMPILER TYPE DEFAULTS --
----------------------------------


let compileJSOptionsEmpty : CompileJSOptions = {
  targetPlatform = CompileJSTP_Generic (),
  debugMode = false,
  generalOptimizations = true,
  tailCallOptimizations = true
}

-- Empty compile JS environment
let compileJSCtxEmpty : CompileJSContext = {
  options = compileJSOptionsEmpty,
  currentFunction = None (),
  recursiveFunctions = emptyRFR "_rec$",
  declarations = setEmpty nameCmp
}
