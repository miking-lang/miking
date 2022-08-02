include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"
include "javascript/util.mc"
include "javascript/intrinsics.mc"
include "javascript/optimizations.mc"

include "sys.mc"
include "common.mc"
include "seq.mc"
include "error.mc"
include "name.mc"
include "option.mc"
include "string.mc"




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
  trampolinedFunctions: Map Name JSExpr,
  currentFunction: Option (Name, Info)
}

-- Empty compile JS environment
let compileJSCtxEmpty = {
  options = compileJSOptionsEmpty,
  trampolinedFunctions = mapEmpty nameCmp,
  currentFunction = None ()
}


let isTrampolinedJs : CompileJSContext -> Name -> Bool =
  lam ctx. lam name.
  match mapLookup name ctx.trampolinedFunctions with Some _
  then true else false

let _lastSubStr : String -> Int -> Option String =
  lam str. lam n.
  if lti (length str) n then None ()
  else Some (subsequence str (subi (length str) n) (length str))

let isFuncInModule : CompileJSContext -> String -> String -> Bool =
  lam ctx. lam funcName. lam modulePath.
  match ctx.currentFunction with Some (name, info) then
    -- Check if the name and function name match
    if eqString funcName (nameGetStr name) then
      -- Check if the module path matches
      match info with Info { filename = filename } then
        match _lastSubStr filename (length modulePath) with Some endpath then
          if eqString modulePath endpath then true else false
        else false
      else false
    else false
  else false


-------------------------------------------
-- MEXPR -> JavaScript COMPILER FRAGMENT --
-------------------------------------------

lang MExprJSCompile = JSProgAst + PatJSCompile + MExprAst + MExprPrettyPrint +
                      JSOptimizeBlocks + JSOptimizeTailCalls +
                      JSOptimizeExprs + JSIntrinsic

  -- Entry point
  sem compileProg (ctx: CompileJSContext) =
  | prog ->
    -- Run compiler
    match compileMExpr ctx prog with expr in
    let exprs = match expr with JSEBlock { exprs = exprs, ret = ret }
      then concat exprs [ret]
      else [expr] in
    -- Return final top level expressions
    JSPProg { imports = [], exprs = exprs }




  ---------------
  -- OPERATORS --
  ---------------

  -- Can compile fully and partially applied intrinsicGen operators and optimize them
  -- depending on the number of arguments to either compile as in-place operations or
  -- as a partially applied curried intrinsicGen functions
  sem compileJSOp (info: Info) (ctx: CompileJSContext) (args: [JSExpr]) =
  -- Binary operators
  | CAddi _ & t
  | CAddf _ & t -> optimizedIntrinsicGenStr t "add" args (_binOp (JSOAdd {}))
  | CSubi _ & t
  | CSubf _ & t -> optimizedIntrinsicGenStr t "sub" args (_binOp (JSOSub {}))
  | CMuli _ & t
  | CMulf _ & t -> optimizedIntrinsicGenStr t "mul" args (_binOp (JSOMul {}))
  | CDivi _ & t
  | CDivf _ & t -> optimizedIntrinsicGenStr t "div" args (_binOp (JSODiv {}))
  | CModi _ & t -> optimizedIntrinsicGenStr t "mod" args (_binOp (JSOMod {}))
  | CEqc  _ & t
  | CEqi  _ & t
  | CEqf  _ & t -> optimizedIntrinsicGenStr t "eq" args (_binOp (JSOEq {}))
  | CLti  _ & t
  | CLtf  _ & t -> optimizedIntrinsicGenStr t "lt" args (_binOp (JSOLt {}))
  | CGti  _ & t
  | CGtf  _ & t -> optimizedIntrinsicGenStr t "gt" args (_binOp (JSOGt {}))
  | CLeqi _ & t
  | CLeqf _ & t -> optimizedIntrinsicGenStr t "le" args (_binOp (JSOLe {}))
  | CGeqi _ & t
  | CGeqf _ & t -> optimizedIntrinsicGenStr t "ge" args (_binOp (JSOGe {}))
  | CNeqi _ & t
  | CNeqf _ & t -> optimizedIntrinsicGenStr t "ne" args (_binOp (JSONeq {}))

  -- Unary operators
  | CNegf _ & t
  | CNegi _ & t -> optimizedIntrinsicGenStr t "neg" args (_unOp (JSONeg {}))

  -- Sequential operators (SeqOpAst)
  | CConcat _ & t -> intrinsicGen t args
  | CCons _   & t -> intrinsicGen t args
  | CFoldl _  & t -> intrinsicGen t args
  | CLength _ & t -> intrinsicGen t args
  | CHead _   & t -> intrinsicGen t args
  | CTail _   & t -> intrinsicGen t args
  | CNull _   & t -> intrinsicGen t args

  -- Convert operations
  | CChar2Int _ & t -> intrinsicGen t args
  | CInt2Char _ & t -> intrinsicGen t args

  -- References
  | CRef _    & t -> intrinsicGen t args
  | CModRef _ & t -> intrinsicGen t args
  | CDeRef _  & t -> intrinsicGen t args

  -- Not directly mapped to JavaScript operators
  | CPrint _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else -- Warning about inconsistent behaviour
      (if not (or (isFuncInModule ctx "printLn" "stdlib/common.mc")
              (or (isFuncInModule ctx "printLn" "internal")
                  (isFuncInModule ctx "utestTestPassed" "internal")))
      then printLn (concat (info2str info)
          "WARNING: 'print' might have unexpected behaviour when targeting the web or a generic JS runtime")
      else ());
        intrinsicGen t args
  | CDPrint _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else -- Warning about inconsistent behaviour
      if not (or (isFuncInModule ctx "dprintLn" "stdlib/common.mc") (isFuncInModule ctx "dprintLn" "internal")) then
        printLn (concat (info2str info)
          "WARNING: 'dprint' might have unexpected behaviour when targeting the web or a generic JS runtime");
          intrinsicGen t args
      else JSEReturn { expr = intrinsicGen t args } -- Ignores the last newline print call in dprintLn
  | CFlushStdout _ -> JSENop { }
  | CExit _ -> JSEString { s = "exit" } -- TODO: Fix this, inspiration: https://stackoverflow.com/questions/550574/how-to-terminate-the-script-in-javascript
  | t -> errorSingle [info] (join ["Unsupported literal '", getConstStringCode 0 t, "' when compiling to JavaScript"])


  -- Extract the name of the function and the arguments from
  -- a function application
  sem foldApp : [Expr] -> Expr -> (Expr, [Expr])
  sem foldApp acc =
  | TmApp { lhs = lhs, rhs = rhs } ->
    if _isUnitTy (tyTm rhs) then foldApp acc lhs
    else foldApp (cons rhs acc) lhs
  | t -> (t, acc)


  -----------------
  -- EXPRESSIONS --
  -----------------
  sem compileMExpr (ctx: CompileJSContext) =
  | TmVar { ident = id } -> JSEVar { id = id }
  | TmApp { info = info } & app ->
    match foldApp [] app with (fun, args) in
    -- Function calls
    let args = map (compileMExpr ctx) args in
    match fun with TmVar { ident = ident } then
      let jsApp = JSEApp {
        fun = JSEVar { id = ident },
        args = args,
        curried = true
      } in
      if isTrampolinedJs ctx ident then
        match mapLookup ident ctx.trampolinedFunctions with Some fun in
        wrapCallToOptimizedFunction info fun (length args) jsApp
      else jsApp
    -- Intrinsics
    else match fun with TmConst { val = val, info = info } then
      compileJSOp info ctx args val
    else errorSingle [infoTm app] "Unsupported application in compileMExpr"

  -- Anonymous function
  | TmLam { ident = arg, body = body } ->
    let body = (compileMExpr ctx) body in
    JSEFun { params = [arg], body = body }

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr) in
      (sidToString sid, (compileMExpr ctx) expr)
    in
    JSEObject { fields = map compileField fieldSeq }

  | TmSeq {tms = tms} ->
    -- Check if sequence of characters, then concatenate them into a string
    if _isCharSeq tms then
      match (_charSeq2String tms) with Some str in
      JSEString { s = str }
    else
      JSEArray { exprs = map (compileMExpr ctx) tms }

  -- Literals
  | TmConst { val = val, info = info } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileJSOp info ctx [] val with jsexpr in jsexpr -- SeqOpAst Consts are handled by the compile operator semantics
  | TmRecordUpdate _ & t -> errorSingle [infoTm t] "Record updates cannot be handled in compileMExpr."


  ----------------
  -- STATEMENTS --
  ----------------

  | TmLet { ident = ident, body = body, inexpr = e, info = info } ->
    match nameGetStr ident with [] then
      flattenBlock (JSEBlock {
        exprs = [compileMExpr ctx body],
        ret = compileMExpr ctx e
      })
    else
      let expr = (match body with TmLam _ then
        let ctx = { ctx with currentFunction = Some (ident, info) } in
        compileMExpr ctx body
      else compileMExpr ctx body) in
      flattenBlock (JSEBlock {
        exprs = [JSEDef { id = ident, expr = expr }],
        ret = compileMExpr ctx e
      })

  | TmRecLets { bindings = bindings, inexpr = e, ty = ty } ->
    let rctx = ref ctx in
    let compileBind = lam bind : RecLetBinding.
      match bind with { ident = ident, body = body, info = info } in
      match body with TmLam _ then
        let ctx = { ctx with currentFunction = Some (ident, info) } in
        let fun = compileMExpr ctx body in
        match optimizeTailCall ident info (deref rctx) fun with (ctx, fun) in
        modref rctx ctx;
        JSEDef { id = ident, expr = fun }
      else errorSingle [info] "Cannot handle non-lambda in recursive let when compiling to JavaScript"
    in
    let exprs = map compileBind bindings in
    flattenBlock (JSEBlock {
      exprs = exprs,
      ret = compileMExpr (deref rctx) e
    })

  | TmType { inexpr = e } -> (compileMExpr ctx) e -- no op (Skip type declaration)
  | TmConApp _ & t -> errorSingle [infoTm t] "Constructor application in compileMExpr."
  | TmConDef { inexpr = e } -> (compileMExpr ctx) e -- no op (Skip type constructor definitions)
  | TmMatch {target = target, pat = pat, thn = thn, els = els } ->
    let target = (compileMExpr ctx) target in
    let pat = compileBindingPattern target pat in
    let thn = (compileMExpr ctx) thn in
    let els = (compileMExpr ctx) els in
    let expr = JSETernary {
      cond = pat,
      thn = immediatelyInvokeBlock thn,
      els = immediatelyInvokeBlock els
    } in
    if ctx.options.optimizations then optimizeExpr3 expr else expr
  | TmUtest _ & t -> errorSingle [infoTm t] "Unit test expressions cannot be handled in compileMExpr"
  | TmExt _ & t -> errorSingle [infoTm t] "External expressions cannot be handled in compileMExpr"
  | TmNever _ -> JSENop { }

end





-- Helper functions
let filepathWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

-- Compile a Miking AST to a JavaScript program AST.
-- Walk the AST and convert it to a JavaScript AST.
let javascriptCompile : CompileJSOptions -> Expr -> JSProg =
  lam opts : CompileJSOptions. lam ast : Expr.
  use MExprJSCompile in
  let ctx = { compileJSCtxEmpty with options = opts } in
  compileProg ctx ast


let javascriptCompileFile : CompileJSOptions -> Expr -> String -> String =
  lam opts : CompileJSOptions.
  lam ast : Expr.
  lam sourcePath: String.
  use JSProgPrettyPrint in
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  let jsprog = javascriptCompile opts ast in   -- Run JS compiler
  let source = printJSProg jsprog in      -- Pretty print
  let intrinsics = join [readFile jsIntrinsicsFile_generic, (
    switch opts.targetPlatform
    case CompileJSTP_Web () then readFile jsIntrinsicsFile_web
    case CompileJSTP_Node () then readFile jsIntrinsicsFile_node
    case _ then "" end
  ), "\n"] in
  writeFile targetPath (concat intrinsics source);
  targetPath
