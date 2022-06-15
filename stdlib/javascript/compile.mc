include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"
include "javascript/operators.mc"
include "javascript/intrinsics.mc"
include "javascript/optimizations.mc"

include "sys.mc"
include "common.mc"
include "seq.mc"
include "error.mc"


----------------------
-- HELPER FUNCTIONS --
----------------------

-- Check for unit type
let _isUnitTy = use RecordTypeAst in lam ty.
  match ty with TyRecord { fields = fields } then mapIsEmpty fields
  else false

let _isCharSeq = use MExprAst in lam tms.
    forAll (
      lam c : Expr.
        match c with TmConst { val = CChar _ } then true
        else false
    ) tms

-- First, always check if the terms are characters using _isCharSeq
let _charSeq2String = use MExprAst in lam tms.
    let toChar = lam expr.
      match expr with TmConst { val = CChar { val = val } } then Some val
      else None ()
    in
    optionMapM toChar tms -- String is a list of characters

-- TODO: Extract shared helper functions into a separate files


-- Empty compile JS environment
let compileJSEnvEmpty = { externals = mapEmpty nameCmp, allocs = [] }



-- Supported JS runtime targets
type CompileJSTargetPlatform
con CompileJSTP_Normal : () -> CompileJSTargetPlatform
con CompileJSTP_Web    : () -> CompileJSTargetPlatform
con CompileJSTP_Node   : () -> CompileJSTargetPlatform

-- JS Compiler options
type CompileJSOptions = {
  targetPlatform : CompileJSTargetPlatform,
  debugMode : Bool
}



-------------------------------------------
-- MEXPR -> JavaScript COMPILER FRAGMENT --
-------------------------------------------

lang MExprJSCompile = JSProgAst + PatJSCompile + MExprAst + JSOptimizeBlocks + JSOptimizeTailCalls + JSOptimizePatterns

  -- Entry point
  sem compileProg (opts: CompileJSOptions) =
  | prog ->
    -- Run compiler
    match compileMExpr opts prog with expr then
      let exprs = match expr with JSEBlock { exprs = exprs, ret = ret }
        then concat exprs [ret]
        else [expr] in
      -- Return final top level expressions
      JSPProg { imports = [], exprs = exprs }
    else never




  ---------------
  -- OPERATORS --
  ---------------

  -- Can compile fully and partially applied intrinsicGen operators and optimize them
  -- depending on the number of arguments to either compile as in-place operations or
  -- as a partially applied curried intrinsicGen functions
  sem compileJSOp (info: Info) (opts: CompileJSOptions) (args: [JSExpr]) =
  -- Binary operators
  | CAddi _ & t
  | CAddf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOAdd {}))
  | CSubi _ & t
  | CSubf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOSub {}))
  | CMuli _ & t
  | CMulf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOMul {}))
  | CDivi _ & t
  | CDivf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSODiv {}))
  | CModi _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOMod {}))
  | CEqi  _ & t
  | CEqf  _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOEq {}))
  | CLti  _ & t
  | CLtf  _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOLt {}))
  | CGti  _ & t
  | CGtf  _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOGt {}))
  | CLeqi _ & t
  | CLeqf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOLe {}))
  | CGeqi _ & t
  | CGeqf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSOGe {}))
  | CNeqi _ & t
  | CNeqf _ & t -> optimizedOpIntrinsicGen t args (_binOp (JSONeq {}))

  -- Unary operators
  | CNegf _ & t
  | CNegi _ & t -> optimizedOpIntrinsicGen t args (_unOp (JSONeg {}))

  -- Sequential operators (SeqOpAst)
  | CConcat _ & t -> intrinsicGen t args
  | CCons _   & t -> intrinsicGen t args
  | CFoldl _  & t -> intrinsicGen t args

  -- Convert operations
  | CChar2Int _ & t -> intrinsicGen t args
  | CInt2Char _ & t -> intrinsicGen t args

  -- References
  | CRef _    & t -> intrinsicGen t args
  | CModRef _ & t -> intrinsicGen t args
  | CDeRef _  & t -> intrinsicGen t args

  -- Not directly mapped to JavaScript operators
  | CPrint _ & t ->
    match opts.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else
      -- Warning about inconsistent behaviour
      printLn (concat
        (info2str info)
        "WARNING: 'print' might have unexpected behaviour when targeting the web or a generic JS runtime"
      );
      intrinsicGen t args
  | CFlushStdout _ -> JSENop { }
  | _ -> errorSingle [info] "Unsupported literal when compiling to JavaScript"


  -----------------
  -- EXPRESSIONS --
  -----------------

  sem compileMExpr (opts: CompileJSOptions) =

  | TmVar { ident = id } -> JSEVar { id = id }

  | TmApp { info = info } & app ->
    recursive let rec: [Expr] -> Expr -> (Expr, [Expr]) = lam acc. lam t.
      match t with TmApp { lhs = lhs, rhs = rhs } then
        if _isUnitTy (tyTm rhs) then rec acc lhs
        else rec (cons rhs acc) lhs
      else (t, acc)
    in
    match rec [] app with (fun, args) then
      -- Function calls
      match fun with TmVar { ident = ident } then
        JSEApp { fun = JSEVar { id = ident }, args = map (compileMExpr opts) args, curried = true }

      -- Intrinsics
      else match fun with TmConst { val = val, info = info } then
        let args = map (compileMExpr opts) args in
        compileJSOp info opts args val

      else errorSingle [info] "Unsupported application in compileMExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam { ident = arg, body = body } ->
    let body = (compileMExpr opts) body in
    JSEFun { param = arg, body = body }

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr)
      then (sidToString sid, (compileMExpr opts) expr)
      else never in
    JSEObject { fields = map compileField fieldSeq }

  | TmSeq {tms = tms} ->
    -- Check if sequence of characters, then concatenate them into a string
    if _isCharSeq tms then
      match (_charSeq2String tms) with Some str then JSEString { s = str }
      else never
    else
      JSEArray { exprs = map (compileMExpr opts) tms }

  -- Literals
  | TmConst { val = val, info = info } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileJSOp info opts [] val with jsexpr then jsexpr -- SeqOpAst Consts are handled by the compile operator semantics
    else never
  | TmRecordUpdate { info = info } -> errorSingle [info] "Record updates cannot be handled in compileMExpr."


  ----------------
  -- STATEMENTS --
  ----------------

  | TmLet { ident = ident, body = body, inexpr = e } ->
    match body with TmLam _ then
      flattenBlock (JSEBlock {
        exprs = [compileFun ident opts false body],
        ret = compileMExpr opts e
      })
    else match nameGetStr ident with [] then
      match body with TmApp _ then
        -- If identifier is the ignore identifier (_, or [])
        -- Then inline the function call
        flattenBlock (JSEBlock {
          exprs = [compileMExpr opts body],
          ret = compileMExpr opts e
        })
      else JSENop { } -- Ignore the expression
    else flattenBlock (JSEBlock {
      exprs = [JSEDef { id = ident, expr = compileMExpr opts body }],
      ret = compileMExpr opts e
    })

  | TmRecLets { bindings = bindings, inexpr = e, ty = ty } ->
    let compileBind = lam bind : RecLetBinding.
      match bind with { ident = ident, body = body, info = info } then
        compileFun ident opts true body
      else never in
    flattenBlock (JSEBlock {
      exprs = map compileBind bindings,
      ret = compileMExpr opts e
    })

  | TmType { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type declaration)
  | TmConApp { info = info } -> errorSingle [info] "Constructor application in compileMExpr."
  | TmConDef { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type constructor definitions)
  | TmMatch {target = target, pat = pat, thn = thn, els = els } ->
    let target: JSExpr = (compileMExpr opts) target in
    let pat: JSExpr = optimizePattern (compileBindingPattern target pat) in
    let thn = (compileMExpr opts) thn in
    let els = (compileMExpr opts) els in
    JSETernary {
      cond = pat,
      thn = immediatelyInvokeBlock thn,
      els = immediatelyInvokeBlock els
    }
  | TmUtest { info = info } -> errorSingle [info] "Unit test expressions cannot be handled in compileMExpr."
  | TmExt { info = info } -> errorSingle [info] "External expressions cannot be handled in compileMExpr."
  | TmNever _ -> JSENop { }

  sem compileFun (name: Name) (opts: CompileJSOptions) (optimize: Bool) =
  | TmLam _ & fun ->
    let optz = lam e. if optimize then optimizeTailCall e else e in
    JSEDef { id = name, expr = optz (compileMExpr opts fun) }
  | t -> errorSingle [infoTm t] "Non-lambda supplied to JavaScript compileFun"


end





-- Helper functions
let filepathWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

let defaultCompileJSOptions : CompileJSOptions = {
  targetPlatform = CompileJSTP_Normal (),
  debugMode = false
}

-- Compile a Miking AST to a JavaScript program AST.
-- Walk the AST and convert it to a JavaScript AST.
let javascriptCompile : CompileJSOptions -> Expr -> JSProg =
  lam opts : CompileJSOptions.
  lam ast : Expr.
  use MExprJSCompile in
  compileProg opts ast



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
