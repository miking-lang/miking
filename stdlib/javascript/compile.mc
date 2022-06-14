include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"
include "javascript/intrinsics.mc"
include "javascript/operators.mc"

include "sys.mc"
include "common.mc"
include "seq.mc"


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

lang MExprJSCompile = JSProgAst + PatJSCompile + MExprAst

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



  -- Helper functions
  sem flattenBlockHelper : JSExpr -> ([JSExpr], JSExpr)
  sem flattenBlockHelper =
  | JSEBlock { exprs = exprs, ret = ret } ->
    -- If the return value is a block, concat the expressions in that block with the
    -- expressions in the current block and set the return value to the return value
    -- of the current block
    -- For each expression in the current block, if it is a block, flatten it
    let flatExprs : [JSExpr] = filterNops (foldr (
      lam e. lam acc.
        let flatE = flattenBlockHelper e in
        match flatE with ([], e) then
          cons e acc
        else match flatE with (flatEExprs, flatERet) then
          join [acc, flatEExprs, [flatERet]]
        else never
    ) [] exprs) in

    -- Call flattenBlockHelper recursively on the return value
    let flatRet = flattenBlockHelper ret in
    match flatRet with ([], e) then
      -- Normal expressions are returned as is, thus concat them with the expressions
      -- in the current block
      (flatExprs, ret)
    else match flatRet with (retExprs, retRet) then
      (concat flatExprs retExprs, retRet)
    else never
  | expr -> ([], expr)

  sem flattenBlock : JSExpr -> JSExpr
  sem flattenBlock =
  | JSEBlock _ & block ->
    match flattenBlockHelper block with (exprs, ret) then
      JSEBlock { exprs = exprs, ret = ret }
    else never
  | expr -> expr

  sem immediatelyInvokeBlock : JSExpr -> JSExpr
  sem immediatelyInvokeBlock =
  | JSEBlock _ & block -> JSEIIFE { body = block }
  | expr -> expr

  sem filterNops : [JSExpr] -> [JSExpr]
  sem filterNops =
  | lst -> foldr (
    lam e. lam acc.
      match e with JSENop { } then acc else cons e acc
  ) [] lst



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


  -----------------
  -- EXPRESSIONS --
  -----------------

  sem compileMExpr (opts: CompileJSOptions) =

  | TmVar { ident = id } -> JSEVar { id = id }

  | TmApp _ & app ->
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

      else error "Unsupported application in compileMExpr"
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
    else error "Unsupported literal"
  | TmRecordUpdate _ -> error "Record updates cannot be handled in compileMExpr."


  ----------------
  -- STATEMENTS --
  ----------------

  | TmLet { ident = id, body = expr, inexpr = e } ->
    -- Check if identifier is the ignore identifier (_, or [])
    -- If so, ignore the expression unless it is a function application
    let data = (match nameGetStr id with [] then
      match expr with TmApp { } then -- Inline the function call
        ([(compileMExpr opts) expr], (compileMExpr opts) e)
      else -- Ignore the expression
        ([], (compileMExpr opts) e)
    else -- Normal let binding
      ([JSEDef { id = id, expr = (compileMExpr opts) expr }], (compileMExpr opts) e)
    ) in
    match data with (exprs, ret) then
      flattenBlock (JSEBlock {
        exprs = exprs,
        ret = ret
      })
    else never

  | TmRecLets { bindings = bindings, inexpr = e, ty = ty } ->
    flattenBlock (JSEBlock {
      exprs = map (
        lam bind : RecLetBinding.
        match bind with { ident = ident, body = body, tyBody = tyBody, info = info } then
          let nop = TmNever { ty = tyBody, info = info } in
          compileMExpr opts (TmLet { ident = ident, body = body, inexpr = nop, ty = ty, tyBody = tyBody, info = info })
        else never
        ) bindings,
      ret = (compileMExpr opts) e
    })
  | TmType { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type declaration)
  | TmConApp _ -> error "Constructor application in compileMExpr."
  | TmConDef { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type constructor definitions)
  | TmMatch {target = target, pat = pat, thn = thn, els = els } ->
    let target: JSExpr = (compileMExpr opts) target in
    let pat: JSExpr = compileBindingPattern target pat in
    let thn = (compileMExpr opts) thn in
    let els = (compileMExpr opts) els in
    JSETernary {
      cond = pat,
      thn = immediatelyInvokeBlock thn,
      els = immediatelyInvokeBlock els
    }
  | TmUtest _ -> error "Unit test expressions cannot be handled in compileMExpr."
  | TmExt _ -> error "External expressions cannot be handled in compileMExpr."

  -- No-op
  | TmNever _ -> JSENop { }
  -- Should not occur
  -- | TmNever _ -> error "Never term found in compileMExpr"



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
