include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
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




-- Names used in the compiler for intrinsics
let _consoleLog = use JSExprAst in
  JSEMember { expr = JSEVar { id = nameSym "console" }, id = nameSym "log" }



-- Supported JS runtime targets
type CompileJSTargetPlatform = Int
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
    match (compileMExpr opts) prog with expr then
      -- Return final top level expressions
      JSPProg { imports = [], exprs = [expr] }
    else never



  ---------------
  -- OPERATORS --
  ---------------

  -- Can compile fully and partially applied intrinsicGen operators and optimize them
  -- depending on the number of arguments to either compile as in-place operations or
  -- as a partially applied curried intrinsicGen functions
  sem compileCOp (opts: CompileJSOptions) (args: [JSExpr]) =
  -- Binary operators
  | CAddi _ & t
  | CAddf _ & t -> optimizedOpIntrinsicGen t "add" args (_binOp (JSOAdd {}))
  | CSubi _ & t
  | CSubf _ & t -> optimizedOpIntrinsicGen t "sub" args (_binOp (JSOSub {}))
  | CMuli _ & t
  | CMulf _ & t -> optimizedOpIntrinsicGen t "mul" args (_binOp (JSOMul {}))
  | CDivi _ & t
  | CDivf _ & t -> optimizedOpIntrinsicGen t "div" args (_binOp (JSODiv {}))
  | CModi _ & t -> optimizedOpIntrinsicGen t "mod" args (_binOp (JSOMod {}))
  | CEqi  _ & t
  | CEqf  _ & t -> optimizedOpIntrinsicGen t "eq" args (_binOp (JSOEq {}))
  | CLti  _ & t
  | CLtf  _ & t -> optimizedOpIntrinsicGen t "lt" args (_binOp (JSOLt {}))
  | CGti  _ & t
  | CGtf  _ & t -> optimizedOpIntrinsicGen t "gt" args (_binOp (JSOGt {}))
  | CLeqi _ & t
  | CLeqf _ & t -> optimizedOpIntrinsicGen t "leq" args (_binOp (JSOLe {}))
  | CGeqi _ & t
  | CGeqf _ & t -> optimizedOpIntrinsicGen t "geq" args (_binOp (JSOGe {}))
  | CNeqi _ & t
  | CNeqf _ & t -> optimizedOpIntrinsicGen t "neq" args (_binOp (JSONeq {}))

  -- Unary operators
  | CNegf _ & t
  | CNegi _ & t -> optimizedOpIntrinsicGen t "neg" args (_unOp (JSONeg {}))

  -- Sequential operators (SeqOpAst)
  | CConcat _ -> intrinsicGen "concat" args
  | CCons _ -> intrinsicGen "cons" args
  | CFoldl _ -> intrinsicGen "foldl" args

  -- Convert operations
  | CChar2Int _ -> intrinsicGen "char2int" args
  | CInt2Char _ -> intrinsicGen "int2char" args

  -- Not directly mapped to JavaScript operators
  | CPrint _ ->
    match opts.targetPlatform with CompileJSTP_Node () then intrinsicNode "print" args
    else
      -- Warning about inconsistent behaviour
      printLn "Warning: CPrint might behave unexpectedly when targeting the web or generic JS";
      intrinsicGen "print" args


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
      else match fun with TmConst { val = val } then
        let args = map (compileMExpr opts) args in
        compileCOp opts args val

      else error "Unsupported application in compileMExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam { ident = arg, body = body } ->
    JSEFun { param = arg, body = (compileMExpr opts) body }

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr)
      then (sidToString sid, (compileMExpr opts) expr)
      else never in
    JSEObject { fields = map compileField fieldSeq }

  | TmSeq {tms = tms, ty = ty, info = info} & t ->
    -- Special handling of strings
    -- Check if sequence of characters, then concatenate them into a string
    if _isCharSeq tms then
      match (_charSeq2String tms) with Some str then JSEString { s = str }
      else infoErrorExit (infoTm t) "Non-literal strings currently unsupported."
    else
      -- infoErrorExit (infoTm t) "Non-literal strings currently unsupported."
      -- Else compile each expression in sequence and return a list
      let tms: [JSExpr] = map (compileMExpr opts) tms in
      JSEArray { exprs = tms, info = info }

  -- Literals
  | TmConst { val = val } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileCOp opts [] val with jsexpr then jsexpr -- SeqOpAst Consts are handled by the compile operator semantics
    else error "Unsupported literal"
  | TmRecordUpdate _ -> error "Record updates cannot be handled in compileMExpr."


  ----------------
  -- STATEMENTS --
  ----------------

  | TmLet { ident = id, body = expr, inexpr = e } ->
    -- Check if identifier is the ignore identifier (_, or [])
    -- If so, ignore the expression unless it is a function application
    match nameGetStr id with [] then
      match expr with TmApp { } then
        -- Inline the function call
        JSSSeq {
          stmts = [
            (compileMExpr opts) expr,
            (compileMExpr opts) e
          ]
        }
      else
        -- Ignore the expression
        (compileMExpr opts) e
    else
      -- Normal let binding
      JSSSeq {
        stmts = [
          JSSDef { id = id, expr = (compileMExpr opts) expr },
          (compileMExpr opts) e
        ]
      }

  | TmRecLets { bindings = bindings, inexpr = e } ->
  	let fst : RecLetBinding = head bindings in
	match fst with { ident = ident, body = body } then
      JSSSeq {
        stmts = [
          JSSDef { id = ident, expr = (compileMExpr opts) body },
          (compileMExpr opts) e
        ]
      }
    else error "ERROR: TmRecLets must have at least one binding."
  | TmType { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type declaration)
  | TmConApp _ -> error "Constructor application in compileMExpr."
  | TmConDef { inexpr = e } -> (compileMExpr opts) e -- no op (Skip type constructor definitions)
  | TmMatch {target = target, pat = pat, thn = thn, els = els } ->
    let target: JSExpr = (compileMExpr opts) target in
    let pat: JSExpr = compileBindingPattern target pat in
    let thn: JSStmt = (compileMExpr opts) thn in
    let els: JSStmt = (compileMExpr opts) els in
    JSSIf {
      cond = pat,
      thn = ensureBlockOrStmt thn,
      els = ensureBlockOrStmt els
    }
  | TmUtest _ -> error "Unit test expressions cannot be handled in compileMExpr."
  | TmExt _ -> error "External expressions cannot be handled in compileMExpr."

  -- Should not occur
  | TmNever _ -> error "Never term found in compileMExpr"

  sem ensureBlockOrStmt =
  | JSSSeq { stmts = stmts } ->
    JSSBlock { stmts = stmts }
  | stmt -> stmt

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
let javascriptCompile : CompileJSOptions -> Expr -> JSPProg =
  lam opts : CompileJSOptions.
  lam ast : Expr.
  use MExprJSCompile in
  compileProg opts ast



let javascriptCompileFile : CompileJSOptions -> Expr -> String -> Bool =
  lam opts : CompileJSOptions.
  lam ast : Expr.
  lam sourcePath: String.
  use JSProgPrettyPrint in
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  let jsprog = javascriptCompile opts ast in   -- Run JS compiler
  let source = printJSProg jsprog in      -- Pretty print
  writeFile targetPath source;
  true
