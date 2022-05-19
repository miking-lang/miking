include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"

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


-- Helper constructors for JSExpr operators
let _binOp : JSBinOp -> [JSExpr] -> JSEBinOp = use JSExprAst in
  lam op. lam args. JSEBinOp { op = op, lhs = head args, rhs = last args }

let _unOp : JSUnOp -> [JSExpr] -> JSEUnOp = use JSExprAst in
  lam op. lam args. JSEUnOp { op = op, rhs = head args }


-- Names used in the compiler for intrinsics
let _consoleLog = use JSExprAst in
  JSEMember { expr = JSEVar { id = nameSym "console" }, id = nameSym "log" }




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

  -- Only a subset of constants can be compiled
  sem compileCOp (t: Expr) (args: [JSExpr]) =

  -- Binary operators
  | CAddi _
  | CAddf _ -> JSEBinOp { op = JSOAdd {}, lhs = head args, rhs = last args }
  | CSubi _
  | CSubf _ -> JSEBinOp { op = JSOSub {}, lhs = head args, rhs = last args }
  | CMuli _
  | CMulf _ -> JSEBinOp { op = JSOMul {}, lhs = head args, rhs = last args }
  | CDivi _
  | CDivf _ -> JSEBinOp { op = JSODiv {}, lhs = head args, rhs = last args }
  | CModi _ -> JSEBinOp { op = JSOMod {}, lhs = head args, rhs = last args }
  | CEqi  _
  | CEqf  _ -> JSEBinOp { op = JSOEq {},  lhs = head args, rhs = last args }
  | CLti  _
  | CLtf  _ -> JSEBinOp { op = JSOLt {},  lhs = head args, rhs = last args }
  | CGti  _
  | CGtf  _ -> JSEBinOp { op = JSOGt {},  lhs = head args, rhs = last args }
  | CLeqi _
  | CLeqf _ -> JSEBinOp { op = JSOLe {},  lhs = head args, rhs = last args }
  | CGeqi _
  | CGeqf _ -> JSEBinOp { op = JSOGe {},  lhs = head args, rhs = last args }
  | CNeqi _
  | CNeqf _ -> JSEBinOp { op = JSONeq {}, lhs = head args, rhs = last args }

  -- Unary operators
  | CNegf _
  | CNegi _ -> JSEUnOp { op = JSONeg {}, rhs = head args }

  -- Sequential operators (SeqOpAst)
  | CConcat _ -> JSEBinOp { op = JSOAdd {}, lhs = head args, rhs = last args }
  | CCons _ -> -- Tuple -> JavaScript array/list
    JSEArray { elems = args }
  | CFoldl _ ->
    match args with [func, init, seq] then
      -- Compile a reduce function
      JSEApp {
        fun = JSEMember {
          expr = seq,
          id = nameSym "reduce"
        },
        args = [ func, init ]
      }
    else
      error "compile operator: Invalid arguments to foldl"

  -- Convert operations
  | CChar2Int _ -> JSEApp {
      fun = JSEMember {
        expr = head args,
        id = nameSym "charCodeAt"
      },
      args = [ JSEInt { i = 0 } ]
    }
  | CInt2Char _ -> JSEApp {
      fun = JSEMember {
        expr = JSEVar { id = nameSym "String" },
        id = nameSym "fromCharCode"
      },
      args = [ head args ]
    }

  -- Not directly mapped to JavaScript operators
  | CPrint _ ->
    JSEApp { fun = _consoleLog, args = args, curried = false }


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
        compileCOp args val

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
    else
      dprintLn "Trying to compile TmConst using compile C Op:";
      dprintLn val;
      match compileCOp [] val with jsexpr then jsexpr -- SeqOpAst Consts are handled by the compile operator semantics
    else
      error "Unsupported literal"
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

-- Supported JS Runtime Mode
type CompileJSTargetPlatform = Int
con CompileJSTP_Normal : () -> CompileJSTargetPlatform
con CompileJSTP_Web    : () -> CompileJSTargetPlatform
con CompileJSTP_Node   : () -> CompileJSTargetPlatform

type CompileJSOptions = {
  targetPlatform : CompileJSTargetPlatform,
  debugMode : Bool
}

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
