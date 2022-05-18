include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/pprint.mc"

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

------------------------------------
-- Pattern -> JavaScript FRAGMENT --
------------------------------------

lang PatJSCompile = JSProgAst + NamedPat + SeqTotPat + SeqEdgePat +
                    RecordPat + DataPat + IntPat + OrPat +
                    CharPat + BoolPat + AndPat + NotPat
  sem compilePat (target: JSExpr) =
  | PatNamed { ident = ident } ->
	dprint "Entered PatNamed";
    match ident with PName name then
		JSEBinOp {
        op  = JSOAssign {},
        lhs = JSEVar { id = name },
        rhs = target
      }
    else -- Whildcard pattern
      JSEBool { b = true }
  | PatInt { val = val } ->
    JSEBinOp {
      op = JSOEq {},
      lhs = JSEInt { i = val },
      rhs = target
    }
  | PatRecord { bindings = bindings } ->
	let fieldSeq = mapToSeq bindings in
	let compileField = lam f. match f with (sid, expr)
		then
		dprint "Compiling field";
		dprint expr;
		(sidToString sid, compilePat expr)
		else never in
	JSPObject { fields = map compileField fieldSeq }

  | unsup ->
  	dprint unsup;
 	error "compilePat: Unsupported pattern"
end

-------------------------------------------
-- MEXPR -> JavaScript COMPILER FRAGMENT --
-------------------------------------------

lang MExprJSCompile = JSProgAst + MExprAst + PatJSCompile

  -- Entry point
  sem compileProg =
  | prog ->
    -- Run compiler
    match compileMExpr prog with expr then
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
  | CDivf _ -> JSEBinOp { op = JSODiv {}, lhs = head args, rhs = last args }
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

  -- Sequential operators (SeqOpAst)
  | CConcat _ -> JSEBinOp { op = JSOAdd {}, lhs = head args, rhs = last args }
  -- Unary operators
  | CNegf _
  | CNegi _ -> JSEUnOp { op = JSONeg {}, rhs = head args }

  -- Not directly mapped to JavaScript operators
  | CPrint _ ->
    JSEApp { fun = _consoleLog, args = args, curried = false }


  -----------------
  -- EXPRESSIONS --
  -----------------

  sem compileMExpr =

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
        JSEApp { fun = JSEVar { id = ident }, args = map compileMExpr args, curried = true }

      -- Intrinsics
      else match fun with TmConst { val = val } then
        let args = map compileMExpr args in
        compileCOp fun args val

      else error "Unsupported application in compileMExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam { ident = arg, body = body } ->
    JSEFun { param = arg, body = compileMExpr body }

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    let compileField = lam f. match f with (sid, expr)
      then (sidToString sid, compileMExpr expr)
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
      let tms: [JSExpr] = map compileMExpr tms in
      JSEArray { exprs = tms, info = info }

  -- Literals
  | TmConst { val = val } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileCOp val with jsexpr then jsexpr -- SeqOpAst Consts are handled in compileCOp
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
            compileMExpr expr,
            compileMExpr e
          ]
        }
      else
        -- Ignore the expression
        compileMExpr e
    else
      -- Normal let binding
      JSSSeq {
        stmts = [
          JSSDef { id = id, expr = compileMExpr expr },
          compileMExpr e
        ]
      }

  | TmRecLets { bindings = bindings, inexpr = e } ->
  	let fst : RecLetBinding = head bindings in
	match fst with { ident = ident, body = body } then
      JSSSeq {
        stmts = [
          JSSDef { id = ident, expr = compileMExpr body },
          compileMExpr e
        ]
      }
    else error "ERROR: TmRecLets must have at least one binding."
  | TmType { inexpr = e } -> compileMExpr e -- no op (Skip type declaration)
  | TmConApp _ -> error "Constructor application in compileMExpr."
  | TmConDef { inexpr = e } -> compileMExpr e -- no op (Skip type constructor definitions)
  | TmMatch {target = target, pat = pat, thn = thn, els = els } ->
    let target: JSExpr = compileMExpr target in
    let pat: JSExpr = compilePat target pat in
    let thn: JSStmt = compileMExpr thn in
    let els: JSStmt = compileMExpr els in
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
  | (JSSBlock _) & block -> block
  | JSSSeq { stmts = stmts } & stmt ->
    JSSBlock { stmts = stmts }
  | stmt -> stmt
end





-- Helper functions
let filepathWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename



-- Compile a Miking AST to a JavaScript program AST.
-- Walk the AST and convert it to a JavaScript AST.
let javascriptCompile : Expr -> JSPProg =
  lam ast : Expr.
  use MExprJSCompile in
  compileProg ast



let javascriptCompileFile : Expr -> String -> Bool =
  lam ast : Expr. lam sourcePath: String.
  use JSProgPrettyPrint in
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  let jsprog = javascriptCompile ast in   -- Run JS compiler
  let source = printJSProg jsprog in      -- Pretty print
  writeFile targetPath source;
  true
