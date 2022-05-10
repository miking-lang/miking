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
let _consoleLog = use JSAst in
  JSEMember { expr = JSEVar { id = nameSym "console" }, id = nameSym "log" }


-------------------------------------------
-- MEXPR -> JavaScript COMPILER FRAGMENT --
-------------------------------------------

lang MExprJSCompile = MExprAst + JSProgAst

  -- Entry point
  sem compile =
  | prog ->
    -- Run compiler
    match compileExpr prog with expr then
      -- Return final top level expressions
      JSPProg { imports = [], exprs = [expr] }
    else never



  ---------------
  -- OPERATORS --
  ---------------

  -- Only a subset of constants can be compiled
  sem compileOp (t: Expr) (args: [JSExpr]) =

  -- Binary operators
  | CAddi _
  | CAddf _ -> JSEBinOp { op = JSOAdd {}, lhs = head args, rhs = last args }
  | CSubi _
  | CSubf _ -> JSEBinOp { op = JSOSub {}, lhs = head args, rhs = last args }
  | CMuli _
  | CMulf _ -> JSEBinOp { op = JSOMul {}, lhs = head args, rhs = last args }
  | CDivf _ -> JSEBinOp { op = JSODiv {}, lhs = head args, rhs = last args }
  | CEqi _
  | CEqf _  -> JSEBinOp { op = JSOEq {},  lhs = head args, rhs = last args }
  | CLti _
  | CLtf _  -> JSEBinOp { op = JSOLt {},  lhs = head args, rhs = last args }
  | CGti _
  | CGtf _  -> JSEBinOp { op = JSOGt {},  lhs = head args, rhs = last args }
  | CLeqi _
  | CLeqf _ -> JSEBinOp { op = JSOLe {},  lhs = head args, rhs = last args }
  | CGeqi _
  | CGeqf _ -> JSEBinOp { op = JSOGe {},  lhs = head args, rhs = last args }
  | CNeqi _
  | CNeqf _ -> JSEBinOp { op = JSONeq {}, lhs = head args, rhs = last args }

  -- Unary operators
  | CNegf _
  | CNegi _ -> JSEUnOp { op = JSONeg {}, rhs = head args }

  -- Not directly mapped to JavaScript operators
  | CPrint _ ->
    JSEApp { fun = _consoleLog, args = args }


  -----------------
  -- EXPRESSIONS --
  -----------------

  sem compileExpr =

  | TmVar { ty = ty, ident = ident } & t->
    error "Not implemented"

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
        JSEApp { fun = JSEVar { id = ident }, args = map compileExpr args }

      -- Intrinsics
      else match fun with TmConst { val = val } then
        let args = map compileExpr args in
        compileOp fun args val

      else error "Unsupported application in compileExpr"
    else never

  -- Anonymous function, not allowed.
  | TmLam { ident = id, body = body } -> JSEFun { param = id, body = body } -- error "Anonymous function in compileExpr."

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    if mapIsEmpty bindings then JSEInt { i = 0 }
    else error "ERROR: Records cannot be handled in compileExpr."

  | TmSeq {tms = tms, ty = ty, info = info} & t ->
    -- Special handling of strings
    -- Check if sequence of characters, then concatenate them into a string
    if _isCharSeq tms then
      match (_charSeq2String tms) with Some str then JSEString { s = str }
      else infoErrorExit (infoTm t) "Non-literal strings currently unsupported."
    else
      -- infoErrorExit (infoTm t) "Non-literal strings currently unsupported."
      -- Else compile each expression in sequence and return a list
      let tms: [JSExpr] = map compileExpr tms in
      JSESeq { exprs = tms, info = info }

  | TmRecordUpdate _ -> error "Record updates cannot be handled in compileExpr."
  | TmConApp _ -> error "Constructor application in compileExpr."
  | TmLet _ -> error "Let expressions cannot be handled in compileExpr."
  | TmRecLets _ -> error "Recursive let expressions cannot be handled in compileExpr."
  | TmType _ -> error "Type expressions cannot be handled in compileExpr."
  | TmConDef _ -> error "Constructor definitions cannot be handled in compileExpr."
  | TmMatch _ -> error "Match expressions cannot be handled in compileExpr."
  | TmUtest _ -> error "Unit test expressions cannot be handled in compileExpr."
  | TmExt _ -> error "External expressions cannot be handled in compileExpr."

  -- Literals
  | TmConst { val = val } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else error "Unsupported literal"

  -- Should not occur
  | TmNever _ -> error "Never term found in compileExpr"

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
  compile ast



let javascriptCompileFile : Expr -> String -> Bool =
  lam ast : Expr. lam sourcePath: String.
  use JSProgPrettyPrint in
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  let jsprog = javascriptCompile ast in   -- Run JS compiler
  let source = printJSProg jsprog in      -- Pretty print
  writeFile targetPath source;
  true
