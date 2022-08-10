include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/utesttrans.mc"
include "mexpr/pprint.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/util.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"
include "javascript/intrinsics.mc"
include "javascript/optimizations.mc"

include "javascript/compile-ext-default.mc"

include "sys.mc"
include "common.mc"
include "seq.mc"
include "set.mc"
include "error.mc"
include "name.mc"
include "option.mc"
include "string.mc"



let _lastSubStr : String -> Int -> Option String =
  lam str. lam n.
  if lti (length str) n then None ()
  else Some (subsequence str (subi (length str) n) (length str))

let isInModule : CompileJSContext -> String -> Bool =
  lam ctx. lam modulePath.
  match ctx.currentFunction with Some (_, info) then
    -- Check if the filename ends with the module path
    match info with Info { filename = filename } then
      match _lastSubStr filename (length modulePath) with Some endpath then
        eqString modulePath endpath
      else false
    else false
  else false

let isInFunc : CompileJSContext -> String -> Bool =
  lam ctx. lam funcName.
  match ctx.currentFunction with Some (name, _)
  then eqString funcName (nameGetStr name)
  else false

let isInModuleFunc : CompileJSContext -> String -> String -> Bool =
  lam ctx. lam funcName. lam modulePath.
  if isInModule ctx modulePath
  then isInFunc ctx funcName
  else false

let isInModuleFuncs : all a. CompileJSContext -> [(String, String)] -> Info -> (() -> a) -> (() -> a) -> a =
  lam ctx. lam funModules. lam info. lam onSuccess. lam onError.
  match info with NoInfo () then onSuccess () else
  if any (lam p. match p with (name, path) in isInModuleFunc ctx name path) funModules then onSuccess ()
  else onError ()

let infoWarn : Info -> String -> () =
    lam info. lam msg.
    printLn (join [(info2str info), "WARNING: ", msg])

-------------------------------------------
-- MEXPR -> JavaScript COMPILER FRAGMENT --
-------------------------------------------

lang MExprJSCompile = JSProgAst + PatJSCompile + MExprAst + MExprPrettyPrint +
                      JSOptimizeBlocks + JSOptimizeTailCalls +
                      JSOptimizeExprs + JSIntrinsic +
                      CompileJSDefaultExt

  -- Entry point
  sem compileProg : CompileJSContext -> Expr -> JSProg
  sem compileProg ctx =
  | prog ->
    let ctx = if ctx.options.optimizations then extractRFRctx ctx prog else ctx in
    -- Run compiler
    match compileMExpr ctx prog with expr in
    let exprs = match expr with JSEBlock { exprs = exprs, ret = ret }
      then concat exprs [ret]
      else [expr] in
    -- Return final top level expressions
    JSPProg { imports = [], exprs = exprs }

    -- Look ahead and extract a list of all recursive functions
    sem extractRecursiveFunctions : Set Name -> Expr -> Set Name
    sem extractRecursiveFunctions acc =
    | e ->
      match e with TmRecLets t then
        let acc = foldl (lam acc: Set Name. lam b: RecLetBinding.
          match b with { ident = ident, body = body } in
          match body with TmLam _ then (setInsert ident acc) else acc
        ) acc t.bindings in
        extractRecursiveFunctions acc t.inexpr
      else sfold_Expr_Expr extractRecursiveFunctions acc e


  ---------------
  -- OPERATORS --
  ---------------

  -- Can compile fully and partially applied intrinsicGen operators and optimize them
  -- depending on the number of arguments to either compile as in-place operations or
  -- as a partially applied curried intrinsicGen functions
  -- Covers all constants in `stdlib/mexpr/builtin.mc`
  sem compileMConst : Info -> CompileJSContext -> [JSExpr] -> Const -> JSExpr
  sem compileMConst info ctx args =
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
  | CSlli _ & t -> intrinsicStrGen "sll" args
  | CSrli _ & t -> intrinsicStrGen "srl" args
  | CSrai _ & t -> intrinsicStrGen "sra" args

  | CRandIntU _ & t -> intrinsicGen t args

  -- Unary operators
  | CNegf _ & t
  | CNegi _ & t -> optimizedIntrinsicGenStr t "neg" args (_unOp (JSONeg {}))
  | CFloorfi _ & t -> intrinsicStrGen "floor" args
  | CCeilfi _  & t -> intrinsicStrGen "ceil"  args
  | CRoundfi _ & t -> intrinsicStrGen "round" args

  -- Convert operations
  | CInt2Char _ & t -> intrinsicGen t args
  | CChar2Int _ & t -> intrinsicGen t args
  | CInt2float _ & t -> intrinsicGen t args
  | CFloat2string _ & t -> intrinsicGen t args
  | CString2float _ & t -> intrinsicGen t args
  | CStringIsFloat _ & t -> intrinsicGen t args

  -- TODO: | CSymb {val : Symbol} -- (("externalExp"),symb(893105)) is of type (String, Symbol)
  | CGensym _ & t -> intrinsicGen t args
  | CSym2hash _ & t -> intrinsicGen t args
  | CEqsym _ & t -> intrinsicGen t args

  -- Sequential operators (SeqOpAst)
  | CLength _ & t -> intrinsicGen t args
  | CHead _   & t -> intrinsicGen t args
  | CTail _   & t -> intrinsicGen t args
  | CNull _   & t -> intrinsicGen t args
  | CSet _ & t -> intrinsicGen t args
  | CGet _ & t -> intrinsicGen t args
  | CConcat _ & t -> intrinsicGen t args
  | CCons _   & t -> intrinsicGen t args
  | CSnoc _ & t -> intrinsicGen t args
  | CReverse _ & t -> intrinsicGen t args
  | CMap _ & t -> intrinsicGen t args
  | CMapi _ & t -> intrinsicGen t args
  | CIter _ & t -> intrinsicGen t args
  | CIteri _ & t -> intrinsicGen t args
  | CFoldl _  & t -> intrinsicGen t args
  | CFoldr _ & t -> intrinsicGen t args
  | CCreate _ & t -> intrinsicGen t args
  | CCreateList _ & t -> intrinsicGen t args
  | CCreateRope _ & t -> intrinsicGen t args
  | CIsList _ & t -> intrinsicGen t args
  | CIsRope _ & t -> intrinsicGen t args
  | CSplitAt _ & t -> intrinsicGen t args
  | CSubsequence _ & t -> intrinsicGen t args

  -- Map operators (MapAst)
  | CMapEmpty _ & t -> intrinsicGen t args
  | CMapInsert _ & t -> intrinsicGen t args
  | CMapRemove _ & t -> intrinsicGen t args
  | CMapFindExn _ & t -> intrinsicGen t args
  | CMapFindOrElse _ & t -> intrinsicGen t args
  | CMapFindApplyOrElse _ & t -> intrinsicGen t args
  | CMapBindings _ & t -> intrinsicGen t args
  | CMapChooseExn _ & t -> intrinsicGen t args
  | CMapChooseOrElse _ & t -> intrinsicGen t args
  | CMapSize _ & t -> intrinsicGen t args
  | CMapMem _ & t -> intrinsicGen t args
  | CMapAny _ & t -> intrinsicGen t args
  | CMapMap _ & t -> intrinsicGen t args
  | CMapMapWithKey _ & t -> intrinsicGen t args
  | CMapFoldWithKey _ & t -> intrinsicGen t args
  | CMapEq _ & t -> intrinsicGen t args
  | CMapCmp _ & t -> intrinsicGen t args
  | CMapGetCmpFun _ & t -> intrinsicGen t args

  -- References
  | CRef _    & t -> intrinsicGen t args
  | CModRef _ & t -> intrinsicGen t args
  | CDeRef _  & t -> intrinsicGen t args

  -- Not directly mapped to JavaScript operators
  | CPrint _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else -- Warning about inconsistent behaviour
      isInModuleFuncs ctx [("printLn", "stdlib/common.mc"), ("printLn", "internal"), ("utestTestPassed", "internal")]
        info (lam. ()) (lam. infoWarn info "'print' might have unexpected behaviour when targeting the web or a generic JS runtime");
      intrinsicGen t args
  | CDPrint _ & t ->
    -- Warning about inconsistent behaviour
    isInModuleFuncs ctx [("dprintLn", "stdlib/common.mc"), ("dprintLn", "internal")]
      info (lam. JSEReturn { expr = intrinsicGen t args }) -- If so, ignore the last newline print call in dprintLn
      (lam.
        infoWarn info "'dprint' might have unexpected behaviour when targeting the web or a generic JS runtime";
        intrinsicGen t args)
  | CExit _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else JSEString { s = "exit" } -- TODO: Fix this, inspiration: https://stackoverflow.com/questions/550574/how-to-terminate-the-script-in-javascript

  | CArgv _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t [JSENop {}]
    else errorSingle [info] "argv is only supported when targeting Node.js"
  | CConstructorTag _ & t -- Look at `test/mexpr/constructor-tags.mc` for an example
  | CError _ & t
  | CCommand _ & t
  | CWallTimeMs _ & t
  | CSleepMs _ & t -- TODO: inspiration: https://stackoverflow.com/questions/951021/what-is-the-javascript-version-of-sleep
  | CRandSetSeed _ & t
  | CPrintError _ & t
  | CReadLine _ & t
  | CReadBytesAsString _ & t -> infoWarn info (join ["Unsupported intrinsic '", getConstStringCode 0 t, "', emitting a no-op"]); JSENop { }
  | CFlushStderr _ & t
  | CFlushStdout _ & t ->
    (if not (isInModule ctx "stdlib/common.mc") then infoWarn info (join ["Unsupported intrinsic '", getConstStringCode 0 t, "', emitting a no-op"]) else ());
    JSENop { }
  | t -> errorSingle [info] (join ["Unsupported literal '", getConstStringCode 0 t, "' when compiling to JavaScript"])

  ---------------
  -- EXTERNALS --
  ---------------
  sem compileExtRef : CompileJSContext -> Info -> String -> JSExpr
  sem compileExtRef ctx info =
  | t ->
    match compileExt (ctx.options.targetPlatform) info t with Some expr then expr
    else errorSingle [info] (join ["Unsupported external '", t, "' when compiling to JavaScript"])


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
  sem compileMExpr : CompileJSContext -> Expr -> JSExpr
  sem compileMExpr ctx =
  | TmVar { ident = id } -> JSEVar { id = id }
  | TmApp { info = info } & app ->
    match foldApp [] app with (fun, args) in
    -- Function calls
    let args = map (compileMExpr ctx) args in
    match fun with TmVar { ident = ident } then
      JSEApp {
        fun = JSEVar { id = ident },
        args = args,
        curried = true
      }
    -- Intrinsics
    else match fun with TmConst { val = val, info = info } then
      compileMConst info ctx args val
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
      let str: String = _charSeq2String tms in
      JSEString { s = str }
    else
      JSEArray { exprs = map (compileMExpr ctx) tms }

  -- Literals
  | TmConst { val = val, info = info } ->
    match val      with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileMConst info ctx [] val with jsexpr in jsexpr -- SeqOpAst Consts are handled by the compile operator semantics
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
    let compileBind = lam bind : RecLetBinding.
      match bind with { ident = ident, body = body, info = info } in
      match body with TmLam _ then
        let ctx = { ctx with currentFunction = Some (ident, info) } in
        let fun = compileMExpr ctx body in
        if ctx.options.optimizations
          then optimizeTailCallFunc ctx ident info fun
          else JSEDef { id = ident, expr = fun }
      else errorSingle [info] "Cannot handle non-lambda in recursive let when compiling to JavaScript"
    in
    let exprs = map compileBind bindings in
    flattenBlock (JSEBlock {
      exprs = exprs,
      ret = compileMExpr ctx e
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
  | TmExt { ident = ident, tyIdent = tyIdent, inexpr = inexpr, effect = effect, ty = ty, info = info } & t ->
    let expr = compileExtRef ctx info (nameGetStr ident) in
    flattenBlock (JSEBlock {
      exprs = [JSEDef { id = ident, expr = expr }],
      ret = compileMExpr ctx inexpr
    })
  | TmNever _ -> intrinsicStrGen "never" [JSENop {}]

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
