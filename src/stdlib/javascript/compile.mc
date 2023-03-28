include "mexpr/boot-parser.mc"
include "mexpr/symbolize.mc"
include "mexpr/pprint.mc"
include "mexpr/info.mc"
include "mexpr/ast.mc"

include "javascript/ast.mc"
include "javascript/util.mc"
include "javascript/pprint.mc"
include "javascript/patterns.mc"
include "javascript/intrinsics.mc"
include "javascript/optimizations.mc"

include "sys.mc"
include "common.mc"
include "seq.mc"
include "set.mc"
include "error.mc"
include "name.mc"
include "option.mc"
include "string.mc"
include "bool.mc"



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
                      JSOptimizeExprs + JSIntrinsic

  -- Entry point
  sem compileProg : CompileJSContext -> Expr -> JSProg
  sem compileProg ctx =
  | prog ->
    let ctx = if ctx.options.tailCallOptimizations then extractRFRctx ctx prog else ctx in
    -- Run compiler
    match compileMExpr ctx prog with (ctx, expr) in
    let exprs = (match expr with JSEBlock { exprs = exprs, ret = ret }
      then
        match compileDeclarations ctx with (ctx, decs) in
        join [ [decs], exprs, [ret] ]
      else [expr]) in
    -- Return final top level expressions
    JSPProg { imports = [], exprs = exprs }


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

  -- References
  | CRef _    & t -> intrinsicGen t args
  | CModRef _ & t -> intrinsicGen t args
  | CDeRef _  & t -> intrinsicGen t args

  | CError _ & t -> intrinsicGen t args

  -- Not directly mapped to JavaScript operators
  | CPrint _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else match ctx.options.targetPlatform with CompileJSTP_Bun () then intrinsicBun t args
    else -- Warning about inconsistent behaviour
      isInModuleFuncs ctx [("printLn", "stdlib/common.mc"), ("printLn", "internal"), ("utestTestPassed", "internal")]
        info (lam. ()) (lam. infoWarn info "'print' might have unexpected behaviour when targeting the web or a generic JS runtime");
      intrinsicGen t args
  | CDPrint _ & t ->
    -- Warning about inconsistent behaviour
    isInModuleFuncs ctx [("dprintLn", "stdlib/common.mc"), ("dprintLn", "internal")] info
      (lam. JSEReturn { expr = intrinsicGen t args }) -- Ignore the last newline print call in dprintLn
      (lam.
        infoWarn info "'dprint' might have unexpected behaviour when targeting the web or a generic JS runtime";
        intrinsicGen t args)
  | CExit _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t args
    else match ctx.options.targetPlatform with CompileJSTP_Bun () then intrinsicBun t args
    else JSEString { s = "exit" } -- TODO: Fix this, inspiration: https://stackoverflow.com/questions/550574/how-to-terminate-the-script-in-javascript

  | CArgv _ & t ->
    match ctx.options.targetPlatform with CompileJSTP_Node () then intrinsicNode t [JSENop {}]
    else match ctx.options.targetPlatform with CompileJSTP_Bun () then intrinsicBun t [JSENop {}]
    else errorSingle [info] "argv is only supported when targeting Node.js"
  | CConstructorTag _ & t -- Look at `test/mexpr/constructor-tags.mc` for an example
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


  -- Extract the name of the function and the arguments from
  -- a function application. Also compile the arguments.
  sem foldApp : CompileJSContext -> [JSExpr] -> Expr -> (CompileJSContext, Expr, [JSExpr])
  sem foldApp ctx acc =
  | TmApp { lhs = lhs, rhs = rhs } ->
    match
      match rhs with TmRecord {bindings = bindings} then
        if mapIsEmpty bindings then (ctx, JSENop {})
        else compileMExpr ctx rhs
      else compileMExpr ctx rhs
    with (ctx, e) in
    foldApp ctx (cons e acc) lhs
  | t -> (ctx, t, acc)

  sem mapCompileMExpr : CompileJSContext -> [Expr] -> (CompileJSContext, [JSExpr])
  sem mapCompileMExpr ctx =
  | exprs ->
    foldr (lam e: Expr. lam acc: (CompileJSContext, [JSExpr]).
      match acc with (ctx, es) in
      match compileMExpr ctx e with (ctx, e) in
      (ctx, cons e es)
    ) (ctx, []) exprs

  -----------------
  -- EXPRESSIONS --
  -----------------
  sem compileMExpr : CompileJSContext -> Expr -> (CompileJSContext, JSExpr)
  sem compileMExpr ctx =
  | TmVar { ident = id } -> (ctx, JSEVar { id = id })
  | TmApp _ & app -> -- Function calls
    match foldApp ctx [] app with (ctx, fun, args) in
    match fun with TmVar { ident = ident } then
      (ctx, JSEApp {
        fun = JSEVar { id = ident },
        args = args,
        curried = true
      })
    -- Intrinsics
    else match fun with TmConst { val = val, info = info } then
      (ctx, compileMConst info ctx args val)
    else errorSingle [infoTm app] "Unsupported application in compileMExpr"

  -- Anonymous function
  | TmLam { ident = arg, body = body } ->
    match compileMExpr ctx body with (ctx, body) in
    (ctx, JSEFun { params = [arg], body = body })

  -- Unit type is represented by int literal 0.
  | TmRecord { bindings = bindings } ->
    let fieldSeq = mapToSeq bindings in
    match foldl (lam acc: (CompileJSContext, [(String, JSExpr)]). lam f: (SID, Expr).
      match acc with (ctx, es) in
      match f with (sid, expr) in
      match compileMExpr ctx expr with (ctx, expr) in
      (ctx, cons (sidToString sid, expr) es)
    ) (ctx, []) fieldSeq with (ctx, fields) in
    (ctx, JSEObject { fields = fields })

  | TmSeq {tms = tms} ->
    -- Check if sequence of characters, then concatenate them into a string
    if _isCharSeq tms then
      let str: String = _charSeq2String tms in
      (ctx, JSEString { s = str })
    else
      match mapCompileMExpr ctx tms with (ctx, exprs) in
      (ctx, JSEArray { exprs = exprs })

  -- Literals
  | TmConst { val = val, info = info } ->
    let expr = (match val with CInt   { val = val } then JSEInt   { i = val }
    else match val with CFloat { val = val } then JSEFloat { f = val }
    else match val with CChar  { val = val } then JSEChar  { c = val }
    else match val with CBool  { val = val } then JSEBool  { b = val }
    else match compileMConst info ctx [] val with jsexpr in jsexpr) -- SeqOpAst Consts are handled by the compile operator semantics
    in (ctx, expr)
  | TmRecordUpdate _ & t -> errorSingle [infoTm t] "Record updates cannot be handled in compileMExpr."


  ----------------
  -- STATEMENTS --
  ----------------

  | TmLet { ident = ident, body = body, inexpr = e, info = info } ->
    match nameGetStr ident with [] then
      match compileMExpr ctx body with (ctx1, body) in
      match compileMExpr ctx e with (ctx2, e) in
      let ctx = combineDeclarations ctx1 ctx2 in
      match compileDeclarations ctx with (ctx, decs) in
      (ctx, flattenBlock (JSEBlock {
        exprs = [decs, body],
        ret = e
      }))
    else
      let ctx = (match body with TmLam _ then { ctx with currentFunction = Some (ident, info) } else ctx) in
      match compileMExpr ctx body with (ctx1, body) in
      match compileMExpr ctx e with (ctx2, e) in
      let ctx = combineDeclarations ctx1 ctx2 in
      match compileDeclarations ctx with (ctx, decs) in
      let bindingExpr = JSEIIFE {
        body = flattenBlock (JSEBlock {
          exprs = [decs, JSEDef { id = ident, expr = body }],
          ret = e})} in
      (ctx, bindingExpr)

  | TmRecLets { bindings = bindings, inexpr = e, ty = ty } ->
    match compileMExpr ctx e with (ctx, e) in
    match foldl (lam acc: (CompileJSContext, [JSExpr]). lam bind : RecLetBinding.
      match acc with (ctx, es) in
      match bind with { ident = ident, body = body, info = info } in
      match body with TmLam _ then
        let ctx = { ctx with currentFunction = Some (ident, info) } in
        match compileMExpr ctx body with (ctx, body) in
        let expr = (if ctx.options.tailCallOptimizations
          then optimizeTailCallFunc ctx ident info body
          else JSEDef { id = ident, expr = body }) in
        (ctx, cons expr es)
      else errorSingle [info] "Cannot handle non-lambda in recursive let when compiling to JavaScript"
      ) (ctx, []) bindings with (ctx, exprs) in
    match compileDeclarations ctx with (ctx, decs) in
    (ctx, flattenBlock (JSEBlock {
      exprs = cons decs exprs,
      ret = e
    }))

  | TmType { inexpr = e } -> compileMExpr ctx e -- Ignore
  | TmConDef { ident = ident, inexpr = e } ->
    let valueParam = nameSym "v" in
    match compileMExpr ctx e with (ctx, e) in
    match compileDeclarations ctx with (ctx, decs) in
    (ctx, flattenBlock (JSEBlock {
      exprs = [
        decs,
        JSEDef { id = ident, expr = JSEFun {
          params = [valueParam],
          body = JSEObject { fields = [
            ("type", JSEString { s = ident.0 }),
            ("value", JSEVar { id = valueParam })
          ] }
        } }
      ],
      ret = e
    }))
  | TmConApp { ident = ident, body = body } ->
    match compileMExpr ctx body with (ctx, body) in
    (ctx, JSEApp {
      fun = JSEVar { id = ident },
      args = [body],
      curried = false
    })
  | TmMatch t ->
    match compileMExpr ctx t.target with (ctx, target) in
    match compileMExpr ctx t.thn with (ctx, thn) in
    match compileMExpr ctx t.els with (ctx, els) in
    match compilePattern ctx target t.pat with (ctx, cond) in
    let expr = JSETernary {
      cond = cond,
      thn = immediatelyInvokeBlock thn,
      els = immediatelyInvokeBlock els} in
    (ctx, if ctx.options.generalOptimizations then optimizeExpr3 expr else expr)
  | TmUtest _ & t -> errorSingle [infoTm t] "Unit test expressions cannot be handled in compileMExpr"
  | TmExt _ & t -> errorSingle [infoTm t] "External expressions cannot be handled in compileMExpr"
  | TmNever _ -> (ctx, intrinsicStrGen "never" [JSENop {}])


  sem tryCompileOptimizedMatch : CompileJSContext -> Expr -> Pat -> Expr -> Expr -> Option (CompileJSContext, JSExpr)
  sem tryCompileOptimizedMatch ctx target pat thn =
  | els ->
      let elsIsNever = (match els with TmNever _ then true else false) in
      match pat with PatRecord { bindings = bindings } then
        if and (eqi (mapLength bindings) 1) elsIsNever then -- Reduce to an indexing operation
          match mapToSeq bindings with [(key, val)] in -- match target with { key: SID = value: Pat }
          -- Check if the then branch returns the value of the record field
          match val with PatNamed { ident = PName valName } then
            match thn with TmVar { ident = thnName } then
              if nameEq valName thnName then
                -- Return an indexing operation on the target with the key
                match compileMExpr ctx target with (ctx, expr) in
                Some (ctx, JSEIndex {
                  expr = expr,
                  index = sidToString key
                })
              else None ()
            else None ()
          else None ()
        else None ()
      else None ()

end





-- Helper functions
let filepathWithoutExtension = lam filename.
  match strLastIndex '.' filename with Some idx then
    subsequence filename 0 idx
  else filename

-- Compile a Miking AST to a JavaScript program AST.
-- Walk the AST and convert it to a JavaScript AST.
let javascriptCompile : use MExprJSCompile in CompileJSOptions -> Expr -> JSProg =
  lam opts : CompileJSOptions. lam ast : use Ast in Expr.
  use MExprJSCompile in
  let ctx = { compileJSCtxEmpty with options = opts } in
  compileProg ctx ast


let javascriptCompileFile : use Ast in CompileJSOptions -> Expr -> String -> String =
  lam opts : CompileJSOptions.
  lam ast : use Ast in Expr.
  lam sourcePath: String.
  use JSProgPrettyPrint in
  let targetPath = concat (filepathWithoutExtension sourcePath) ".js" in
  let jsprog = javascriptCompile opts ast in   -- Run JS compiler
  let source = printJSProg jsprog in      -- Pretty print
  let intrinsics = join [readFile jsIntrinsicsFile_generic, (
    switch opts.targetPlatform
    case CompileJSTP_Web () then readFile jsIntrinsicsFile_web
    case CompileJSTP_Node () then readFile jsIntrinsicsFile_node
    case CompileJSTP_Bun () then readFile jsIntrinsicsFile_bun
    case _ then "" end
  ), "\n"] in
  writeFile targetPath (concat intrinsics source);
  targetPath
