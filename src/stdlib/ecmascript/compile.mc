-- Compilation of MExpr to the ECMAScript AST.
--
-- The compiler works in two modes, which is what keeps a chain of `let ... in`
-- bindings flat instead of nesting one function scope per binding:
--
--   * `compileStmts` is *statement* mode. It knows where the value of the
--     expression is going -- via an `ESCont` -- and returns a flat statement
--     list. A `TmDecl` spine simply concatenates, and a `TmMatch` becomes an
--     `if`/`else` rather than a ternary over immediately-invoked functions.
--
--   * `compileExpr` is *expression* mode. It returns an expression plus any
--     statements that must run before it, so bindings encountered in
--     expression position are hoisted into the enclosing statement list rather
--     than wrapped in an immediately-invoked function.

include "ecmascript/ast.mc"
include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
-- Only for `getConstStringCode`, which names constants in error messages.
include "mexpr/pprint.mc"
include "name.mc"
include "seq.mc"
include "set.mc"

-- Where the value produced by a term should go.
type ESCont
con ESCReturn : () -> ESCont    -- `return <e>;`
con ESCBind : Name -> ESCont    -- `const x = <e>;`
con ESCAssign : Name -> ESCont  -- `x = <e>;`, for a name declared by a branch
con ESCDiscard : () -> ESCont   -- `<e>;`

type ESCompileCtx = {
  -- The name bound to the runtime environment parameter of the generated
  -- `main` function. Effectful intrinsics compile to member access on it, so
  -- that a caller supplies them on every execution.
  runtimeEnv : Name,

  -- Arity of each name bound to a chain of lambdas. A saturated call to one of
  -- these becomes a direct n-ary call; see `esApplyKnown`.
  arities : Map Name Int,

  -- Pure runtime intrinsics the program has used. Their definitions are
  -- appended to the bottom of the generated module.
  runtime : Set String
}

let esCompileCtxEmpty : ESCompileCtx = {
  runtimeEnv = nameNoSym "env",
  arities = mapEmpty nameCmp,
  runtime = setEmpty cmpString
}

-- Flattens a curried application spine into its head and argument list.
recursive let esCollectApp : use Ast in Expr -> (Expr, [Expr]) =
  use MExprAst in
  lam e.
  match e with TmApp t then
    match esCollectApp t.lhs with (fn, args) in
    (fn, snoc args t.rhs)
  else (e, [])
end

-- Flattens a chain of single-parameter lambdas into a parameter list and body.
recursive let esCollectLams : use Ast in Expr -> ([Name], Expr) =
  use MExprAst in
  lam e.
  match e with TmLam t then
    match esCollectLams t.body with (params, body) in
    (cons t.ident params, body)
  else ([], e)
end

lang MExprESCompile = MExprAst + ESAst + MExprPrettyPrint

  -----------------
  -- SMALL UTILS --
  -----------------

  sem esTrue : () -> ESExpr
  sem esTrue = | _ -> ESEBool { value = true }

  sem esIsTrue : ESExpr -> Bool
  sem esIsTrue =
  | ESEBool { value = true } -> true
  | _ -> false

  -- Applies `fn` one argument at a time, as MExpr semantics require when the
  -- callee's arity is unknown.
  sem esCurryApply : ESExpr -> [ESExpr] -> ESExpr
  sem esCurryApply fn =
  | args -> foldl (lam acc. lam a. ESECall { callee = acc, args = [a] }) fn args

  -- Wraps `body` in one single-parameter arrow per name, outermost first.
  sem esCurryArrows : [Name] -> ESExpr -> ESExpr
  sem esCurryArrows params =
  | body ->
    foldr (lam p. lam acc. ESEArrow { params = [p], body = ESFBExpr { expr = acc } })
      body params

  -- Emits the statement that delivers `expr` to its destination.
  sem esDeliver : ESCont -> ESExpr -> [ESStmt]
  sem esDeliver cont =
  | expr ->
    switch cont
    case ESCReturn _ then [ESSReturn { expr = Some expr }]
    case ESCBind id then [ESSConst { id = id, init = expr }]
    case ESCAssign id then
      [ESSAssign { target = ESEVar { id = id }, value = expr }]
    case ESCDiscard _ then [ESSExpr { expr = expr }]
    end

  -- A `const` cannot be introduced inside one arm of an `if` and read after
  -- it, so a binding continuation becomes a `let` declared before the branch
  -- plus an assignment within each arm.
  sem esBranchCont : ESCont -> ([ESStmt], ESCont)
  sem esBranchCont =
  | ESCBind id -> ([ESSLet { id = id, init = None () }], ESCAssign id)
  | cont -> ([], cont)

  -- Recovers the value from a statement that delivers to `cont`, if that is
  -- all the statement does. Used to fold a two-armed branch back into a
  -- ternary without recompiling either arm.
  sem esUndeliver : ESCont -> ESStmt -> Option ESExpr
  sem esUndeliver cont =
  | ESSReturn { expr = Some e } ->
    match cont with ESCReturn _ then Some e else None ()
  | ESSAssign { target = ESEVar { id = id }, value = v } ->
    match cont with ESCAssign id2 then
      if nameEq id id2 then Some v else None ()
    else None ()
  | _ -> None ()

  sem esThrow : Info -> String -> ESStmt
  sem esThrow info =
  | msg ->
    ESSThrow { expr = ESENew
      { callee = ESEGlobal { name = "Error" }
      , args = [ESEString { value = join [msg, " at ", info2str info] }] } }

  ---------------------
  -- STATEMENT MODE --
  ---------------------

  sem compileStmts : ESCompileCtx -> ESCont -> Expr -> (ESCompileCtx, [ESStmt])
  sem compileStmts ctx cont =
  | TmDecl { decl = DeclLet d, inexpr = inexpr } ->
    -- The whole point: a binding becomes a sibling statement, not a scope.
    match compileStmtsDecl ctx d with (ctx, bind) in
    match compileStmts ctx cont inexpr with (ctx, rest) in
    (ctx, concat bind rest)
  | TmDecl { decl = decl } & t ->
    errorSingle [infoTm t] (concat
      "ecmascript: unsupported declaration: " (esDeclName decl))
  | TmMatch t ->
    match compileExpr ctx t.target with (ctx, s0, target) in
    match esPatCompile ctx target t.pat with (ctx, test, binds) in
    if esIsTrue test then
      -- Irrefutable: the else branch is unreachable, so emit no branch at all.
      match compileStmts ctx cont t.thn with (ctx, thn) in
      (ctx, join [s0, binds, thn])
    else
      match esBranchCont cont with (pre, bcont) in
      match compileStmts ctx bcont t.thn with (ctx, thn) in
      match compileStmts ctx bcont t.els with (ctx, els) in
      -- When both arms do nothing but produce a value, a ternary reads better
      -- than a four-line `if`. Checked on the compiled arms rather than by
      -- compiling them twice, which would be exponential in nesting depth.
      let folded =
        match (binds, thn, els) with ([], [thn1], [els1]) then
          match (esUndeliver bcont thn1, esUndeliver bcont els1)
            with (Some a, Some b) then
            Some (esDeliver cont (ESECond { cond = test, thn = a, els = b }))
          else None ()
        else None () in
      match folded with Some stmts then (ctx, concat s0 stmts)
      else
        (ctx, join [s0, pre,
          [ESSIf { cond = test, thn = concat binds thn, els = els }]])
  | TmNever t ->
    (ctx, [esThrow t.info "ecmascript: reached a `never` expression"])
  | t ->
    match compileExpr ctx t with (ctx, stmts, expr) in
    (ctx, concat stmts (esDeliver cont expr))

  ----------------------
  -- EXPRESSION MODE --
  ----------------------

  sem compileExpr : ESCompileCtx -> Expr -> (ESCompileCtx, [ESStmt], ESExpr)
  sem compileExpr ctx =
  | TmVar t ->
    -- A named n-ary function used as a value has to be handed back in curried
    -- form, since whoever receives it will apply one argument at a time.
    match mapLookup t.ident ctx.arities with Some n then
      let ps = create n (lam. nameSym "a") in
      (ctx, [], esCurryArrows ps (ESECall
        { callee = ESEVar { id = t.ident }
        , args = map (lam p. ESEVar { id = p }) ps }))
    else (ctx, [], ESEVar { id = t.ident })
  | TmConst t & e ->
    match esConstLit t.val with Some lit then (ctx, [], lit)
    else match esConstArity t.val with Some n then
      let ps = create n (lam. nameSym "a") in
      match esConstApplyWith ctx (map (lam p. ESEVar { id = p }) ps) t.val
        with (ctx, body) in
      (ctx, [], esCurryArrows ps body)
    else errorSingle [infoTm e] (concat
      "ecmascript: unsupported constant: " (getConstStringCode 0 t.val))
  | TmLam _ & t ->
    -- An anonymous lambda's arity is not tracked anywhere, so whoever receives
    -- it will apply one argument at a time: emit curried arrows.
    match esCollectLams t with (params, body) in
    match compileStmts ctx (ESCReturn ()) body with (ctx, stmts) in
    -- A lone `return e;` reads better as a concise arrow body.
    let innerBody = match stmts with [ESSReturn { expr = Some e }]
      then ESFBExpr { expr = e } else ESFBBlock { stmts = stmts } in
    match splitAt params (subi (length params) 1) with (outer, [innermost]) in
    (ctx, [], esCurryArrows outer
      (ESEArrow { params = [innermost], body = innerBody }))
  | TmDecl { decl = DeclLet _ } & t ->
    -- Hoist the binding out in front of the expression that needs it. Sound
    -- because a hoist never crosses a conditional: `TmMatch` in expression
    -- position keeps each branch's statements inside its own arm, below.
    match t with TmDecl { decl = DeclLet d, inexpr = inexpr } in
    match compileStmtsDecl ctx d with (ctx, bind) in
    match compileExpr ctx inexpr with (ctx, stmts, expr) in
    (ctx, concat bind stmts, expr)
  | TmApp _ & t ->
    match esCollectApp t with (fn, args) in
    match fn with TmConst c then compileConstApp ctx (infoTm t) c.val args
    else match fn with TmVar v then
      match mapLookup v.ident ctx.arities with Some n then
        esApplyKnown ctx v.ident n args
      else
        match compileExprs ctx args with (ctx, s, xs) in
        (ctx, s, esCurryApply (ESEVar { id = v.ident }) xs)
    else
      match compileExpr ctx fn with (ctx, s0, callee) in
      match compileExprs ctx args with (ctx, s1, xs) in
      (ctx, concat s0 s1, esCurryApply callee xs)
  | TmMatch t ->
    match compileExpr ctx t.target with (ctx, s0, target) in
    match esPatCompile ctx target t.pat with (ctx, test, binds) in
    if esIsTrue test then
      match compileExpr ctx t.thn with (ctx, s1, e) in
      (ctx, join [s0, binds, s1], e)
    else
      match compileExpr ctx t.thn with (ctx, sThn, eThn) in
      match compileExpr ctx t.els with (ctx, sEls, eEls) in
      if and (null binds) (and (null sThn) (null sEls)) then
        (ctx, s0, ESECond { cond = test, thn = eThn, els = eEls })
      else
        -- A branch needs statements, so declare a temporary and assign in each
        -- arm. Still no immediately-invoked function.
        let tmp = nameSym "v" in
        (ctx
        , join [s0, [ESSLet { id = tmp, init = None () }]
          , [ESSIf { cond = test
                   , thn = join [binds, sThn, esDeliver (ESCAssign tmp) eThn]
                   , els = concat sEls (esDeliver (ESCAssign tmp) eEls) }]]
        , ESEVar { id = tmp })
  | TmNever t ->
    (ctx, [esThrow t.info "ecmascript: reached a `never` expression"], esUnit)
  | TmRecord t ->
    if mapIsEmpty t.bindings then (ctx, [], esUnit)
    else errorSingle [t.info] "ecmascript: records are not supported yet"
  | t ->
    errorSingle [infoTm t] (concat
      "ecmascript: unsupported expression: " (esExprName t))

  -- Compiles a single `DeclLet` to the statements that bind it.
  sem compileStmtsDecl : ESCompileCtx -> DeclLetRecord -> (ESCompileCtx, [ESStmt])
  sem compileStmtsDecl ctx =
  | d ->
    -- `a; b` desugars to `let #var"" = a in b`, whose binder has an empty name
    -- and is never referenced. Emit the effect as a bare statement instead of
    -- an unused `const`.
    if null (nameGetStr d.ident) then
      compileStmts ctx (ESCDiscard ()) d.body
    else match d.body with TmLam _ then
      -- A named function: emit an n-ary declaration and record its arity so
      -- that saturated calls avoid currying. `DeclLet` is not recursive, so
      -- the arity is deliberately recorded only after compiling the body.
      match esCollectLams d.body with (params, body) in
      match compileStmts ctx (ESCReturn ()) body with (ctx, bodyStmts) in
      let ctx = { ctx with
        arities = mapInsert d.ident (length params) ctx.arities } in
      (ctx, [ESSFunDecl { id = d.ident, params = params, body = bodyStmts }])
    else match d.body with TmVar v then
      -- An alias inherits the arity it points at, so calls through it stay
      -- n-ary instead of going through an eta-expanded curried wrapper.
      match mapLookup v.ident ctx.arities with Some n then
        ({ ctx with arities = mapInsert d.ident n ctx.arities }
        , [ESSConst { id = d.ident, init = ESEVar { id = v.ident } }])
      else compileStmts ctx (ESCBind d.ident) d.body
    else compileStmts ctx (ESCBind d.ident) d.body

  -- Compiles a list of expressions, concatenating the statements each hoists.
  sem compileExprs : ESCompileCtx -> [Expr] -> (ESCompileCtx, [ESStmt], [ESExpr])
  sem compileExprs ctx =
  | exprs ->
    let step = lam acc. lam e.
      match acc with (ctx, stmts) in
      match compileExpr ctx e with (ctx, s, x) in
      ((ctx, concat stmts s), x)
    in
    match mapAccumL step (ctx, []) exprs with ((ctx, stmts), xs) in
    (ctx, stmts, xs)

  -- Applies a name of known arity. A saturated call is a direct n-ary call; a
  -- partial one is eta-expanded so the emitted function is never called with
  -- too few arguments; extra arguments are applied to the result.
  sem esApplyKnown
    : ESCompileCtx -> Name -> Int -> [Expr] -> (ESCompileCtx, [ESStmt], ESExpr)
  sem esApplyKnown ctx id arity =
  | args ->
    match compileExprs ctx args with (ctx, stmts, xs) in
    let fn = ESEVar { id = id } in
    let n = length xs in
    if lti n arity then
      let extra = create (subi arity n) (lam. nameSym "a") in
      (ctx, stmts, esCurryArrows extra (ESECall
        { callee = fn
        , args = concat xs (map (lam p. ESEVar { id = p }) extra) }))
    else
      let saturated = ESECall { callee = fn, args = subsequence xs 0 arity } in
      (ctx, stmts, esCurryApply saturated (subsequence xs arity (subi n arity)))

  --------------
  -- PATTERNS --
  --------------

  -- Returns a test deciding whether `target` matches, and the statements that
  -- bind the pattern's names. After pattern lowering every pattern is shallow,
  -- so sub-patterns are names or wildcards and no recursion is needed here.
  sem esPatCompile
    : ESCompileCtx -> ESExpr -> Pat -> (ESCompileCtx, ESExpr, [ESStmt])
  sem esPatCompile ctx target =
  | PatNamed { ident = PName n } ->
    (ctx, esTrue (), [ESSConst { id = n, init = target }])
  | PatNamed { ident = PWildcard _ } -> (ctx, esTrue (), [])
  | PatInt t ->
    (ctx, ESEBin { op = ESOEq {}, lhs = target, rhs = ESEInt { value = t.val } }, [])
  | PatChar t ->
    (ctx, ESEBin { op = ESOEq {}, lhs = target
                 , rhs = ESEString { value = [t.val] } }, [])
  | PatBool t ->
    (ctx, (if t.val then target else ESEUn { op = ESONot {}, arg = target }), [])
  | p ->
    errorSingle [infoPat p] (concat
      "ecmascript: unsupported pattern: " (esPatName p))

  ----------------
  -- INTRINSICS --
  ----------------

  -- Constants that are values rather than operations.
  sem esConstLit : Const -> Option ESExpr
  sem esConstLit =
  | CInt t -> Some (ESEInt { value = t.val })
  | CFloat t -> Some (ESEFloat { value = t.val })
  | CBool t -> Some (ESEBool { value = t.val })
  -- A Char is a one-character string, the element representation of `[Char]`.
  | CChar t -> Some (ESEString { value = [t.val] })
  | _ -> None ()

  -- How many arguments an operation consumes. `None` means unsupported.
  sem esConstArity : Const -> Option Int
  sem esConstArity =
  | CAddi _ | CSubi _ | CMuli _ | CDivi _ | CModi _
  | CEqi _ | CNeqi _ | CLti _ | CGti _ | CLeqi _ | CGeqi _
  | CSlli _ | CSrli _ | CSrai _
  | CAddf _ | CSubf _ | CMulf _ | CDivf _
  | CEqf _ | CNeqf _ | CLtf _ | CGtf _ | CLeqf _ | CGeqf _
  | CEqc _ -> Some 2
  | CNegi _ | CNegf _ | CFloorfi _ | CCeilfi _ | CRoundfi _ | CInt2float _
  | CChar2Int _ | CInt2Char _ | CDPrint _ -> Some 1
  | _ -> None ()

  -- Builds the expression for an operation applied to exactly its arity.
  sem esConstApplyWith : ESCompileCtx -> [ESExpr] -> Const -> (ESCompileCtx, ESExpr)
  sem esConstApplyWith ctx args =
  | const ->
    let bin = lam op.
      match args with [a, b] in (ctx, ESEBin { op = op, lhs = a, rhs = b }) in
    let un = lam op.
      match args with [a] in (ctx, ESEUn { op = op, arg = a }) in
    let math = lam f.
      match args with [a] in
      (ctx, ESECall { callee = esMember (ESEGlobal { name = "Math" }) f, args = [a] }) in
    let rt = lam name.
      ({ ctx with runtime = setInsert name ctx.runtime }
      , ESECall { callee = ESEGlobal { name = name }, args = args }) in
    switch const
    -- Integer arithmetic. `divi` truncates towards zero, as OCaml does.
    case CAddi _ then bin (ESOAdd {})
    case CSubi _ then bin (ESOSub {})
    case CMuli _ then bin (ESOMul {})
    case CDivi _ then
      match args with [a, b] in
      (ctx, ESECall { callee = esMember (ESEGlobal { name = "Math" }) "trunc"
                    , args = [ESEBin { op = ESODiv {}, lhs = a, rhs = b }] })
    case CModi _ then bin (ESOMod {})
    case CNegi _ then un (ESONeg {})
    case CEqi _ then bin (ESOEq {})
    case CNeqi _ then bin (ESONeq {})
    case CLti _ then bin (ESOLt {})
    case CGti _ then bin (ESOGt {})
    case CLeqi _ then bin (ESOLe {})
    case CGeqi _ then bin (ESOGe {})
    -- Shifts keep OCaml's 63-bit semantics; see runtime/mexpr.mjs.
    case CSlli _ then rt "$slli"
    case CSrli _ then rt "$srli"
    case CSrai _ then rt "$srai"
    -- Floats share the `number` representation, so `int2float` is a no-op.
    case CAddf _ then bin (ESOAdd {})
    case CSubf _ then bin (ESOSub {})
    case CMulf _ then bin (ESOMul {})
    case CDivf _ then bin (ESODiv {})
    case CNegf _ then un (ESONeg {})
    case CEqf _ then bin (ESOEq {})
    case CNeqf _ then bin (ESONeq {})
    case CLtf _ then bin (ESOLt {})
    case CGtf _ then bin (ESOGt {})
    case CLeqf _ then bin (ESOLe {})
    case CGeqf _ then bin (ESOGe {})
    case CInt2float _ then match args with [a] in (ctx, a)
    case CFloorfi _ then math "floor"
    case CCeilfi _ then math "ceil"
    -- `Math.round` rounds half towards +Infinity; OCaml rounds half away from
    -- zero, so they disagree on every negative half.
    case CRoundfi _ then rt "$roundfi"
    -- Chars are one-character strings.
    case CEqc _ then bin (ESOEq {})
    case CChar2Int _ then
      match args with [a] in
      (ctx, ESECall { callee = esMember a "codePointAt", args = [ESEInt { value = 0 }] })
    case CInt2Char _ then
      match args with [a] in
      (ctx, ESECall
        { callee = esMember (ESEGlobal { name = "String" }) "fromCodePoint"
        , args = [a] })
    case CDPrint _ then
      (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "dprint", args = args })
    case _ then error "esConstApplyWith: arity table and cases disagree"
    end

  sem compileConstApp
    : ESCompileCtx -> Info -> Const -> [Expr] -> (ESCompileCtx, [ESStmt], ESExpr)
  sem compileConstApp ctx info const =
  | args ->
    match esConstArity const with Some arity then
      match compileExprs ctx args with (ctx, stmts, xs) in
      let n = length xs in
      if lti n arity then
        -- Partial application: eta-expand into a curried closure.
        let extra = create (subi arity n) (lam. nameSym "a") in
        match esConstApplyWith ctx
          (concat xs (map (lam p. ESEVar { id = p }) extra)) const
          with (ctx, body) in
        (ctx, stmts, esCurryArrows extra body)
      else
        match esConstApplyWith ctx (subsequence xs 0 arity) const with (ctx, e) in
        (ctx, stmts, esCurryApply e (subsequence xs arity (subi n arity)))
    else errorSingle [info] (concat
      "ecmascript: unsupported constant: " (getConstStringCode 0 const))

  -------------------------
  -- ERROR MESSAGE NAMES --
  -------------------------

  sem esDeclName : Decl -> String
  sem esDeclName =
  | DeclLet _ -> "let"
  | DeclRecLets _ -> "recursive let"
  | DeclType _ -> "type"
  | DeclConDef _ -> "con"
  | DeclExt _ -> "external"
  | DeclUtest _ -> "utest"

  sem esExprName : Expr -> String
  sem esExprName =
  | TmVar _ -> "TmVar"                | TmApp _ -> "TmApp"
  | TmLam _ -> "TmLam"                | TmDecl _ -> "TmDecl"
  | TmConst _ -> "TmConst"            | TmSeq _ -> "TmSeq"
  | TmRecord _ -> "TmRecord"          | TmRecordUpdate _ -> "TmRecordUpdate"
  | TmConApp _ -> "TmConApp"          | TmMatch _ -> "TmMatch"
  | TmNever _ -> "TmNever"            | TmOpaque _ -> "TmOpaque"
  | TmPlaceholder _ -> "TmPlaceholder" | _ -> "an unrecognized term"

  sem esPatName : Pat -> String
  sem esPatName =
  | PatNamed _ -> "PatNamed"      | PatSeqTot _ -> "PatSeqTot"
  | PatSeqEdge _ -> "PatSeqEdge"  | PatRecord _ -> "PatRecord"
  | PatCon _ -> "PatCon"          | PatInt _ -> "PatInt"
  | PatChar _ -> "PatChar"        | PatBool _ -> "PatBool"
  | PatAnd _ -> "PatAnd"          | PatOr _ -> "PatOr"
  | PatNot _ -> "PatNot"          | _ -> "an unrecognized pattern"

  --------------
  -- PROGRAM --
  --------------

  -- Wraps a compiled program in `export default function main(env) { ... }`,
  -- and reports which runtime intrinsics it used.
  --
  -- The top-level expression is discarded rather than returned: in practice it
  -- is the program's final effect and has unit type, and `env.print(x);` reads
  -- better than `return env.print(x);`.
  sem compileESProg : Expr -> (ESProg, [String])
  sem compileESProg =
  | ast ->
    let runtimeEnv = nameSym "env" in
    let ctx = { esCompileCtxEmpty with runtimeEnv = runtimeEnv } in
    match compileStmts ctx (ESCDiscard ()) ast with (ctx, stmts) in
    ( ESProg
      { imports = []
      , stmts =
        [ ESSExportDefault
          { stmt = ESSFunDecl
            { id = nameSym "main", params = [runtimeEnv], body = stmts } } ] }
    , setToSeq ctx.runtime )

end
