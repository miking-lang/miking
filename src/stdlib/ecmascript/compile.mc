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
include "ecmascript/ident.mc"
include "map.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/const-arity.mc"
include "mexpr/info.mc"
-- Only for `getConstStringCode`, which names constants in error messages.
include "mexpr/pprint.mc"
include "name.mc"
include "seq.mc"
include "set.mc"
include "stringid.mc"

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

  -- Types that were emitted as a base class, so a constructor knows whether
  -- it has a base to extend or must carry the payload itself.
  variants : Set Name,

  -- The function currently being compiled and its parameters, when a
  -- saturated self-call in tail position can become a loop rather than
  -- recursion. Cleared inside nested functions.
  selfCall : Option (Name, [Name])
}

let esCompileCtxEmpty : ESCompileCtx = {
  runtimeEnv = nameNoSym "env",
  arities = mapEmpty nameCmp,
  variants = setEmpty nameCmp,
  selfCall = None ()
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

-- Orders record fields for output. Tuple fields are named "0", "1", ... and
-- should read in numeric order rather than the lexicographic one that would
-- put "10" before "2". `mapBindings` order is by interned SID, which is
-- essentially arbitrary, so sorting also makes output stable.
let esCmpFieldName : String -> String -> Int = lam a. lam b.
  if and (stringIsInt a) (stringIsInt b)
  then subi (string2int a) (string2int b)
  else cmpString a b

lang MExprESCompile = MExprAst + ESAst + MExprPrettyPrint + MExprArity

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

  -- Reads one field. Tuple fields are named "0", "1", ... which cannot be
  -- written with a dot.
  -- The type a constructor belongs to: strip the quantifiers, take the
  -- arrow's codomain, and strip any type arguments to reach its name.
  sem esConCodomain : Type -> Option Name
  sem esConCodomain =
  | TyAll t -> esConCodomain t.ty
  | TyArrow t -> esTyConName t.to
  | _ -> None ()

  sem esTyConName : Type -> Option Name
  sem esTyConName =
  | TyCon t -> Some t.ident
  | TyApp t -> esTyConName t.lhs
  | TyAll t -> esTyConName t.ty
  | _ -> None ()

  -- Whether a `continue` was emitted for the function being compiled. Nested
  -- functions run their own loops, so their bodies are not searched.
  sem esHasContinue : [ESStmt] -> Bool
  sem esHasContinue =
  | stmts -> any esStmtHasContinue stmts

  sem esStmtHasContinue : ESStmt -> Bool
  sem esStmtHasContinue =
  | ESSContinue _ -> true
  | ESSIf t -> or (esHasContinue t.thn) (esHasContinue t.els)
  | ESSBlock t -> esHasContinue t.stmts
  | ESSExportDefault t -> esStmtHasContinue t.stmt
  | _ -> false

  sem esVar : Name -> ESExpr
  sem esVar = | id -> ESEVar { id = id }

  sem esArrow1 : Name -> ESExpr -> ESExpr
  sem esArrow1 p = | body ->
    ESEArrow { params = [p], body = ESFBExpr { expr = body } }

  sem esArrow2 : Name -> Name -> ESExpr -> ESExpr
  sem esArrow2 p q = | body ->
    ESEArrow { params = [p, q], body = ESFBExpr { expr = body } }

  sem esIsCharConst : Expr -> Bool
  sem esIsCharConst =
  | TmConst { val = CChar _ } -> true
  | _ -> false

  sem esCharConstVal : Expr -> Char
  sem esCharConstVal =
  | TmConst { val = CChar c } -> c.val
  | _ -> error "esCharConstVal: not a character literal"

  sem esField : ESExpr -> String -> ESExpr
  sem esField obj =
  | key ->
    if esIsIdentLike key then ESEMember { obj = obj, prop = key }
    else if stringIsInt key then
      ESEIndex { obj = obj, index = ESEInt { value = string2int key } }
    else ESEIndex { obj = obj, index = ESEString { value = key } }

  sem esAnd : ESExpr -> ESExpr -> ESExpr
  sem esAnd lhs =
  | rhs ->
    if esIsTrue lhs then rhs
    else if esIsTrue rhs then lhs
    else ESEBin { op = ESOAnd {}, lhs = lhs, rhs = rhs }

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
  | TmDecl t ->
    -- The whole point: a declaration becomes a sibling statement, not a scope.
    match esCompileDecl ctx t.decl with (ctx, decls) in
    match compileStmts ctx cont t.inexpr with (ctx, rest) in
    (ctx, concat decls rest)
  | TmMatch t ->
    match compileExpr ctx t.target with (ctx, s0, target) in
    match esPatCompile ctx target t.pat with (ctx, pre, test, binds) in
    let s0 = concat s0 pre in
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
  | TmApp _ & t ->
    -- A saturated self-call in tail position: rebind the parameters and jump
    -- back to the top rather than recursing.
    match (cont, ctx.selfCall) with (ESCReturn _, Some (fname, params)) then
      match esCollectApp t with (fn, args) in
      match fn with TmVar v then
        if and (nameEq v.ident fname) (eqi (length args) (length params)) then
          esTailCall ctx params args
        else esCompileToCont ctx cont t
      else esCompileToCont ctx cont t
    else esCompileToCont ctx cont t
  | t -> esCompileToCont ctx cont t

  sem esCompileToCont : ESCompileCtx -> ESCont -> Expr -> (ESCompileCtx, [ESStmt])
  sem esCompileToCont ctx cont =
  | t ->
    match compileExpr ctx t with (ctx, stmts, expr) in
    (ctx, concat stmts (esDeliver cont expr))

  -- Parameters are rebound simultaneously, so with more than one they go
  -- through temporaries first: assigning in sequence would let a later
  -- argument see an already-updated parameter.
  sem esTailCall
    : ESCompileCtx -> [Name] -> [Expr] -> (ESCompileCtx, [ESStmt])
  sem esTailCall ctx params =
  | args ->
    match compileExprs ctx args with (ctx, stmts, xs) in
    match params with [p] then
      (ctx, join [stmts
        , [ESSAssign { target = ESEVar { id = p }, value = head xs }]
        , [ESSContinue {}]])
    else
      let temps = map (lam. nameSym "_arg") params in
      let binds = zipWith (lam n. lam x. ESSConst { id = n, init = x }) temps xs in
      let assigns = zipWith (lam p. lam n.
          ESSAssign { target = ESEVar { id = p }, value = ESEVar { id = n } })
        params temps in
      (ctx, join [stmts, binds, assigns, [ESSContinue {}]])

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
    else
      let ps = create (constArity t.val) (lam. nameSym "a") in
      match esConstApplyWith ctx (map (lam p. ESEVar { id = p }) ps) t.val
        with Some (ctx, body) then
        (ctx, [], esCurryArrows ps body)
      else errorSingle [infoTm e] (concat
        "ecmascript: unsupported constant: " (getConstStringCode 0 t.val))
  | TmLam _ & t ->
    -- An anonymous lambda's arity is not tracked anywhere, so whoever receives
    -- it will apply one argument at a time: emit curried arrows.
    --
    -- Entering a new function also ends the enclosing function's tail
    -- position. Without clearing it, a self-call inside this lambda would emit
    -- a `continue` belonging to a loop it is not inside.
    match esCollectLams t with (params, body) in
    let outer = ctx.selfCall in
    let ctx = { ctx with selfCall = None () } in
    match compileStmts ctx (ESCReturn ()) body with (ctx, stmts) in
    let ctx = { ctx with selfCall = outer } in
    -- A lone `return e;` reads better as a concise arrow body.
    let innerBody = match stmts with [ESSReturn { expr = Some e }]
      then ESFBExpr { expr = e } else ESFBBlock { stmts = stmts } in
    match splitAt params (subi (length params) 1) with (outer, [innermost]) in
    (ctx, [], esCurryArrows outer
      (ESEArrow { params = [innermost], body = innerBody }))
  | TmDecl t ->
    -- Hoist the declaration out in front of the expression that needs it.
    -- Sound because a hoist never crosses a conditional: `TmMatch` in
    -- expression position keeps each branch's statements inside its own arm.
    match esCompileDecl ctx t.decl with (ctx, decls) in
    match compileExpr ctx t.inexpr with (ctx, stmts, expr) in
    (ctx, concat decls stmts, expr)
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
    match esPatCompile ctx target t.pat with (ctx, pre, test, binds) in
    let s0 = concat s0 pre in
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
        let tmp = nameSym "_v" in
        (ctx
        , join [s0, [ESSLet { id = tmp, init = None () }]
          , [ESSIf { cond = test
                   , thn = join [binds, sThn, esDeliver (ESCAssign tmp) eThn]
                   , els = concat sEls (esDeliver (ESCAssign tmp) eEls) }]]
        , ESEVar { id = tmp })
  | TmNever t ->
    (ctx, [esThrow t.info "ecmascript: reached a `never` expression"], esUnit)
  | TmSeq t ->
    -- A sequence of character literals is a string. `$S` spreads a JS string
    -- literal, which iterates by codepoint, so the result reads as text in the
    -- output while staying an ordinary array at runtime.
    if and (not (null t.tms)) (forAll esIsCharConst t.tms) then
      (ctx, []
      , ESECall { callee = ESEGlobal { name = "$S" }
                , args = [ESEString { value = map esCharConstVal t.tms }] })
    else
      match compileExprs ctx t.tms with (ctx, stmts, xs) in
      (ctx, stmts, ESEArray { exprs = xs })
  | TmConApp t ->
    match compileExpr ctx t.body with (ctx, stmts, body) in
    (ctx, stmts, ESENew { callee = ESEVar { id = t.ident }, args = [body] })
  | TmRecord t ->
    -- The empty record is MExpr's unit value.
    if mapIsEmpty t.bindings then (ctx, [], esUnit)
    else
      let fields = sort (lam a. lam b. esCmpFieldName a.0 b.0)
        (map (lam b. (sidToString b.0, b.1)) (mapBindings t.bindings)) in
      match compileExprs ctx (map (lam f. f.1) fields) with (ctx, stmts, xs) in
      (ctx, stmts, ESEObject
        { fields = zipWith (lam f. lam x. (f.0, x)) fields xs })
  | TmRecordUpdate t ->
    match compileExpr ctx t.rec with (ctx, s0, rec) in
    match compileExpr ctx t.value with (ctx, s1, value) in
    (ctx, concat s0 s1, ESEObjectWith
      { base = rec, fields = [(sidToString t.key, value)] })
  | t ->
    errorSingle [infoTm t] (concat
      "ecmascript: unsupported expression: " (esExprName t))

  -- Compiles a named function. A saturated self-call in tail position becomes
  -- a jump back to the top of the body, so self-recursion runs in constant
  -- stack; if any such jump was emitted the body is wrapped in a loop.
  sem esCompileFun
    : ESCompileCtx -> Name -> [Name] -> Expr -> (ESCompileCtx, ESStmt)
  sem esCompileFun ctx id params =
  | body ->
    let outer = ctx.selfCall in
    let ctx = { ctx with selfCall = Some (id, params) } in
    match compileStmts ctx (ESCReturn ()) body with (ctx, stmts) in
    let ctx = { ctx with selfCall = outer } in
    let stmts =
      if esHasContinue stmts
      then [ESSWhile { cond = ESEBool { value = true }, body = stmts }]
      else stmts in
    (ctx, ESSFunDecl { id = id, params = params, body = stmts })

  -- Compiles one declaration to the statements that introduce it. Shared by
  -- both compilation modes, so a declaration behaves the same whether it is
  -- reached in statement or expression position.
  sem esCompileDecl : ESCompileCtx -> Decl -> (ESCompileCtx, [ESStmt])
  sem esCompileDecl ctx =
  | DeclType d ->
    -- A datatype becomes a base class carrying the payload; a type alias is
    -- erased entirely.
    match d.tyIdent with TyVariant _ then
      ({ ctx with variants = setInsert d.ident ctx.variants }
      , [ESSClass { id = d.ident, extends = None () }])
    else (ctx, [])
  | DeclConDef d ->
    -- Extending the type's class is what records, in the output, that these
    -- constructors belong together -- MExpr datatypes are open, so they can be
    -- declared far from the type. A constructor whose type has no emitted base
    -- carries the payload itself.
    let base = match esConCodomain d.tyIdent with Some ty then
      (if setMem ty ctx.variants then Some ty else None ()) else None () in
    (ctx, [ESSClass { id = d.ident, extends = base }])
  | DeclRecLets d ->
    -- Every arity is recorded before any body is compiled, so calls within the
    -- group are n-ary in both directions. JS hoists function declarations, so
    -- mutual recursion needs no ordering care.
    let ctx = foldl (lam ctx. lam b.
        match b.body with TmLam _ then
          match esCollectLams b.body with (params, _) in
          { ctx with arities = mapInsert b.ident (length params) ctx.arities }
        else ctx)
      ctx d.bindings in
    let step = lam acc. lam b.
      match acc with (ctx, stmts) in
      match b.body with TmLam _ then
        match esCollectLams b.body with (params, body) in
        match esCompileFun ctx b.ident params body with (ctx, decl) in
        (ctx, snoc stmts decl)
      else errorSingle [b.info]
        "ecmascript: a recursive binding must be a function"
    in
    foldl step (ctx, []) d.bindings
  | decl & !(DeclLet _) ->
    errorSingle [infoDecl decl] (concat
      "ecmascript: unsupported declaration: " (esDeclName decl))
  | DeclLet d ->
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
      match esCompileFun ctx d.ident params body with (ctx, decl) in
      let ctx = { ctx with
        arities = mapInsert d.ident (length params) ctx.arities } in
      (ctx, [decl])
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

  -- Returns statements to run *before* the test, the test itself, and the
  -- statements that bind the pattern's names once it has succeeded.
  --
  -- After pattern lowering sub-patterns are names or wildcards, but the record
  -- case recurses anyway so that a refutable field pattern would still be
  -- handled correctly rather than silently mis-compiled.
  sem esPatCompile
    : ESCompileCtx -> ESExpr -> Pat -> (ESCompileCtx, [ESStmt], ESExpr, [ESStmt])
  sem esPatCompile ctx target =
  | PatNamed { ident = PName n } ->
    (ctx, [], esTrue (), [ESSConst { id = n, init = target }])
  | PatNamed { ident = PWildcard _ } -> (ctx, [], esTrue (), [])
  | PatInt t ->
    (ctx, [], ESEBin { op = ESOEq {}, lhs = target, rhs = ESEInt { value = t.val } }, [])
  | PatChar t ->
    (ctx, [], ESEBin { op = ESOEq {}, lhs = target
                     , rhs = ESEString { value = [t.val] } }, [])
  | PatBool t ->
    (ctx, [], (if t.val then target else ESEUn { op = ESONot {}, arg = target }), [])
  | PatRecord t ->
    let fields = sort (lam a. lam b. esCmpFieldName a.0 b.0)
      (map (lam b. (sidToString b.0, b.1)) (mapBindings t.bindings)) in
    -- The empty record pattern matches unit, and binds nothing.
    if null fields then (ctx, [], esTrue (), [])
    else
      -- Reading more than one field out of a computed target would evaluate
      -- that target once per field, so bind it first.
      match (if gti (length fields) 1 then esPatTarget ctx target
             else (target, [])) with (obj, pre) in
      let step = lam acc. lam f.
        match acc with (ctx, pre, test, binds) in
        match esPatCompile ctx (esField obj f.0) f.1 with (ctx, p, t, b) in
        (ctx, concat pre p, esAnd test t, concat binds b)
      in
      foldl step (ctx, pre, esTrue (), []) fields
  | PatCon t ->
    -- Each constructor is its own class, so matching is an `instanceof`, and
    -- the payload is the single field the base class holds. The target is read
    -- twice, so a computed one is bound first.
    match esPatTarget ctx target with (obj, pre) in
    match esPatCompile ctx (esMember obj "v") t.subpat with (ctx, pre2, sub, binds) in
    ( ctx, concat pre pre2
    , esAnd (ESEInstanceOf { lhs = obj, rhs = ESEVar { id = t.ident } }) sub
    , binds )
  | PatSeqTot t ->
    match esPatTarget ctx target with (obj, pre) in
    let n = length t.pats in
    let test = ESEBin { op = ESOEq {}
                      , lhs = esMember obj "length"
                      , rhs = ESEInt { value = n } } in
    let step = lam acc. lam ip.
      match acc with (ctx, i, binds) in
      match esPatCompile ctx (ESEIndex { obj = obj, index = ESEInt { value = i } }) ip
        with (ctx, _, t2, b2) in
      -- After lowering these sub-patterns only bind, so any test they produce
      -- would be `true`; a refutable one would need `test` extending instead.
      (ctx, addi i 1, concat binds b2)
    in
    match foldl step (ctx, 0, []) t.pats with (ctx, _, binds) in
    (ctx, pre, test, binds)
  | PatSeqEdge t ->
    match esPatTarget ctx target with (obj, pre) in
    let np = length t.prefix in
    let ns = length t.postfix in
    let len = esMember obj "length" in
    let test = ESEBin { op = ESOGe {}, lhs = len
                      , rhs = ESEInt { value = addi np ns } } in
    -- Prefix elements count from the front, postfix from the back, and the
    -- middle is whatever is left between them.
    let front = lam acc. lam ip.
      match acc with (ctx, i, binds) in
      match esPatCompile ctx (ESEIndex { obj = obj, index = ESEInt { value = i } }) ip
        with (ctx, _, _, b) in
      (ctx, addi i 1, concat binds b)
    in
    match foldl front (ctx, 0, []) t.prefix with (ctx, _, binds) in
    let back = lam acc. lam ip.
      match acc with (ctx, i, binds) in
      let idx = ESEBin { op = ESOSub {}, lhs = len
                       , rhs = ESEInt { value = subi ns i } } in
      match esPatCompile ctx (ESEIndex { obj = obj, index = idx }) ip
        with (ctx, _, _, b) in
      (ctx, addi i 1, concat binds b)
    in
    match foldl back (ctx, 0, binds) t.postfix with (ctx, _, binds) in
    match t.middle with PName m then
      let mid = ESECall { callee = esMember obj "slice"
        , args = [ ESEInt { value = np }
                 , ESEBin { op = ESOSub {}, lhs = len, rhs = ESEInt { value = ns } }] } in
      (ctx, pre, test, snoc binds (ESSConst { id = m, init = mid }))
    else (ctx, pre, test, binds)
  | p ->
    errorSingle [infoPat p] (concat
      "ecmascript: unsupported pattern: " (esPatName p))

  -- Binds a target that is not already a variable, so that a pattern reading
  -- it more than once does not re-evaluate it.
  sem esPatTarget : ESCompileCtx -> ESExpr -> (ESExpr, [ESStmt])
  sem esPatTarget ctx =
  | ESEVar _ & e -> (e, [])
  | ESEGlobal _ & e -> (e, [])
  | e ->
    let tmp = nameSym "_s" in
    (ESEVar { id = tmp }, [ESSConst { id = tmp, init = e }])

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


  -- Builds the expression for an operation applied to exactly its arity, or
  -- `None` if this backend does not implement it.
  sem esConstApplyWith
    : ESCompileCtx -> [ESExpr] -> Const -> Option (ESCompileCtx, ESExpr)
  sem esConstApplyWith ctx args =
  | const ->
    let bin = lam op.
      match args with [a, b] in Some (ctx, ESEBin { op = op, lhs = a, rhs = b }) in
    let un = lam op.
      match args with [a] in Some (ctx, ESEUn { op = op, arg = a }) in
    let math = lam f.
      match args with [a] in
      Some (ctx, ESECall
        { callee = esMember (ESEGlobal { name = "Math" }) f, args = [a] }) in
    -- Calls a runtime helper with the arguments as given.
    let rt = lam name.
      Some (ctx
           , ESECall { callee = ESEGlobal { name = name }, args = args }) in
    -- Calls an effect on the runtime environment with the arguments as given.
    let env = lam field.
      Some (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) field
        , args = args }) in
    -- ... with every `[Char]` argument converted to a JS string first, so a
    -- host never sees the internal representation.
    let envStr = lam field.
      Some (ctx
      , ESECall
             { callee = esMember (ESEVar { id = ctx.runtimeEnv }) field
             , args = map (lam a. ESECall
                 { callee = ESEGlobal { name = "$jsStr" }, args = [a] }) args }) in
    -- ... and the result converted back.
    let envStrOut = lam field.
      match envStr field with Some (ctx, call) in
      Some (ctx
      , ESECall { callee = ESEGlobal { name = "$S" }, args = [call] }) in
    switch const
    -- Integer arithmetic. `divi` truncates towards zero, as OCaml does.
    case CAddi _ then bin (ESOAdd {})
    case CSubi _ then bin (ESOSub {})
    case CMuli _ then bin (ESOMul {})
    case CDivi _ then
      match args with [a, b] in
      Some (ctx, ESECall { callee = esMember (ESEGlobal { name = "Math" }) "trunc"
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
    case CInt2float _ then match args with [a] in Some (ctx, a)
    case CFloorfi _ then math "floor"
    case CCeilfi _ then math "ceil"
    -- `Math.round` rounds half towards +Infinity; OCaml rounds half away from
    -- zero, so they disagree on every negative half.
    case CRoundfi _ then rt "$roundfi"
    -- Chars are one-character strings.
    case CEqc _ then bin (ESOEq {})
    case CChar2Int _ then
      match args with [a] in
      Some (ctx, ESECall { callee = esMember a "codePointAt", args = [ESEInt { value = 0 }] })
    case CInt2Char _ then
      match args with [a] in
      Some (ctx, ESECall
        { callee = esMember (ESEGlobal { name = "String" }) "fromCodePoint"
        , args = [a] })
    case CDPrint _ then
      Some (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "dprint", args = args })

    -- Sequences are arrays, so most operations are plain JS idioms. Only the
    -- ones needing a copy, a clamp, or a pair go through the runtime.
    case CLength _ then match args with [s] in Some (ctx, esMember s "length")
    case CGet _ then
      match args with [s, i] in Some (ctx, ESEIndex { obj = s, index = i })
    case CHead _ then
      match args with [s] in
      Some (ctx, ESEIndex { obj = s, index = ESEInt { value = 0 } })
    case CTail _ then
      match args with [s] in
      Some (ctx, ESECall { callee = esMember s "slice"
                    , args = [ESEInt { value = 1 }] })
    case CNull _ then
      match args with [s] in
      Some (ctx, ESEBin { op = ESOEq {}, lhs = esMember s "length"
                   , rhs = ESEInt { value = 0 } })
    case CConcat _ then
      match args with [a, b] in
      Some (ctx, ESECall { callee = esMember a "concat", args = [b] })
    case CCons _ then
      match args with [v, s] in
      Some (ctx, ESEArray { exprs = [v, ESEUn { op = ESOSpread {}, arg = s }] })
    case CSnoc _ then
      match args with [s, v] in
      Some (ctx, ESEArray { exprs = [ESEUn { op = ESOSpread {}, arg = s }, v] })
    case CReverse _ then
      match args with [s] in
      Some (ctx, ESECall
        { callee = esMember
            (ESEArray { exprs = [ESEUn { op = ESOSpread {}, arg = s }] }) "reverse"
        , args = [] })
    -- Every function value this backend produces takes exactly one parameter,
    -- so `map` and `iter` can hand theirs straight to the JS method and let it
    -- ignore the extra index and array arguments. The indexed and folding
    -- forms still need a wrapper, because MExpr curries them and `foldr` takes
    -- its arguments in the opposite order to `reduceRight`.
    case CMap _ then
      match args with [f, s] in
      Some (ctx, ESECall { callee = esMember s "map", args = [f] })
    case CMapi _ then
      match args with [f, s] in
      let x = nameSym "_x" in let i = nameSym "_i" in
      Some (ctx, ESECall { callee = esMember s "map"
        , args = [esArrow2 x i (ESECall
            { callee = ESECall { callee = f, args = [esVar i] }
            , args = [esVar x] })] })
    case CIter _ then
      match args with [f, s] in
      Some (ctx, ESECall { callee = esMember s "forEach", args = [f] })
    case CIteri _ then
      match args with [f, s] in
      let x = nameSym "_x" in let i = nameSym "_i" in
      Some (ctx, ESECall { callee = esMember s "forEach"
        , args = [esArrow2 x i (ESECall
            { callee = ESECall { callee = f, args = [esVar i] }
            , args = [esVar x] })] })
    case CFoldl _ then
      match args with [f, acc, s] in
      let a = nameSym "_a" in let x = nameSym "_x" in
      Some (ctx, ESECall { callee = esMember s "reduce"
        , args = [esArrow2 a x (ESECall
            { callee = ESECall { callee = f, args = [esVar a] }
            , args = [esVar x] }), acc] })
    case CFoldr _ then
      match args with [f, acc, s] in
      let a = nameSym "_a" in let x = nameSym "_x" in
      Some (ctx, ESECall { callee = esMember s "reduceRight"
        , args = [esArrow2 a x (ESECall
            { callee = ESECall { callee = f, args = [esVar x] }
            , args = [esVar a] }), acc] })
    -- This backend has a single sequence representation, so the two
    -- representation predicates answer uniformly.
    case CIsList _ then Some (ctx, ESEBool { value = false })
    case CIsRope _ then Some (ctx, ESEBool { value = true })
    case CSet _ then rt "$set"
    case CSplitAt _ then rt "$splitAt"
    case CSubsequence _ then rt "$subsequence"
    case CCreate _ | CCreateList _ | CCreateRope _ then rt "$create"

    -- Effects reach the host as ordinary JS strings, so it never has to know
    -- how `[Char]` is represented.
    case CPrint _ then envStr "print"
    case CPrintError _ then envStr "printError"
    case CFlushStdout _ then
      Some (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "flushStdout"
        , args = [] })
    case CFloat2string _ then rt "$float2string"
    case CString2float _ then rt "$string2float"
    case CStringIsFloat _ then rt "$stringIsFloat"
    -- Symbols are integers from a counter, so equality is `===` and the hash
    -- is the identity.
    case CGensym _ then
      Some (ctx
      , ESECall { callee = ESEGlobal { name = "$gensym" }, args = [] })
    case CSym2hash _ then match args with [a] in Some (ctx, a)
    case CEqsym _ then bin (ESOEq {})

    -- References. The standard library builds these out of rank-0 tensors
    -- instead, so these intrinsics are rarely reached.
    case CRef _ then rt "$ref"
    case CDeRef _ then match args with [r] in Some (ctx, esMember r "v")
    case CModRef _ then rt "$modref"

    case CConstructorTag _ then rt "$conTag"
    case CUnsafeCoerce _ then match args with [a] in Some (ctx, a)

    -- Effects reach the host as ordinary JS strings.
    case CExit _ then env "exit"
    case CError _ then envStr "error"
    case CArgv _ then
      Some (ctx
      , ESECall
             { callee = esMember (ESECall
                 { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "argv"
                 , args = [] }) "map"
             , args = [ESEGlobal { name = "$S" }] })
    case CCommand _ then envStr "command"
    case CFileRead _ then envStrOut "readFile"
    case CFileWrite _ then envStr "writeFile"
    case CFileExists _ then envStr "fileExists"
    case CFileDelete _ then envStr "deleteFile"
    case CFlushStderr _ then
      Some (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "flushStderr"
        , args = [] })
    case CReadLine _ then
      Some (ctx
      , ESECall { callee = ESEGlobal { name = "$S" }
                     , args = [ESECall
                         { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "readLine"
                         , args = [] }] })
    case CWallTimeMs _ then
      Some (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "wallTimeMs"
        , args = [] })
    case CSleepMs _ then env "sleepMs"
    case CRandIntU _ then env "randIntU"
    case CRandSetSeed _ then env "randSetSeed"

    -- Tensors. The two element-type families collapse into one dense
    -- representation here.
    case CTensorCreate _ | CTensorCreateInt _ | CTensorCreateFloat _ then
      rt "$tCreate"
    case CTensorCreateUninitInt _ | CTensorCreateUninitFloat _ then rt "$tUninit"
    case CTensorGetExn _ then rt "$tGet"
    case CTensorSetExn _ then rt "$tSet"
    case CTensorLinearGetExn _ then rt "$tLinGet"
    case CTensorLinearSetExn _ then rt "$tLinSet"
    case CTensorRank _ then match args with [t] in Some (ctx, esMember t "rank")
    case CTensorShape _ then match args with [t] in Some (ctx, esMember t "shape")
    case CTensorReshapeExn _ then rt "$tReshape"
    case CTensorSliceExn _ then rt "$tSlice"
    case CTensorSubExn _ then rt "$tSub"
    case CTensorCopy _ then rt "$tCopy"
    case CTensorIterSlice _ then rt "$tIterSlice"
    case CTensorEq _ then rt "$tEq"
    case CTensorTransposeExn _ then rt "$tTranspose"
    case CTensorToString _ then rt "$tToString"

    case _ then None ()
    end

  sem compileConstApp
    : ESCompileCtx -> Info -> Const -> [Expr] -> (ESCompileCtx, [ESStmt], ESExpr)
  sem compileConstApp ctx info const =
  | args ->
    let arity = constArity const in
    match compileExprs ctx args with (ctx, stmts, xs) in
    let n = length xs in
    let unsupported = lam.
      errorSingle [info] (concat
        "ecmascript: unsupported constant: " (getConstStringCode 0 const)) in
    if lti n arity then
      -- Partial application: eta-expand into a curried closure.
      let extra = create (subi arity n) (lam. nameSym "a") in
      match esConstApplyWith ctx
        (concat xs (map (lam p. ESEVar { id = p }) extra)) const
        with Some (ctx, body) then
        (ctx, stmts, esCurryArrows extra body)
      else unsupported ()
    else
      match esConstApplyWith ctx (subsequence xs 0 arity) const
        with Some (ctx, e) then
        (ctx, stmts, esCurryApply e (subsequence xs arity (subi n arity)))
      else unsupported ()

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

  -- Wraps a compiled program in `export default function main(env) { ... }`.
  --
  -- The top-level expression is discarded rather than returned: in practice it
  -- is the program's final effect and has unit type, and `env.print(x);` reads
  -- better than `return env.print(x);`.
  sem compileESProg : Expr -> ESProg
  sem compileESProg =
  | ast ->
    let runtimeEnv = nameSym "env" in
    let ctx = { esCompileCtxEmpty with runtimeEnv = runtimeEnv } in
    match compileStmts ctx (ESCDiscard ()) ast with (_, stmts) in
    ESProg
    { imports = []
    , stmts =
      [ ESSExportDefault
        { stmt = ESSFunDecl
          { id = nameSym "main", params = [runtimeEnv], body = stmts } } ] }

end
