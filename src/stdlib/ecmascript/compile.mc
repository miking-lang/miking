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

-- Orders record fields for output. Tuple fields are named "0", "1", ... and
-- should read in numeric order rather than the lexicographic one that would
-- put "10" before "2". `mapBindings` order is by interned SID, which is
-- essentially arbitrary, so sorting also makes output stable.
let esCmpFieldName : String -> String -> Int = lam a. lam b.
  if and (stringIsInt a) (stringIsInt b)
  then subi (string2int a) (string2int b)
  else cmpString a b

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

  -- Reads one field. Tuple fields are named "0", "1", ... which cannot be
  -- written with a dot.
  sem esVar : Name -> ESExpr
  sem esVar = | id -> ESEVar { id = id }

  sem esArrow1 : Name -> ESExpr -> ESExpr
  sem esArrow1 p = | body ->
    ESEArrow { params = [p], body = ESFBExpr { expr = body } }

  sem esArrow2 : Name -> Name -> ESExpr -> ESExpr
  sem esArrow2 p q = | body ->
    ESEArrow { params = [p, q], body = ESFBExpr { expr = body } }

  -- Calls an effect on the runtime environment with the sequence converted to
  -- a JS string.
  sem esEnvStr : ESCompileCtx -> String -> [ESExpr] -> (ESCompileCtx, ESExpr)
  sem esEnvStr ctx field =
  | args ->
    ({ ctx with runtime = setInsert "$jsStr" ctx.runtime }
    , ESECall { callee = esMember (ESEVar { id = ctx.runtimeEnv }) field
              , args = [ESECall { callee = ESEGlobal { name = "$jsStr" }
                                , args = args }] })

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
      ({ ctx with runtime = setInsert "$S" ctx.runtime }, []
      , ESECall { callee = ESEGlobal { name = "$S" }
                , args = [ESEString { value = map esCharConstVal t.tms }] })
    else
      match compileExprs ctx t.tms with (ctx, stmts, xs) in
      (ctx, stmts, ESEArray { exprs = xs })
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
  | CChar2Int _ | CInt2Char _ | CDPrint _
  | CLength _ | CHead _ | CTail _ | CNull _ | CReverse _
  | CIsList _ | CIsRope _
  | CPrint _ | CPrintError _ | CFlushStdout _
  | CFloat2string _ | CString2float _ | CStringIsFloat _ -> Some 1
  | CGet _ | CCons _ | CSnoc _ | CConcat _ | CSplitAt _
  | CMap _ | CMapi _ | CIter _ | CIteri _
  | CCreate _ | CCreateList _ | CCreateRope _ -> Some 2
  | CSet _ | CFoldl _ | CFoldr _ | CSubsequence _ -> Some 3
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

    -- Sequences are arrays, so most operations are plain JS idioms. Only the
    -- ones needing a copy, a clamp, or a pair go through the runtime.
    case CLength _ then match args with [s] in (ctx, esMember s "length")
    case CGet _ then
      match args with [s, i] in (ctx, ESEIndex { obj = s, index = i })
    case CHead _ then
      match args with [s] in
      (ctx, ESEIndex { obj = s, index = ESEInt { value = 0 } })
    case CTail _ then
      match args with [s] in
      (ctx, ESECall { callee = esMember s "slice"
                    , args = [ESEInt { value = 1 }] })
    case CNull _ then
      match args with [s] in
      (ctx, ESEBin { op = ESOEq {}, lhs = esMember s "length"
                   , rhs = ESEInt { value = 0 } })
    case CConcat _ then
      match args with [a, b] in
      (ctx, ESECall { callee = esMember a "concat", args = [b] })
    case CCons _ then
      match args with [v, s] in
      (ctx, ESEArray { exprs = [v, ESEUn { op = ESOSpread {}, arg = s }] })
    case CSnoc _ then
      match args with [s, v] in
      (ctx, ESEArray { exprs = [ESEUn { op = ESOSpread {}, arg = s }, v] })
    case CReverse _ then
      match args with [s] in
      (ctx, ESECall
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
      (ctx, ESECall { callee = esMember s "map", args = [f] })
    case CMapi _ then
      match args with [f, s] in
      let x = nameSym "_x" in let i = nameSym "_i" in
      (ctx, ESECall { callee = esMember s "map"
        , args = [esArrow2 x i (ESECall
            { callee = ESECall { callee = f, args = [esVar i] }
            , args = [esVar x] })] })
    case CIter _ then
      match args with [f, s] in
      (ctx, ESECall { callee = esMember s "forEach", args = [f] })
    case CIteri _ then
      match args with [f, s] in
      let x = nameSym "_x" in let i = nameSym "_i" in
      (ctx, ESECall { callee = esMember s "forEach"
        , args = [esArrow2 x i (ESECall
            { callee = ESECall { callee = f, args = [esVar i] }
            , args = [esVar x] })] })
    case CFoldl _ then
      match args with [f, acc, s] in
      let a = nameSym "_a" in let x = nameSym "_x" in
      (ctx, ESECall { callee = esMember s "reduce"
        , args = [esArrow2 a x (ESECall
            { callee = ESECall { callee = f, args = [esVar a] }
            , args = [esVar x] }), acc] })
    case CFoldr _ then
      match args with [f, acc, s] in
      let a = nameSym "_a" in let x = nameSym "_x" in
      (ctx, ESECall { callee = esMember s "reduceRight"
        , args = [esArrow2 a x (ESECall
            { callee = ESECall { callee = f, args = [esVar x] }
            , args = [esVar a] }), acc] })
    -- This backend has a single sequence representation, so the two
    -- representation predicates answer uniformly.
    case CIsList _ then (ctx, ESEBool { value = false })
    case CIsRope _ then (ctx, ESEBool { value = true })
    case CSet _ then rt "$set"
    case CSplitAt _ then rt "$splitAt"
    case CSubsequence _ then rt "$subsequence"
    case CCreate _ | CCreateList _ | CCreateRope _ then rt "$create"

    -- Effects reach the host as ordinary JS strings, so it never has to know
    -- how `[Char]` is represented.
    case CPrint _ then esEnvStr ctx "print" args
    case CPrintError _ then esEnvStr ctx "printError" args
    case CFlushStdout _ then
      (ctx, ESECall
        { callee = esMember (ESEVar { id = ctx.runtimeEnv }) "flushStdout"
        , args = [] })
    case CFloat2string _ then rt "$float2string"
    case CString2float _ then rt "$string2float"
    case CStringIsFloat _ then rt "$stringIsFloat"
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
