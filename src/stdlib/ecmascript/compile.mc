-- Compilation of MExpr to the ECMAScript AST.
--
-- The compiler works in two modes, which is what keeps a chain of `let ... in`
-- bindings flat instead of nesting one function scope per binding:
--
--   * `compileStmts` is *statement* mode. It knows where the value of the
--     expression is going -- via an `ESCont` -- and returns a flat statement
--     list. A `TmDecl` spine simply concatenates.
--
--   * `compileExpr` is *expression* mode. It returns an expression plus any
--     statements that must run before it, so bindings encountered in
--     expression position are hoisted into the enclosing statement list rather
--     than wrapped in an immediately-invoked function.

include "ecmascript/ast.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/info.mc"
-- Only for `getConstStringCode`, which names constants in error messages.
include "mexpr/pprint.mc"
include "name.mc"
include "seq.mc"

-- Where the value produced by a term should go.
type ESCont
con ESCReturn : () -> ESCont    -- `return <e>;`
con ESCBind : Name -> ESCont    -- `const x = <e>;`
con ESCDiscard : () -> ESCont   -- `<e>;`

type ESCompileCtx = {
  -- The name bound to the runtime environment parameter of the generated
  -- `main` function. Effectful intrinsics compile to member access on it, so
  -- that a caller supplies them on every execution.
  runtimeEnv : Name
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

lang MExprESCompile = MExprAst + ESAst + MExprPrettyPrint

  -- Emits the statement that delivers `expr` to its destination.
  sem esDeliver : ESCont -> ESExpr -> [ESStmt]
  sem esDeliver cont =
  | expr ->
    switch cont
    case ESCReturn _ then [ESSReturn { expr = Some expr }]
    case ESCBind id then [ESSConst { id = id, init = expr }]
    case ESCDiscard _ then [ESSExpr { expr = expr }]
    end

  ---------------------
  -- STATEMENT MODE --
  ---------------------

  sem compileStmts : ESCompileCtx -> ESCont -> Expr -> (ESCompileCtx, [ESStmt])
  sem compileStmts ctx cont =
  | TmDecl { decl = DeclLet d, inexpr = inexpr } ->
    -- The whole point: a binding becomes a sibling statement, not a new scope.
    match compileStmts ctx (ESCBind d.ident) d.body with (ctx, bind) in
    match compileStmts ctx cont inexpr with (ctx, rest) in
    (ctx, concat bind rest)
  | TmDecl { decl = decl } & t ->
    errorSingle [infoTm t] (concat
      "ecmascript: unsupported declaration: " (esDeclName decl))
  | t ->
    match compileExpr ctx t with (ctx, stmts, expr) in
    (ctx, concat stmts (esDeliver cont expr))

  ----------------------
  -- EXPRESSION MODE --
  ----------------------

  sem compileExpr : ESCompileCtx -> Expr -> (ESCompileCtx, [ESStmt], ESExpr)
  sem compileExpr ctx =
  | TmVar t -> (ctx, [], ESEVar { id = t.ident })
  | TmConst { val = CInt c } -> (ctx, [], ESEInt { value = c.val })
  | TmConst t & e ->
    errorSingle [infoTm e] (concat
      "ecmascript: unsupported constant in value position: "
      (getConstStringCode 0 t.val))
  | TmDecl { decl = DeclLet d, inexpr = inexpr } ->
    -- Hoist the binding out in front of the expression that needs it.
    --
    -- This is only sound because nothing in step 1 builds a conditional or a
    -- short-circuit operator in expression position; once it does, hoisting
    -- must stop at that boundary and fall back to an IIFE.
    match compileStmts ctx (ESCBind d.ident) d.body with (ctx, bind) in
    match compileExpr ctx inexpr with (ctx, stmts, expr) in
    (ctx, concat bind stmts, expr)
  | TmApp _ & t ->
    match esCollectApp t with (fn, args) in
    match fn with TmConst c then compileConstApp ctx (infoTm t) c.val args
    else
      match compileExpr ctx fn with (ctx, s0, callee) in
      match compileExprs ctx args with (ctx, s1, args) in
      (ctx, concat s0 s1, ESECall { callee = callee, args = args })
  | t ->
    errorSingle [infoTm t] (concat
      "ecmascript: unsupported expression: " (esExprName t))

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

  ---------------
  -- INTRINSICS --
  ---------------

  -- Compiles a fully applied constant. MExpr constants are curried, so an
  -- application carrying the wrong number of arguments is a partial
  -- application, which step 1 does not yet build a closure for.
  sem compileConstApp
    : ESCompileCtx -> Info -> Const -> [Expr] -> (ESCompileCtx, [ESStmt], ESExpr)
  sem compileConstApp ctx info const =
  | args ->
    let binop = lam op.
      match args with [l, r] then
        match compileExprs ctx [l, r] with (ctx, stmts, [l, r]) in
        Some (ctx, stmts, ESEBin { op = op, lhs = l, rhs = r })
      else None ()
    in
    let effect = lam field.
      match args with [x] then
        match compileExpr ctx x with (ctx, stmts, x) in
        let callee = esMember (ESEVar { id = ctx.runtimeEnv }) field in
        Some (ctx, stmts, ESECall { callee = callee, args = [x] })
      else None ()
    in
    let result =
      switch const
      case CAddi _ then binop (ESOAdd {})
      case CSubi _ then binop (ESOSub {})
      case CMuli _ then binop (ESOMul {})
      case CDPrint _ then effect "dprint"
      case _ then None ()
      end
    in
    match result with Some r then r
    else errorSingle [info] (join
      [ "ecmascript: unsupported application of '"
      , getConstStringCode 0 const
      , "' to ", int2string (length args)
      , " argument(s) in step 1" ])

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
    let ctx = { runtimeEnv = runtimeEnv } in
    match compileStmts ctx (ESCDiscard ()) ast with (_, stmts) in
    ESProg { 
      imports = [],
      stmts = [
        ESSExportDefault {
          stmt = ESSFunDecl {
            id = nameSym "main",
            params = [runtimeEnv],
            body = stmts
          }
        }
      ]
    }

end
