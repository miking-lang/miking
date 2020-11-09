-- Compilation from MExpr to C. Only supports a small subset of MExpr
-- programs. We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--
-- Assumptions:
-- * All identifiers are unique (i.e., are symbolized)
-- * All lets and lambdas have proper type annotations
-- (TODO(dlunde,2020-10-03): Add type annotations to all lets). This requirement
-- can be weakened when we have a type system.

include "mexpr/ast.mc"
include "mexpr/anf.mc"
include "mexpr/programs.mc"

include "ast.mc"
include "pprint.mc"

-- NOTE(dlunde,2020-11-04) Compiler phases:
-- 1. Identify compound types and define them at top-level (structs, tagged
-- unions). NOTE: Do we want to support curried data constructors?
-- 2. Do a (partial) ANF transformation, lifting out construction of compound
-- data types from expressions (i.e., we avoid anonymous
-- record/sequence/variant construction in the middle of expressions). By doing
-- this, construction of complex data types is explicit and always bound to
-- variables, which makes translation to C straightforward.
-- 3. Translate to C program.

-- TODO(dlunde,2020-11-02): Right now, this fragment definition merges the ASTs
-- of both MExpr and C. This results in, for instance, Expr including both
-- MExpr and C expressions. In the future, we need some type of qualified
-- fragment include or similar to resolve this.
-- See https://github.com/miking-lang/miking/issues/213.
lang CompileMExprC = MExprAst + CAst + MExprANF

  -- TODO: Minimize ANF transform

  sem compile =
  | prog ->
    let prog = normalizeTerm prog in
    error "TODO"
    -- Call `compileTop` and build final program from result.

  sem compileTop =
  | TmLet _ -> error "TODO"
    -- Check for and specially handle let x = lam. ....
    -- Otherwise, compile and move initialization to `main` function (leave
    -- declaration here though)
  | TmRecLets _ -> error "TODO"
    -- Only allow let x = lam. ....
    -- Identical to a sequence of TmLets, but also forward declare all
    -- functions involved.
  | TmConDef _ -> error "TODO"
    -- Fail or skip. These should be handled by a prior compiler phase.
  | TmUtest _ -> error "TODO"
    -- Fail or skip.
  | rest -> error "TODO"
    -- This is the return value of function `main` (call compileStmt)

  sem compileStmt =
  | TmLet _ -> error "TODO"
    -- Declare variable and call `compileExpr` on body.
    -- The following bodies require special handling:
    -- * TmMatch: translate to if or switch statement.
    -- * TmSeq: allocate and create a new struct/array.
    -- * TmConApp: allocate and create a new struct.
    -- * TmRecord: allocate and create new struct.
    -- * TmRecordUpdate: allocate and create new struct.
  | TmRecLets _ -> error "TODO"
    -- Not allowed here.
  | TmConDef _ -> error "TODO"
    -- Should have been handled by prior compiler phase/type checker.
  | TmUtest _ -> error "TODO"
    -- Skip or fail
  | rest -> error "TODO"
    -- Return result of `compileExpr`

  sem compileExpr =
  | TmVar _ -> error "TODO"
    -- Direct translation.
  | TmApp _ -> error "TODO"
    -- Fail if lhs is not TmVar (or a predetermined set of consts).
  | TmLam _ -> error "TODO"
    -- Anonymous function, not allowed.
  | TmRecord _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmRecordUpdate _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmLet _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmRecLets _ -> error "TODO"
    -- Not allowed here.
  | TmConst _ -> error "TODO"
    -- Translate to Literal.
  | TmConDef _ -> error "TODO"
    -- Should have been handled by prior compiler phase/type checker.
  | TmConApp _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmMatch _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmUtest _ -> error "TODO"
    -- Not allowed.
  | TmSeq _ -> error "TODO"
    -- Should not occur here because of prior compiler phase.
  | TmNever _ -> error "TODO"
    -- Should not occur here.

end

-- TODO Throws error
-- lang TestLang = CompileMExprC + MExprPrettyPrint + CPrettyPrint
lang TestLang = CompileMExprC + CPrettyPrint + MExprPrettyPrint

mexpr
use TestLang in

-- global data
-- odd
-- even
-- factorial
-- function creating and returning record
-- nested match

let mprog = bindall_ [
  programsFactorial,
  programsOddEven
]
in

let _ = tyint_ in

let _ = print (expr2str mprog) in

()
