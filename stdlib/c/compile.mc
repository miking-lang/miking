-- Compilation from MExpr to C. Only supports a small subset of MExpr
-- programs. We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--
-- Assumptions:
-- * All identifiers are unique (i.e., are symbolized)
-- * All lets and lambdas have proper type annotations
-- (TODO(dlunde,2020-10-03): Add type annotations to lets). This requirement
-- can (probably?) be weakened when we have a type system.

include "mexpr/ast.mc"
include "ast.mc"


-- TODO(dlunde,2020-11-02): Right now, this fragment definition merges the ASTs
-- of both MExpr and C. This results in, for instance, Expr including both
-- MExpr and C expressions. In the future, we need some type of qualified
-- fragment include or similar to resolve this.
lang CompileMExprC = MExprAst + CAst

  sem compile =
  | prog -> error "TODO"
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
    -- Declare variable and call `compileExpr` on body. TmMatch requires
    -- special handling (translates to if-statement).
  | TmRecLets _ -> error "TODO"
    -- Not allowed.
  | TmConDef _ -> error "TODO"
    -- Should have been handled by prior compiler phase/type checker
  | TmUtest _ -> error "TODO"
    -- Skip or fail
  | rest -> error "TODO"
    -- Call compileExpr

  sem compileExpr =
  | TmVar _ -> error "TODO"
    -- Direct translation
  | TmApp _ -> error "TODO"
    -- Fail if lhs is not TmVar (or a predetermined set of consts)
  | TmLam _ -> error "TODO"
    -- Anonymous function, not allowed
  | TmRecord _ -> error "TODO"
    -- Create a new struct (allow?)
  | TmRecordUpdate _ -> error "TODO"
    -- Create a new struct (allow?)
  | TmLet _ -> error "TODO"
    -- Equivalent to starting a new scope?
  | TmRecLets _ -> error "TODO"
    -- Not allowed.
  | TmConst _ -> error "TODO"
    -- Literal
  | TmConDef _ -> error "TODO"
    -- Should have been handled by prior compiler phase/type checker
  | TmConApp _ -> error "TODO"
    -- Will be equivalent to returning a C struct, which is not allowed.
  | TmMatch _ -> error "TODO"
    -- Translates depending on pattern. Most basic things can be encoded using
    -- if-statements.
  | TmUtest _ -> error "TODO"
    -- Not allowed
  | TmSeq _ -> error "TODO"
    -- Create a new struct/array (allow?)
  | TmNever _ -> error "TODO"
    -- Should not occur here

end
