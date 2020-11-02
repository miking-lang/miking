-- Compilation from MExpr to C (only supports a small subset of MExpr
-- programs). We currently do not have checks for this, so some MExpr programs
-- will compile (without error) to invalid C programs.
--
-- Assumptions:
-- * All identifiers are unique (i.e., are symbolized)


-- TODO(dlunde,2020-11-02): Right now, this fragment definition merges the ASTs
-- of both MExpr and C. This results in, for instance, Expr including both
-- MExpr and C expressions. In the future, we need some type of qualified
-- fragment include or similar to resolve this.
lang CompileMExprC = MExprAst + CAst

  sem compile =
  | prog -> -- Call `compileTop` and build final program from result.

  sem compileTop =
  | TmLet ->
    -- Check for and specially handle let x = lam. ....
    -- Otherwise, compile and move initialization to `main` function (leave
    -- declaration here though)
  | TmRecLets ->
    -- Only allow let x = lam. ....
    -- Identical to a sequence of TmLets, but also forward declare all
    -- functions involved.
  | TmConDef ->
    -- These should be handled by a prior compiler phase (which also receives
    -- input from the type checker)
  | TmUtest ->
    -- Skip
  | rest ->
    -- Return value of function `main` (call compileStmt)

  sem compileStmt =
  | TmLet ->
    -- Declare variable and call `compileExpr` on body. TmMatch requires
    -- special handling (translates to if-statement).
  | TmRecLets -> fail
    -- Not allowed.
  | TmConDef -> fail
    -- Should have been handled by prior compiler phase/type checker
  | TmUtest -> fail
    -- Not allowed
  | TmNever -> fail
    -- Should not occur at this level

  -- The below will be very similar to compileExpr, except the value is
  -- returned and not written to a variable. Reuse possible?
  | TmVar ->
    -- Return contents of variable
  | TmApp ->
    -- Return the result of calling a function. Fail if lhs is not TmVar
  | TmLam -> fail
    -- Return anonymous function, not allowed
  | TmRecord -> fail
    -- Return struct (or struct pointer) in C (allow?)
  | TmRecordUpdate -> fail
    -- Return struct (or struct pointer)in C (allow?)
  | TmConst ->
    -- Return a literal.
  | TmConApp -> fail
    -- Return struct (or struct pointer) in C (allow?)
  | TmMatch ->
    -- Translates depending on pattern. Most basic things can be encoded using
    -- if-statements.
  | TmSeq -> fail
    -- Return struct/array (or struct pointer) in C (allow?)

  sem compileExpr =
  | TmVar ->
    -- Direct translation
  | TmApp ->
    -- Fail if lhs is not TmVar
  | TmLam -> fail
    -- Anonymous function, not allowed
  | TmRecord -> fail
    -- Create a new struct (allow?)
  | TmRecordUpdate -> fail
    -- Create a new struct (allow?)
  | TmLet ->
    -- Equivalent to starting a new scope?
  | TmRecLets -> fail
    -- Not allowed.
  | TmConst ->
    -- Literal
  | TmConDef -> fail
    -- Should have been handled by prior compiler phase/type checker
  | TmConApp -> fail
    -- Will be equivalent to returning a C struct, which is not allowed.
  | TmMatch ->
    -- Translates depending on pattern. Most basic things can be encoded using
    -- if-statements.
  | TmUtest -> fail
    -- Not allowed
  | TmSeq -> fail
    -- Create a new struct/array (allow?)
  | TmNever -> fail
    -- Create a new struct/array (allow?)

end
