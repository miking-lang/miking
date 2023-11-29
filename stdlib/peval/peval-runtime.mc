-- Defines the different functions that should be included in the AST during
-- the specialize transformation.
include "map.mc"
include "stringid.mc"
include "peval/peval.mc"
include "peval/jit.mc"
include "name.mc"

let pevalWithEnv = lam env. lam ast.
  use MExprPEval in pevalWithEnv env ast

mexpr

unsafeCoerce (pevalWithEnv, mapFromSeq, stringToSid, mapMapWithKey, _noSymbol,
 jitCompile, nameCmp)

-- Want to make sure that:
--  * All constructors for Expr, Type and Pat are included
--  * Builtins
--  * Some additional functions as well as semantic peval function
