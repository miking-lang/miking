-- Defines the different functions that should be included in the AST during
-- the specialize transformation.
include "map.mc"
include "stringid.mc"
include "mexpr/pprint.mc"
include "peval/peval.mc"
include "name.mc"

let toString = use MExprPrettyPrint in
  lam x. mexprToString x

let pevalWithEnv = lam env. lam ast.
  use MExprPEval in pevalWithEnv env ast

mexpr

unsafeCoerce (pevalWithEnv, mapFromSeq, stringToSid, mapMapWithKey, toString, _noSymbol)

-- Want to make sure that:
--  * All constructors for Expr, Type and Pat are included
--  * Builtins
--  * Some additional functions as well as semantic peval function
