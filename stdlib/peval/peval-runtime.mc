include "peval/peval.mc"


-- Let bind the semantic 'peval' function such that we can include it 
let pevalWithEnv = lam env. lam ast. 
    use MExprPEval in
    pevalWithEnv env ast

mexpr

unsafeCoerce (pevalWithEnv)
