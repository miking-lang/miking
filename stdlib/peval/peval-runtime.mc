include "peval/peval.mc"


-- Let bind the semantic 'peval' function such that we can include it 
let peval : Expr -> Expr = lam ast. 
    use MExprPEval in
    peval ast

mexpr

unsafeCoerce (peval)
