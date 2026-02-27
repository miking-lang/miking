include "./utils.mc"
include "../global/objects.mc"
include "mexpr/pprint.mc"

let semVariantParse : use MExprPrettyPrint in use Objects in Expr -> [SemVariant] = 
    use Objects in
    use MExprPrettyPrint in

    lam e.

    recursive let skipLams = lam e.
        match e with TmLam { body = body } then skipLams body
        else e
    in

    recursive let getVariants = lam e.
        match e with TmMatch { pat = pat, els = els }
        then cons (pat2str pat) (getVariants els)
        else []
    in

    let lamLess = skipLams e in
    getVariants lamLess
