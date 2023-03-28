include "lib.mc"

let alsoIncludeDecon = lam x. match x with TestCon _ then "match" else "no match"
let triple_bump = lam n. bump(bump(bump n))
