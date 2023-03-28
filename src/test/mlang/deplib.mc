include "dep.mc"
include "lib.mc"

let depDecon = lam x. match x with TestCon _ then "match" else error "no match"
