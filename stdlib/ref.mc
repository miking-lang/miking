-- Construct a reference
let ref = lam x. tensorCreate [] (lam _. x)

-- De-reference
let deref = lam t. tensorGetExn t []

-- Mutate reference
let modref = lam t. lam v. tensorSetExn t [] v
