-- Construct a reference
let ref = lam x. tensorCreate [] (lam. x)

-- De-reference
let deref = lam t. tensorGetExn t []

-- Mutate reference
let modref = lam t. lam v. tensorSetExn t [] v
