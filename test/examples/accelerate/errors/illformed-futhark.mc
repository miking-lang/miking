mexpr
accelerate (
  recursive
    let a = lam f. b (f 1)
    let b = lam x. muli x (b (subi x 1))
  in
  let s = [lam x. addi x 1, lam y. muli y 2] in
  -- NOTE: use a map to force use of Futhark backend
  map a s)
