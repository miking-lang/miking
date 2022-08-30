-- Nested acceleration among bindings of a recursive-let.

let f = lam x. addi x 1
recursive
  let a = lam x. b x
  let b = lam y. accelerate (c y)
  let c = lam z. f z
end

mexpr

accelerate (a 3)
