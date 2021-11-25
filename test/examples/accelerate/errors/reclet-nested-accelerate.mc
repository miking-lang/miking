-- Nested acceleration among bindings of a recursive-let.

let f = lam x. addi x 1
recursive
  let a = lam x. b x
  let b = lam y. accelerate (f y)
end

mexpr

accelerate (a 3)
