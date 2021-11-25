-- Nested acceleration within the element of a sequence literal.

let f = lam x. accelerate (muli x 2)
let g = lam x. f (addi x 1)

mexpr

let s = [accelerate (g 3), f 4] in
s
