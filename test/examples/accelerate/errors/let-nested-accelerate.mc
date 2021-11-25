-- Example using nested accelerate terms, which is not allowed

let f : Int -> Int = lam x. accelerate (addi x 1)

mexpr

accelerate (f 2)
