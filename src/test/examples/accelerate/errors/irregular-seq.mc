mexpr
let s = [[1, 2, 3], [4, 5], [7, 8, 9]] in
accelerate (map (foldl addi 0) s)
