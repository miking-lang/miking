mexpr
rectype SomeEnv in
recfield x : all m. SomeEnv -> Int in 
recfield y : all m. SomeEnv -> Int in 
let rec = {SomeEnv of x = 1} in 
let rec = {extend rec with y = 2} in 
utest addi rec.x rec.y with 3 in 
()