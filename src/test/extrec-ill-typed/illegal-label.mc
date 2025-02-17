mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 

let r = {Foo of x = 1, y = 2} in 
r.z