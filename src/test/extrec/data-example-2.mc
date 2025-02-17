mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 
recfield z : all m. Foo -> Int in 

let f : all m :: {Foo [< x y z]}.
        Int -> Foo{m} = 
  lam arg. {Foo of x = 0, y = arg, z = subi 100 arg} in 

let r = f 10 in 
utest r.x with 0 in 
utest r.y with 10 in 
utest r.z with 90 in ()