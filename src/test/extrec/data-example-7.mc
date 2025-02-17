mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 

rectype Bar in 
recfield f1 : all m. Bar -> Foo{m} in 
recfield f2 : all m. Bar -> Foo{m} in 

let fun : all m :: {Bar [> f1 f2], Foo [> x y]}. 
            Bar{m} -> Int
  = lam bar.
    let f1 = bar.f1 in 
    let f2 = bar.f2 in 
    addi f1.x f2.y
in 

let b = {Bar of f1 = {Foo of x = 1, y = 2}, 
                f2 = {Foo of x = -1, y = -2}} in 

utest fun b with -1 in 

()
