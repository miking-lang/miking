mexpr
rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 
recfield z : all m. Foo -> Int in 

let setXY : all m :: {Foo [< x y]}. 
            Int -> Int -> Foo{m}
  = lam x. lam y. {Foo of x = x, y = y} in

let r = setXY 10 20 in 

let addXY : all m :: {Foo [> x y]}.
          Foo{m} -> Int = 
  lam r. addi r.x r.y in

utest addXY r with 30 in

()
