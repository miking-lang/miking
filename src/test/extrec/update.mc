mexpr

rectype Foo in 
recfield x : all m. Foo -> Int in 
recfield y : all m. Foo -> Int in 

rectype Bar in 
recfield a : all m. Bar -> Foo{m} in 
recfield b : all m. Bar -> Foo{m} in 
recfield c : all m. Bar -> () in 

let f1 = {Foo of x = 1, y = 2} in 
let f2 = {Foo of x = -1, y = 2} in 

let bar = {Bar of c = (), a = f1} in

let f = bar.a in 
utest f.x with 1 in 

let bar = {bar with a = f2} in 
let f = bar.a in 
utest f.x with -1 in 

()