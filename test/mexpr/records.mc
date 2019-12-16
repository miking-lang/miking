mexpr

let empty : {} = {} in
utest empty with {} in

let r1 : {age : int, name : string} = {age = 42, name = "foobar"} in
utest r1 with {age = 42, name = "foobar"} in
utest r1 with {name = "foobar", age = 42} in

utest r1.age with 42 in
utest r1.name with "foobar" in

let r2 = {r1 with age = 43} in
utest r2 with {age = 43, name = "foobar"} in

let bumpAge = lam r : {age : int}. {r with age = r.age + 1} in

()