mexpr

let empty : {} = {} in
utest empty with {} in

let r1 : {age : Int, name : String} = {age = 42, name = "foobar"} in
utest r1 with {age = 42, name = "foobar"} in
utest r1 with {name = "foobar", age = 42} in

utest r1.age with 42 in
utest r1.name with "foobar" in

let r2 = {r1 with age = 43} in
utest r2 with {age = 43, name = "foobar"} in

let r3 = {{r1 with age = 41} with name = "barbar"} in
utest r3 with {age = 41, name = "barbar"} in

let bumpAge = lam r : {age : Int, name : String}. {r with age = addi r.age 1} in

utest bumpAge r1 with r2 in

()
