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

let r4 = {r1 with age = 12, name = "babar"} in
utest r4 with {age = 12, name = "babar"} in

let bumpAge = lam r : {age : Int, name : String}. {r with age = addi r.age 1} in

utest bumpAge r1 with r2 in

let nested = {a = {b = 1}} in
let arec = {nested.a with b = addi nested.a.b 1} in
utest arec.b with 2 in

-- test order of evaluation for record update expressions by observing side effects
let v = ref 0 in
let r5 = {x = 2, y = 1, z = 3, a = 0} in
let r5mod = {r5 with
	z = modref v (addi (deref v) 1); addi r5.z (deref v),
	x = modref v (addi (deref v) 1); addi r5.x (deref v),
	y = modref v (addi (deref v) 1); addi r5.y (deref v),
	a = modref v (addi (deref v) 1); addi r5.a (deref v)
} in

utest r5mod with {x = 4, y = 4, z = 4, a = 4} in

()
