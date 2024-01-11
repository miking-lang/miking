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

let nested = (1,(2,3)) in
utest nested.1.0 with 2 in
utest nested .1 .0 with 2 in
utest nested.#label"1".#label"0" with 2 in
utest nested .#label"1" .#label"0" with 2 in

-- test order of evaluation for record expressions by observing side effects
let v = ref 0 in
let r5 = {x = 10, y = 11, z = 12, a = 13} in
let r5mod = {r5 with
	z = modref v (addi (deref v) 1); addi r5.z (deref v),
	x = modref v (addi (deref v) 1); addi r5.x (deref v),
	y = modref v (addi (deref v) 1); addi r5.y (deref v),
	a = modref v (addi (deref v) 1); addi r5.a (deref v)
} in

utest r5mod with {x = 12, y = 14, z = 13, a = 17} in

-- NOTE(oerikss, 2024-01-10): Checks so that the parser does not confuse .x with
-- a record projection. However, lam x.1 will not parse as .1 is tokenized as a
-- tuple projection label.
utest (lam x.x) 1 with 1 in

()
