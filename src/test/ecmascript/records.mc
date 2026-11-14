-- Records and tuples.
mexpr
let r = {x = 1, y = 2, z = 3} in
utest r.x with 1 in
utest r.y with 2 in
utest r.z with 3 in
utest r with {x = 1, y = 2, z = 3} in

-- Tuples are records whose fields are named "0", "1", ... so they are indexed
-- rather than accessed with a dot.
let t = (10, 20, 30) in
utest t.0 with 10 in
utest t.1 with 20 in
utest t.2 with 30 in
utest t with (10, 20, 30) in

-- Nested access.
let n = {inner = {a = 7, b = 8}, c = 9} in
utest n.inner.a with 7 in
utest n.inner.b with 8 in
utest n.c with 9 in

-- Update leaves the other fields alone and does not mutate the original.
let r2 = {r with y = 99} in
utest r2 with {x = 1, y = 99, z = 3} in
utest r.y with 2 in

-- A pattern that names several fields.
let sum2 = lam p. match p with {x = a, y = b} then addi a b else 0 in
utest sum2 r with 3 in

-- Tuple patterns.
let sum3 = lam p. match p with (a, b, c) then addi a (addi b c) else 0 in
utest sum3 t with 60 in

-- Records flowing through functions, and built inside them.
let mk = lam a. lam b. {lo = a, hi = b} in
let width = lam p. subi p.hi p.lo in
utest width (mk 3 10) with 7 in

-- A field holding a function.
let ops = {double = lam v. muli v 2} in
utest ops.double 21 with 42 in

-- Unit is the empty record.
let u = () in
utest match u with {} then 1 else 0 with 1 in
()
