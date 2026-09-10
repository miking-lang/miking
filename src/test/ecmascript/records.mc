-- Records and tuples.
--
-- As in arith.mc, every printed value is an integer: `dprint` of a record
-- renders differently in the OCaml backend than anywhere else.
mexpr
let r = {x = 1, y = 2, z = 3} in
dprint r.x;
dprint r.y;
dprint r.z;

-- Tuples are records whose fields are named "0", "1", ... so they are indexed
-- rather than accessed with a dot.
let t = (10, 20, 30) in
dprint t.0;
dprint t.1;
dprint t.2;

-- Nested access.
let n = {inner = {a = 7, b = 8}, c = 9} in
dprint n.inner.a;
dprint n.inner.b;
dprint n.c;

-- Update leaves the other fields alone and does not mutate the original.
let r2 = {r with y = 99} in
dprint r2.x;
dprint r2.y;
dprint r2.z;
dprint r.y;

-- A pattern that names several fields.
let sum2 = lam p. match p with {x = a, y = b} then addi a b else 0 in
dprint (sum2 r);

-- Tuple patterns.
let sum3 = lam p. match p with (a, b, c) then addi a (addi b c) else 0 in
dprint (sum3 t);

-- Records flowing through functions, and built inside them.
let mk = lam a. lam b. {lo = a, hi = b} in
let width = lam p. subi p.hi p.lo in
dprint (width (mk 3 10));

-- A field holding a function.
let ops = {double = lam v. muli v 2} in
dprint (ops.double 21);

-- Unit is the empty record.
let u = () in
dprint (match u with {} then 1 else 0)
