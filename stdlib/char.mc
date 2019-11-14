include "seq.mc"

let eqchar = lam c1. lam c2. eqi (char2int c1) (char2int c2)
let neqchar = lam c1. lam c2. neqi (char2int c1) (char2int c2)
let ltchar = lam c1. lam c2. lti (char2int c1) (char2int c2)
let gtchar = lam c1. lam c2. gti (char2int c1) (char2int c2)
let leqchar = lam c1. lam c2. leqi (char2int c1) (char2int c2)
let geqchar = lam c1. lam c2. geqi (char2int c1) (char2int c2)
let show_char = lam c. concat "'" (concat [c] "'")

-- Character conversion
let char2upper = lam c.
  if and (geqchar c 'a') (leqchar c 'z')
  then (int2char (subi (char2int c) 32))
  else c

let char2lower = lam c.
  if and (geqchar c 'A') (leqchar c 'Z')
  then (int2char (addi (char2int c) 32))
  else c

-- TODO: It would be nicer with escape codes in chars!
let is_whitespace = lam c.
  or (or (eqchar c ' ') (eqchar c (head "\n"))) (eqchar c (head "\t"))

let is_lower_alpha = lam c.
  and (leqi (char2int 'a') (char2int c)) (leqi (char2int c) (char2int 'z'))

let is_upper_alpha = lam c.
  and (leqi (char2int 'A') (char2int c)) (leqi (char2int c) (char2int 'Z'))

let is_alpha = lam c. or (is_lower_alpha c) (is_upper_alpha c)

let is_digit = lam c.
  and (leqi (char2int '0') (char2int c)) (leqi (char2int c) (char2int '9'))

let is_alphanum = lam c.
  or (is_alpha c) (is_digit c)

mexpr

utest char2upper 'a' with 'A' in
utest char2upper '0' with '0' in
utest char2upper 'A' with 'A' in

utest char2lower 'a' with 'a' in
utest char2lower '0' with '0' in
utest char2lower 'A' with 'a' in

utest is_whitespace ' ' with true in
utest is_whitespace '	' with true in
utest is_whitespace '
' with true in
utest is_whitespace 'a' with false in

utest is_alpha 'a' with true in
utest is_alpha 'm' with true in
utest is_alpha 'z' with true in
utest is_alpha '`' with false in
utest is_alpha '{' with false in
utest is_alpha 'A' with true in
utest is_alpha 'M' with true in
utest is_alpha 'Z' with true in
utest is_alpha '@' with false in
utest is_alpha '[' with false in

utest is_digit '0' with true in
utest is_digit '5' with true in
utest is_digit '9' with true in
utest is_digit '/' with false in
utest is_digit ':' with false in

utest is_alphanum '0' with true in
utest is_alphanum '9' with true in
utest is_alphanum 'A' with true in
utest is_alphanum 'z' with true in
utest is_alphanum '_' with false in
()
