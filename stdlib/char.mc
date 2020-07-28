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

utest char2upper 'a' with 'A'
utest char2upper '0' with '0'
utest char2upper 'A' with 'A'

let char2lower = lam c.
  if and (geqchar c 'A') (leqchar c 'Z')
  then (int2char (addi (char2int c) 32))
  else c

utest char2lower 'a' with 'a'
utest char2lower '0' with '0'
utest char2lower 'A' with 'a'

-- Character predicates
let is_whitespace = lam c. any (eqchar c) [' ', '\n', '\t', '\r']

utest is_whitespace ' ' with true
utest is_whitespace '	' with true
utest is_whitespace '
' with true
utest is_whitespace 'a' with false
utest is_whitespace '\n' with true
utest is_whitespace '\t' with true
utest is_whitespace '\r' with true
utest is_whitespace '\'' with false

let is_lower_alpha = lam c.
  and (leqi (char2int 'a') (char2int c)) (leqi (char2int c) (char2int 'z'))

let is_upper_alpha = lam c.
  and (leqi (char2int 'A') (char2int c)) (leqi (char2int c) (char2int 'Z'))

let is_alpha = lam c. or (is_lower_alpha c) (is_upper_alpha c)

utest is_alpha 'a' with true
utest is_alpha 'm' with true
utest is_alpha 'z' with true
utest is_alpha '`' with false
utest is_alpha '{' with false
utest is_alpha 'A' with true
utest is_alpha 'M' with true
utest is_alpha 'Z' with true
utest is_alpha '@' with false
utest is_alpha '[' with false

let is_digit = lam c.
  and (leqi (char2int '0') (char2int c)) (leqi (char2int c) (char2int '9'))

utest is_digit '0' with true
utest is_digit '5' with true
utest is_digit '9' with true
utest is_digit '/' with false
utest is_digit ':' with false

let is_alphanum = lam c.
  or (is_alpha c) (is_digit c)

utest is_alphanum '0' with true
utest is_alphanum '9' with true
utest is_alphanum 'A' with true
utest is_alphanum 'z' with true
utest is_alphanum '_' with false
