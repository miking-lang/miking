let eqchar = lam c1. lam c2. eqi (char2int c1) (char2int c2)
let show_char = lam c. concat "'" (concat [c] "'")

-- TODO: It would be nicer with escape codes in chars!
let is_whitespace = lam c.
  or (or (eqchar c ' ') (eqchar c (head "\n"))) (eqchar c (head "\t"))

let is_alpha = lam c.
  or (and (leqi (char2int 'A') (char2int c)) (leqi (char2int c) (char2int 'Z')))
     (and (leqi (char2int 'a') (char2int c)) (leqi (char2int c) (char2int 'z')))

let is_digit = lam c.
  and (leqi (char2int '0') (char2int c)) (leqi (char2int c) (char2int '9'))

let is_alphanum = lam c.
  or (is_alpha c) (is_digit c)

main

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
