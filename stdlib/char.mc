include "seq.mc"

let eqChar = lam c1. lam c2. eqi (char2int c1) (char2int c2)
let leqChar = lam c1. lam c2. leqi (char2int c1) (char2int c2)
let geqChar = lam c1. lam c2. geqi (char2int c1) (char2int c2)

-- Display characters
let showChar = lam c.
  let escapes = [('\n', "n"), ('\t', "t"), ('\r', "r"),
                 ('\\', "\\"), ('\"', "\""), ('\'', "\'")] in
  match find (lam e. eqChar c e.0) escapes with Some (_, v) then
    join ["\'\\", v, "\'"]
  else
    ['\'', c, '\'']

utest showChar 'e' with "\'e\'"
utest showChar '0' with "\'0\'"
utest showChar '\n' with "\'\\n\'"
utest showChar '\r' with "\'\\r\'"
utest showChar '\t' with "\'\\t\'"

-- Character conversion
let char2upper = lam c.
  if and (geqChar c 'a') (leqChar c 'z')
  then (int2char (subi (char2int c) 32))
  else c

utest char2upper 'a' with 'A'
utest char2upper '0' with '0'
utest char2upper 'A' with 'A'

let char2lower = lam c.
  if and (geqChar c 'A') (leqChar c 'Z')
  then (int2char (addi (char2int c) 32))
  else c

utest char2lower 'a' with 'a'
utest char2lower '0' with '0'
utest char2lower 'A' with 'a'

-- Character predicates
let isWhitespace = lam c. any (eqChar c) [' ', '\n', '\t', '\r']

utest isWhitespace ' ' with true
utest isWhitespace '	' with true
utest isWhitespace '
' with true
utest isWhitespace 'a' with false
utest isWhitespace '\n' with true
utest isWhitespace '\t' with true
utest isWhitespace '\r' with true
utest isWhitespace '\'' with false

let isLowerAlpha = lam c.
  and (leqi (char2int 'a') (char2int c)) (leqi (char2int c) (char2int 'z'))

let isUpperAlpha = lam c.
  and (leqi (char2int 'A') (char2int c)) (leqi (char2int c) (char2int 'Z'))

let isAlpha = lam c. or (isLowerAlpha c) (isUpperAlpha c)

utest isAlpha 'a' with true
utest isAlpha 'm' with true
utest isAlpha 'z' with true
utest isAlpha '`' with false
utest isAlpha '{' with false
utest isAlpha 'A' with true
utest isAlpha 'M' with true
utest isAlpha 'Z' with true
utest isAlpha '@' with false
utest isAlpha '[' with false

let isDigit = lam c.
  and (leqi (char2int '0') (char2int c)) (leqi (char2int c) (char2int '9'))

utest isDigit '0' with true
utest isDigit '5' with true
utest isDigit '9' with true
utest isDigit '/' with false
utest isDigit ':' with false

let isAlphanum = lam c.
  or (isAlpha c) (isDigit c)

utest isAlphanum '0' with true
utest isAlphanum '9' with true
utest isAlphanum 'A' with true
utest isAlphanum 'z' with true
utest isAlphanum '_' with false
