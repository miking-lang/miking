include "seq.mc"


let eqChar = lam c1. lam c2. eqc c1 c2
let neqChar = lam c1. lam c2. not (eqc c1 c2)
utest eqChar 'a' 'a' with true
utest eqChar 'A' 'B' with false
utest neqChar 'a' 'a' with false
utest neqChar 'A' 'B' with true

let ltChar = lam c1. lam c2. lti (char2int c1) (char2int c2)
let gtChar = lam c1. lam c2. gti (char2int c1) (char2int c2)
let leqChar = lam c1. lam c2. leqi (char2int c1) (char2int c2)
let geqChar = lam c1. lam c2. geqi (char2int c1) (char2int c2)
let cmpChar = lam c1. lam c2. subi (char2int c1) (char2int c2)

utest cmpChar 'a' 'a' with 0
utest cmpChar 'a' 'A' with 32
utest cmpChar '\t' '\n' with subi 0 1

-- Escape characters
let _escapes = [
  ('\n', "\\n"),
  ('\t', "\\t"),
  ('\r', "\\r"),
  ('\\', "\\\\"),
  ('\"', "\\\""),
  ('\'', "\\\'")
]
let escapeChar = lam c.
  match find (lam e : (Char, String). eqChar c e.0) _escapes with Some n then
    let n : (Char, String) = n in
    n.1
  else [c]

utest escapeChar 'e' with "e"
utest escapeChar '0' with "0"
utest escapeChar '\n' with "\\n"
utest escapeChar '\r' with "\\r"
utest escapeChar '\t' with "\\t"

-- Display characters
let showChar = lam c. join ["\'", escapeChar c, "\'"]

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
  let i = char2int c in
  if leqi (char2int 'a') i then
    leqi i (char2int 'z')
  else false

let isUpperAlpha = lam c.
  let i = char2int c in
  if leqi (char2int 'A') i then
    leqi i (char2int 'Z')
  else false

let isAlpha = lam c.
  if isLowerAlpha c then true
  else isUpperAlpha c

let isLowerAlphaOrUnderscore = lam c.
  if isLowerAlpha c then true
  else eqChar c '_'

let isAlphaOrUnderscore = lam c.
  if isAlpha c then true
  else eqChar c '_'

utest isAlphaOrUnderscore '1' with false
utest isAlphaOrUnderscore 'a' with true
utest isAlphaOrUnderscore 'A' with true
utest isAlphaOrUnderscore '_' with true
utest isAlphaOrUnderscore '{' with false

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
  let i = char2int c in
  if leqi (char2int '0') i then
    leqi i (char2int '9')
  else false

utest isDigit '0' with true
utest isDigit '5' with true
utest isDigit '9' with true
utest isDigit '/' with false
utest isDigit ':' with false

let isAlphanum = lam c.
  if isAlpha c then true
  else isDigit c

utest isAlphanum '0' with true
utest isAlphanum '9' with true
utest isAlphanum 'A' with true
utest isAlphanum 'z' with true
utest isAlphanum '_' with false

utest isLowerAlpha 'a' with true
utest isLowerAlpha 'z' with true
utest isLowerAlpha 'A' with false
utest isLowerAlpha 'Z' with false
utest isLowerAlpha '\n' with false
utest isLowerAlpha '7' with false
utest isLowerAlpha '_' with false

utest isUpperAlpha '0' with false
utest isUpperAlpha 'a' with false
utest isUpperAlpha '_' with false
utest isUpperAlpha 'X' with true
utest isUpperAlpha 'K' with true
utest isUpperAlpha '%' with false

utest isLowerAlphaOrUnderscore '0' with false
utest isLowerAlphaOrUnderscore 'a' with true
utest isLowerAlphaOrUnderscore 'A' with false
utest isLowerAlphaOrUnderscore '{' with false
utest isLowerAlphaOrUnderscore '_' with true
utest isLowerAlphaOrUnderscore '\n' with false

-- Generates a random ASCII letter or digit character.
let randAlphanum : () -> Char = lam.
  -- NOTE(larshum, 2021-09-15): The total number of digits or ASCII letters
  -- (lower- and upper-case) is 10 + 26 + 26 = 62.
  let r = randIntU 0 62 in
  if lti r 10 then int2char (addi r 48)
  else if lti r 36 then int2char (addi r 55)
  else int2char (addi r 61)
