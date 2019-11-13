include "char.mc"
include "option.mc"
include "seq.mc"

let eqstr = fix (lam eqstr. lam s1. lam s2.
    if neqi (length s1) (length s2)
    then false
    else if null s1
         then true
         else if eqchar (head s1) (head s2)
         then eqstr (tail s1) (tail s2)
         else false
)

let string2int = fix (lam string2int. lam s.
  let len = length s in
  let last = subi len 1 in
  if eqi len 0
  then 0
  else
    let lsd = subi (char2int (nth s last)) (char2int '0') in
    let rest = muli 10 (string2int (slice s 0 last)) in
    addi rest lsd
)

let int2string = fix (lam int2string. lam n.
  if lti n 10
  then [int2char (addi n (char2int '0'))]
  else
    let d = [int2char (addi (modi n 10) (char2int '0'))] in
    concat (int2string (divi n 10)) d
)

// Returns an option with the index of the first occurrence of c in s. Returns
// None if c was not found in s.
let strIndex = lam c. lam s.
  let strIndex_rechelper = fix (lam strIndex. lam i. lam c. lam s.
    if eqi (length s) 0
    then None
    else if eqchar c (head s)
         then Some(i)
         else strIndex (addi i 1) c (tail s)
  ) in
  strIndex_rechelper 0 c s

// Returns an option with the index of the last occurrence of c in s. Returns
// None if c was not found in s.
let strLastIndex = lam c. lam s.
  let strLastIndex_rechelper = fix (lam strLastIndex. lam i. lam acc. lam c. lam s.
    if eqi (length s) 0 then
      if eqi acc (negi 1)
      then None
      else Some(acc)
    else
      if eqchar c (head s)
      then strLastIndex (addi i 1) i   c (tail s)
      else strLastIndex (addi i 1) acc c (tail s)
  ) in
  strLastIndex_rechelper 0 (negi 1) c s

// Splits s on delim
let strSplit = fix (lam strSplit. lam delim. lam s.
  if or (eqi (length delim) 0) (lti (length s) (length delim))
  then cons s []
  else if eqstr delim (slice s 0 (length delim))
       then cons [] (strSplit delim (slice s (length delim) (length s)))
       else let remaining = strSplit delim (tail s) in
            cons (cons (head s) (head remaining)) (tail remaining)
)

// Trims s of spaces
let strTrim = lam s.
  let strTrim_init = fix (lam strTrim_init. lam s.
    if eqstr s ""
    then s
    else if is_whitespace (head s)
         then strTrim_init (tail s)
         else s
  ) in
  reverse (strTrim_init (reverse (strTrim_init s)))

// Joins the strings in strs on delim
let strJoin = fix (lam strJoin. lam delim. lam strs.
  if eqi (length strs) 0
  then ""
  else if eqi (length strs) 1
       then head strs
       else concat (concat (head strs) delim) (strJoin delim (tail strs))
)

mexpr

utest string2int "5" with 5 in
utest string2int "25" with 25 in
utest string2int "314159" with 314159 in

utest int2string 5 with "5" in
utest int2string 25 with "25" in
utest int2string 314159 with "314159" in

utest strIndex '%' "a % 5" with Some(2) in
utest strIndex '%' "a & 5" with None in
utest strIndex 'w' "Hello, world!" with Some(7) in
utest strIndex 'w' "Hello, World!" with None in
utest strIndex 'o' "Hello, world!" with Some(4) in
utest strIndex '@' "Some @TAG@" with Some(5) in

utest strLastIndex '%' "a % 5" with Some(2) in
utest strLastIndex '%' "a & 5" with None in
utest strLastIndex 'w' "Hello, world!" with Some(7) in
utest strLastIndex 'w' "Hello, World!" with None in
utest strLastIndex 'o' "Hello, world!" with Some(8) in
utest strLastIndex '@' "Some @TAG@" with Some(9) in

utest strSplit "ll" "Hello" with ["He", "o"] in
utest strSplit "ll" "Hellallllo" with ["He", "a", "", "o"] in
utest strSplit "" "Hello" with ["Hello"] in
utest strSplit "lla" "Hello" with ["Hello"] in
utest strSplit "Hello" "Hello" with ["", ""] in

utest strTrim " aaaa   " with "aaaa" in
utest strTrim "   bbbbb  bbb " with "bbbbb  bbb" in
utest strTrim "ccccc c\t   \n" with "ccccc c" in

utest strJoin "--" ["water", "tea", "coffee"] with "water--tea--coffee" in
utest strJoin "--" [] with "" in
utest strJoin "--" ["coffee"] with "coffee" in
utest strJoin "water" ["coffee", "tea"] with "coffeewatertea" in

()
