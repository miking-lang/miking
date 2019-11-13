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
let strindex = lam c. lam s.
  let strindex_abs = fix (lam strindex. lam i. lam c. lam s.
    if eqi (length s) 0
    then None
    else if eqchar c (head s)
         then Some(i)
         else strindex (addi i 1) c (tail s)
  ) in
  strindex_abs 0 c s

// Returns an option with the index of the last occurrence of c in s. Returns
// None if c was not found in s.
let strrindex = lam c. lam s.
  let strrindex_abs = fix (lam strrindex. lam i. lam acc. lam c. lam s.
    if eqi (length s) 0 then
      if eqi acc (negi 1)
      then None
      else Some(acc)
    else
      if eqchar c (head s)
      then strrindex (addi i 1) i   c (tail s)
      else strrindex (addi i 1) acc c (tail s)
  ) in
  strrindex_abs 0 (negi 1) c s

// Splits s on delim
let strsplit = fix (lam strsplit. lam delim. lam s.
  if or (eqi (length delim) 0) (lti (length s) (length delim))
  then cons s []
  else if eqstr delim (slice s 0 (length delim))
       then cons [] (strsplit delim (slice s (length delim) (length s)))
       else let remaining = strsplit delim (tail s) in
            cons (cons (head s) (head remaining)) (tail remaining)
)

// Trims s of spaces
let strtrim = lam s.
  let strtrim_init = fix (lam strtrim_init. lam s.
    if eqstr s ""
    then s
    else if is_whitespace (head s)
         then strtrim_init (tail s)
         else s
  ) in
  reverse (strtrim_init (reverse (strtrim_init s)))

// Joins the strings in strs on delim
let strjoin = fix (lam strjoin. lam delim. lam strs.
  if eqi (length strs) 0
  then ""
  else if eqi (length strs) 1
       then head strs
       else concat (concat (head strs) delim) (strjoin delim (tail strs))
)

mexpr

utest string2int "5" with 5 in
utest string2int "25" with 25 in
utest string2int "314159" with 314159 in

utest int2string 5 with "5" in
utest int2string 25 with "25" in
utest int2string 314159 with "314159" in

utest strindex '%' "a % 5" with Some(2) in
utest strindex '%' "a & 5" with None in
utest strindex 'w' "Hello, world!" with Some(7) in
utest strindex 'w' "Hello, World!" with None in
utest strindex 'o' "Hello, world!" with Some(4) in
utest strindex '@' "Some @TAG@" with Some(4) in

utest strrindex '%' "a % 5" with Some(2) in
utest strrindex '%' "a & 5" with None in
utest strrindex 'w' "Hello, world!" with Some(7) in
utest strrindex 'w' "Hello, World!" with None in
utest strrindex 'o' "Hello, world!" with Some(8) in

utest strsplit "ll" "Hello" with ["He", "o"] in
utest strsplit "ll" "Hellallllo" with ["He", "a", "", "o"] in
utest strsplit "" "Hello" with ["Hello"] in
utest strsplit "lla" "Hello" with ["Hello"] in
utest strsplit "Hello" "Hello" with ["", ""] in

utest strtrim " aaaa   " with "aaaa" in
utest strtrim "   bbbbb  bbb " with "bbbbb  bbb" in
utest strtrim "ccccc c\t   \n" with "ccccc c" in

utest strjoin "--" ["water", "tea", "coffee"] with "water--tea--coffee" in
utest strjoin "--" [] with "" in
utest strjoin "--" ["coffee"] with "coffee" in
utest strjoin "water" ["coffee", "tea"] with "coffeewatertea" in

()
