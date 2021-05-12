include "char.mc"
include "option.mc"
include "seq.mc"
include "math.mc"

let emptyStr : String = ""

let escapeString = lam s. join (map escapeChar s)

utest escapeString "e" with "e"
utest escapeString "0" with "0"
utest escapeString "\n" with "\\n"
utest escapeString "\r" with "\\r"
utest escapeString "\t" with "\\t"

recursive
  let eqString = lam s1. lam s2.
      if neqi (length s1) (length s2)
      then false
      else if null s1
           then true
           else if eqChar (head s1) (head s2)
           then eqString (tail s1) (tail s2)
           else false
end

utest eqString "" "" with true
utest eqString "" "a" with false
utest eqString "a" "" with false
utest eqString "a" "a" with true
utest eqString "a" "aa" with false

-- Lexicographical ordering of strings. ltString s1 s2 is true iff s1 is
-- lexicographically smaller than s2.
recursive
  let ltString: String -> String -> Bool = lam s1. lam s2.
    if null s2 then
      false
    else if null s1 then
      true
    else if eqChar (head s1) (head s2) then
      ltString (tail s1) (tail s2)
    else
      ltChar (head s1) (head s2)
end

-- Returns true iff s1 is lexicographically greater than s2.
let gtString: String -> String -> Bool = lam s1. lam s2. ltString s2 s1

utest ltString "" "" with false
utest ltString "" "A" with true
utest ltString "A" "" with false
utest ltString "A" "B" with true
utest ltString "BA" "B" with false
utest ltString "AB" "B" with true

utest gtString "" "" with false
utest gtString "" "x" with false
utest gtString "x" "" with true
utest gtString "x" "y" with false
utest gtString "yx" "y" with true
utest gtString "xy" "y" with false

-- String comparison giving a total ordering of strings.
-- cmpString s1 s2 returns >0 or <0 if s1 lexicographically
-- greater respectively smaller than s2, else 0.
recursive
  let cmpString: String -> String -> Int = lam s1. lam s2.
    if and (null s1) (null s2) then
      0
    else if null s1 then
      subi 0 1
    else if null s2 then
      1
    else
      let d = cmpChar (head s1) (head s2) in
      match d with 0 then
        cmpString (tail s1) (tail s2)
      else d
end

utest cmpString "" "" with 0
utest cmpString "Hello" "Hello" with 0
utest
  match gti (cmpString "a" "") 0 with true then true else false
  with true
utest
  match lti (cmpString "aa" "aaa") 0 with true then true else false
  with true
utest
  match lti (cmpString "aaa" "aab") 0 with true then true else false
  with true

let str2upper = lam s. map char2upper s
let str2lower = lam s. map char2lower s

let string2int = lam s.
  recursive
  let string2int_rechelper = lam s.
    let len = length s in
    let last = subi len 1 in
    if eqi len 0
    then 0
    else
      let lsd = subi (char2int (get s last)) (char2int '0') in
      let rest = muli 10 (string2int_rechelper (subsequence s 0 last)) in
      addi rest lsd
  in
  match s with [] then 0 else
  if eqChar '-' (head s)
  then negi (string2int_rechelper (tail s))
  else string2int_rechelper s

utest string2int "5" with 5
utest string2int "25" with 25
utest string2int "314159" with 314159
utest string2int "-314159" with (negi 314159)

let int2string = lam n.
  recursive
  let int2string_rechelper = lam n.
    if lti n 10
    then [int2char (addi n (char2int '0'))]
    else
      let d = [int2char (addi (modi n 10) (char2int '0'))] in
      concat (int2string_rechelper (divi n 10)) d
  in
  if lti n 0
  then cons '-' (int2string_rechelper (negi n))
  else int2string_rechelper n

utest int2string 5 with "5"
utest int2string 25 with "25"
utest int2string 314159 with "314159"
utest int2string (negi 314159) with "-314159"

-- 'stringIsInt s' returns true iff 's' is a string representing an integer
let stringIsInt: String -> Bool = lam s.
  eqString s (int2string (string2int s))

utest stringIsInt "" with false
utest stringIsInt "1 " with false
utest stringIsInt " 1" with false
utest stringIsInt "1" with true
utest stringIsInt "-1098" with true

-- Returns an option with the index of the first occurrence of c in s. Returns
-- None if c was not found in s.
let strIndex = lam c. lam s.
  recursive
  let strIndex_rechelper = lam i. lam c. lam s.
    if eqi (length s) 0
    then None ()
    else if eqChar c (head s)
         then Some(i)
         else strIndex_rechelper (addi i 1) c (tail s)
  in
  strIndex_rechelper 0 c s

utest strIndex '%' "a % 5" with Some(2) using optionEq eqi
utest strIndex '%' "a & 5" with None () using optionEq eqi
utest strIndex 'w' "Hello, world!" with Some(7) using optionEq eqi
utest strIndex 'w' "Hello, World!" with None () using optionEq eqi
utest strIndex 'o' "Hello, world!" with Some(4) using optionEq eqi
utest strIndex '@' "Some @TAG@" with Some(5) using optionEq eqi

-- Returns an option with the index of the last occurrence of c in s. Returns
-- None if c was not found in s.
let strLastIndex = lam c. lam s.
  recursive
  let strLastIndex_rechelper = lam i. lam acc. lam c. lam s.
    if eqi (length s) 0 then
      if eqi acc (negi 1)
      then None ()
      else Some(acc)
    else
      if eqChar c (head s)
      then strLastIndex_rechelper (addi i 1) i   c (tail s)
      else strLastIndex_rechelper (addi i 1) acc c (tail s)
  in
  strLastIndex_rechelper 0 (negi 1) c s

utest strLastIndex '%' "a % 5" with Some(2) using optionEq eqi
utest strLastIndex '%' "a & 5" with None () using optionEq eqi
utest strLastIndex 'w' "Hello, world!" with Some(7) using optionEq eqi
utest strLastIndex 'w' "Hello, World!" with None () using optionEq eqi
utest strLastIndex 'o' "Hello, world!" with Some(8) using optionEq eqi
utest strLastIndex '@' "Some @TAG@" with Some(9) using optionEq eqi

-- Splits s on delim
recursive
  let strSplit = lam delim. lam s.
    if or (eqi (length delim) 0) (lti (length s) (length delim))
    then cons s []
    else if eqString delim (subsequence s 0 (length delim))
         then cons [] (strSplit delim (subsequence s (length delim) (length s)))
         else let remaining = strSplit delim (tail s) in
              cons (cons (head s) (head remaining)) (tail remaining)
end

utest strSplit "ll" "Hello" with ["He", "o"]
utest strSplit "ll" "Hellallllo" with ["He", "a", "", "o"]
utest strSplit "" "Hello" with ["Hello"]
utest strSplit "lla" "Hello" with ["Hello"]
utest strSplit "Hello" "Hello" with [emptyStr, ""]

-- Trims s of spaces
let strTrim = lam s.
  recursive
  let strTrim_init = lam s.
    if eqString s ""
    then s
    else if isWhitespace (head s)
         then strTrim_init (tail s)
         else s
  in
  reverse (strTrim_init (reverse (strTrim_init s)))

utest strTrim " aaaa   " with "aaaa"
utest strTrim "   bbbbb  bbb " with "bbbbb  bbb"
utest strTrim "ccccc c\t   \n" with "ccccc c"

-- Joins the strings in strs on delim
recursive
  let strJoin = lam delim. lam strs.
    if eqi (length strs) 0
    then ""
    else if eqi (length strs) 1
         then head strs
         else concat (concat (head strs) delim) (strJoin delim (tail strs))
end

utest strJoin "--" ["water", "tea", "coffee"] with "water--tea--coffee"
utest strJoin "--" [] with emptyStr
utest strJoin "--" ["coffee"] with "coffee"
utest strJoin "water" ["coffee", "tea"] with "coffeewatertea"
