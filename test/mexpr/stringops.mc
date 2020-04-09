// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test implementation of simple string operations

mexpr

let head = lam seq. get seq 0 in
let tail = lam seq. slice seq 1 (length seq) in

recursive
  let map = lam f. lam seq.
    if eqi (length seq) 0 then []
    else cons (f (head seq)) (map f (tail seq))
in

let eqchar = lam c1. lam c2. eqi (char2int c1) (char2int c2) in
let ltchar = lam c1. lam c2. lti (char2int c1) (char2int c2) in
let gtchar = lam c1. lam c2. gti (char2int c1) (char2int c2) in
let leqchar = lam c1. lam c2. leqi (char2int c1) (char2int c2) in
let geqchar = lam c1. lam c2. geqi (char2int c1) (char2int c2) in

recursive
  let eqstr = lam s1. lam s2.
    if neqi (length s1) (length s2)
    then false
    else if eqi (length s1) 0
         then true
         else if eqchar (head s1) (head s2)
         then eqstr (tail s1) (tail s2)
         else false
in

// Convert a character to upper case
let char2upper = (lam c.
	if and (geqchar c 'a') (leqchar c 'z')
	then (int2char (subi (char2int c) 32))
	else c
) in

// Convert a character to lower case
let char2lower = (lam c.
	if and (geqchar c 'A') (leqchar c 'Z')
	then (int2char (addi (char2int c) 32))
	else c
) in

let str2upper = lam s. map char2upper s in
let str2lower = lam s. map char2lower s in

recursive
  // Splits the string on the entered delimiter
  let strsplit = lam delim. lam s.
    if or (eqi (length delim) 0) (lti (length s) (length delim))
    then cons s []
    else if eqstr delim (slice s 0 (length delim))
         then cons [] (strsplit delim (slice s (length delim) (length s)))
         else let remaining = strsplit delim (tail s) in
              cons (cons (head s) (head remaining)) (tail remaining)
in

// Trims a string of spaces
recursive
  let strtrim_init = lam s.
    if eqstr s ""
    then s
    else if eqchar (head s) ' '
         then strtrim_init (tail s)
         else s
in
let strtrim = lam s. reverse (strtrim_init (reverse (strtrim_init s))) in

recursive
  // Join a list of strings with a common delimiter
  let strjoin = lam delim. lam slist.
    if eqi (length slist) 0
    then ""
    else if eqi (length slist) 1
         then head slist
         else concat (concat (head slist) delim) (strjoin delim (tail slist))
in
let strflatten = lam s. strjoin "" s in


utest str2upper "Hello, world!" with "HELLO, WORLD!" in
utest str2lower "Foo... BAR!" with "foo... bar!" in

utest (eqstr "Hello" "Hello") with true in
utest (cons "Hello" []) with ["Hello"] in

utest (strsplit "ll" "Hello") with ["He", "o"] in
utest (strsplit "ll" "Hellallllo") with ["He", "a", "", "o"] in
utest (strsplit "" "Hello") with ["Hello"] in
utest (strsplit "lla" "Hello") with ["Hello"] in

utest strtrim "    good afternoon!  " with "good afternoon!" in
utest (map strtrim (strsplit "," "eggs, flour, milk, sugar")) with ["eggs", "flour", "milk", "sugar"] in
utest strsplit ", " "eggs, flour, milk, sugar" with ["eggs", "flour", "milk", "sugar"] in
utest strjoin "--" ["water", "tea", "coffee"] with "water--tea--coffee" in
utest strflatten (strsplit "." (strflatten (strsplit "," "a.b,c"))) with "abc" in

()
