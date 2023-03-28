-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The name library implements an approach to name handling
-- where a name both has a string and a symbol representation.
-- This library is typically used for variable handling
-- and name binding. It is also used in the 'symtable.mc'
-- library.

include "string.mc"
include "seq.mc"

type Name = (String, Symbol)

-- We use the private _noSymbol instead of an option type
-- for performance reasons (no tagging).
let _noSymbol = gensym ()


-- 'nameNoSym x' constructs a new name with string 'x'. The
-- returned name does not contain a symbol.
let nameNoSym : String -> Name =
  lam x. (x, _noSymbol)


-- 'nameSym x' constructs a new name with string 'x' together
-- with a fresh symbol
let nameSym : String -> Name =
  lam x. (x, gensym ())


-- 'nameEqStr n1 n2' returns true if both names 'n1' and 'n2'
-- contain the same string, else false.
let nameEqStr : Name -> Name -> Bool =
  lam n1 : Name. lam n2 : Name. eqString n1.0 n2.0

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _t3 = nameSym "bar"
utest nameEqStr _t1 _t1 with true
utest nameEqStr _t1 _t2 with true
utest nameEqStr _t2 _t3 with false
utest nameEqStr _t1 _t3 with false


-- 'nameHasSym n' returns true if name 'n' has a
-- symbol, else it returns false.
let nameHasSym : Name -> Bool =
  lam n : Name. not (eqsym n.1 _noSymbol)

utest nameHasSym (nameSym "foo") with true
utest nameHasSym (nameNoSym "foo") with false


-- 'nameEqSym n1 n2' returns true if both names 'n1' and 'n2' contain the same
-- symbol. If either 'n1' or 'n2' does not have a symbol, or if the symbols
-- differ, return false.
let nameEqSym : Name -> Name -> Bool =
  lam n1 : Name. lam n2 : Name.
    if nameHasSym n1 then
      if nameHasSym n2 then
        eqsym n1.1 n2.1
      else false
    else false

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _t3 = nameSym "foo"
utest nameEqSym _t1 _t1 with false
utest _t2 with _t2 using nameEqSym
utest nameEqSym _t1 _t2 with false
utest nameEqSym _t2 _t3 with false
utest _t3 with _t3 using nameEqSym

-- 'nameEqSymUnsafe' returns true if names 'n1' and 'n2' contain the same
-- symbols, without checking whether they contain a symbol. This means two
-- unsymbolized names will be considered equal.
--
-- This function is to be used in performance critical situations where we know
-- both names have been symbolized.
let nameEqSymUnsafe : Name -> Name -> Bool = lam n1. lam n2. eqsym n1.1 n2.1

-- 'nameEq n1 n2' returns true if the symbols are equal, or if neither name has
-- a symbol and their strings are equal. Otherwise, return false.
let nameEq : Name -> Name -> Bool =
  lam n1 : Name. lam n2 : Name.
    if nameEqSym n1 n2 then true
    else if nameHasSym n1 then false
    else if nameHasSym n2 then false
    else nameEqStr n1 n2

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _t3 = nameSym "foo"
utest _t1 with _t1 using nameEq
utest _t2 with _t2 using nameEq
utest nameEq _t1 _t2 with false
utest nameEq _t2 _t3 with false
utest _t3 with _t3 using nameEq

-- 'nameSetNewSym n' returns a new name with a fresh symbol.
-- The returned name contains the same string as 'n'.
let nameSetNewSym : Name -> Name =
  lam n : Name. (n.0, gensym ())

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
utest nameEqStr _t1 (nameSetNewSym _t1) with true
utest nameEqSym _t1 (nameSetNewSym _t1) with false
utest nameEqStr _t2 (nameSetNewSym _t2) with true
utest nameEqSym _t2 (nameSetNewSym _t2) with false


-- 'nameSetSym n s' returns a name with the same string as 'n'
-- but with symbol 's'.
let nameSetSym : Name -> Symbol -> Name =
  lam n : Name. lam s. (n.0, s)

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _s = gensym ()
utest nameEqSym _t2 (nameSetSym _t1 _s) with false
utest nameEqSym (nameSetSym _t2 _s) (nameSetSym _t1 _s) with true

-- `nameRemoveSym` returns a name wit the same string as the argument, but
-- without an associated symbol.
let nameRemoveSym : Name -> Name = lam n. (n.0, _noSymbol)

let _t1 = nameSym "Foo"
let _t2 = nameNoSym "Foo"
utest nameHasSym (nameRemoveSym _t1) with false
utest nameEq _t1 _t2 with false 
utest nameEq (nameRemoveSym _t1) _t2 with true

-- 'nameSetStr n str' returns a new name with string 'str' and
-- with the symbol of 'n', if it has a symbol.
let nameSetStr : Name -> String -> Name =
  lam n : Name. lam str. (str, n.1)

let _t1 = nameNoSym "foo"
let _t2 = nameSym "bar"
utest nameEqStr (nameSetStr _t1 "bar") _t2 with true
utest nameEqStr (nameSetStr _t1 "bar") _t1 with false
utest nameEqStr (nameSetStr _t2 "foo") _t1 with true


-- 'nameGetStr n' returns the string of name 'n'
let nameGetStr : Name -> String =
  lam n : Name. n.0

utest nameGetStr (nameNoSym "foo") with "foo"
utest nameGetStr (nameSym "foo") with "foo"


-- 'nameGetSym n' returns optionally the symbol of name 'n'.
-- If 'n' has no symbol, 'None' is returned.
let nameGetSym : Name -> Option Symbol =
  lam n : Name. if eqsym n.1 _noSymbol then None () else Some n.1

let _s = gensym ()
utest nameGetSym (nameNoSym "foo") with None () using optionEq eqsym
utest nameGetSym (nameSetSym (nameNoSym "foo") _s) with Some _s using optionEq eqsym

-- NOTE(Linnea, 2021-01-26): This function is temporarily added for performance
-- experiments. It is not a total ordering since symbols are not ordered.
-- 'nameCmp n1 n2' compares two names lexicographically.
let nameCmp : Name -> Name -> Int =
  lam n1 : Name. lam n2 : Name.
    match nameGetSym n1 with Some a then
      match nameGetSym n2 with Some b then
        subi (sym2hash a) (sym2hash b)
      else negi 1
    else match nameGetSym n2 with Some _ then 1
    else cmpString (nameGetStr n1) (nameGetStr n2)

let _s1 = gensym ()
let _s2 = gensym ()
utest nameCmp (nameSetSym (nameNoSym "foo") _s1) (nameSetSym (nameNoSym "foo") _s1) with 0
utest nameCmp (nameSetSym (nameNoSym "foo") _s1) (nameSetSym (nameNoSym "foo") _s2) with (subi 0 1)
utest nameCmp (nameSetSym (nameNoSym "foo") _s2) (nameSetSym (nameNoSym "foo") _s1) with 1
utest nameCmp (nameNoSym "foo") (nameNoSym "foo") with 0
utest nameCmp (nameNoSym "a") (nameNoSym "A") with 32
utest nameCmp (nameSetSym (nameNoSym "foo") _s1) (nameNoSym "foo") with subi 0 1
utest nameCmp (nameNoSym "foo") (nameSetSym (nameNoSym "foo") _s1) with 1
