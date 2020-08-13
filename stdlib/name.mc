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

-- We use the private _noNymbol instead of an option type
-- for performance reason (no tagging).
let _noSymbol = gensym ()


-- 'nameNoSym x' constructs a new name with string 'x'. The
-- returned name does not contain a symbol.
let nameNoSym : String -> Name =
  lam x. (x, _noSymbol)

utest nameNoSym "foo" with nameNoSym "foo"


-- 'nameSym x' constructs a new name with string 'x' together
-- with a fresh symbol
let nameSym : String -> Name =
  lam x. (x, gensym ())

let _t = nameSym "foo"
utest _t with _t


-- 'nameEqSym n1 n2' returns true if both names 'n1' and 'n2'
-- contain the same symbol or if none of them has a symbol.
-- If not, the function returns false.
let nameEqSym : Name -> Name -> Bool =
  lam n1. lam n2. eqs n1.1 n2.1

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _t3 = nameSym "foo"
utest nameEqSym _t1 _t1 with true
utest nameEqSym _t2 _t2 with true
utest nameEqSym _t1 _t2 with false
utest nameEqSym _t2 _t3 with false


-- 'nameEqStr n1 n2' returns true if both names 'n1' and 'n2'
-- contain the same string, else false.
let nameEqStr : Name -> Name -> Bool =
  lam n1. lam n2. eqstr n1.0 n2.0

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
  lam n. not (eqs n.1 _noSymbol)

utest nameHasSym (nameSym "foo") with true
utest nameHasSym (nameNoSym "foo") with false


-- 'nameSetNewSym n' returns a new name with a fresh symbol.
-- The returned name contains the same string as 'n'.
let nameSetNewSym : Name -> Name =
  lam n. (n.0, gensym ())

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
utest nameEqStr _t1 (nameSetNewSym _t1) with true
utest nameEqSym _t1 (nameSetNewSym _t1) with false
utest nameEqStr _t2 (nameSetNewSym _t2) with true
utest nameEqSym _t2 (nameSetNewSym _t2) with false


-- 'nameSetSym n s' returns a name with the same string as 'n'
-- but with symbol 's'.
let nameSetSym : Name -> Symbol -> Name =
  lam n. lam s. (n.0, s)

let _t1 = nameNoSym "foo"
let _t2 = nameSym "foo"
let _s = gensym ()
utest nameEqSym _t2 (nameSetSym _t1 _s) with false
utest nameEqSym (nameSetSym _t2 _s) (nameSetSym _t1 _s) with true


-- 'nameSetStr n str' returns a new name with string 'str' and
-- with the symbol of 'n', if it has a symbol.
let nameSetStr : Name -> String -> Name =
  lam n. lam str. (str, n.1)

let _t1 = nameNoSym "foo"
let _t2 = nameSym "bar"
utest nameEqStr (nameSetStr _t1 "bar") _t2 with true
utest nameEqStr (nameSetStr _t1 "bar") _t1 with false
utest nameEqStr (nameSetStr _t2 "foo") _t1 with true


-- 'nameGetStr n' returns the string of name 'n'
let nameGetStr : Name -> String =
  lam n. n.0

utest nameGetStr (nameNoSym "foo") with "foo"
utest nameGetStr (nameSym "foo") with "foo"


-- 'nameGetSym n' returns optionally the symbol of name 'n'.
-- If 'n' has no symbol, 'None' is returned.
-- TODO: Update signature when we have polymorphic types.
let nameGetSym : Name -> OptionSymbol =
  lam n. if eqs n.1 _noSymbol then None () else Some n.1

let _s = gensym ()
utest nameGetSym (nameNoSym "foo") with None ()
utest nameGetSym (nameSetSym (nameNoSym "foo") _s) with Some _s
