-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- This library implements a symbol table. The
-- implementation is based on  module 'name.mc'.


include "name.mc"
include "seq.mc"

type SymTable = [Name]


-- Defines an empty symbol table
let symtableEmpty = []


-- 'symtableAdd n t' returns a record  '{name:Name, table:SymTable)' where
-- field 'table' has been extended with name 'n' if it did not
-- already exist in 't'. If the string of 'n' existed, then
-- the returned table is the same as table 't'. In both cases,
-- field 'name' has the string of 'n' with a unique symbol.
let symtableAdd : Name -> SymTable -> {name: Name, table: SymTable} =
  lam n. lam t.
    match find (nameEqStr n) t with Some n2 then
      {name = n2, table = t}
    else
      let n2 = nameSetNewSym n in
      {name = n2, table = cons n2 t}

let _r1 = symtableAdd (nameNoSym "foo") []
let _r2 = symtableAdd (nameNoSym "bar") _r1.table
let _r3 = symtableAdd (nameNoSym "foo") _r2.table
utest nameEqStr (_r1.name) (nameNoSym "foo") with true
utest nameEqStr (_r2.name) (nameNoSym "bar") with true
utest nameEqStr (_r3.name) (nameNoSym "foo") with true
utest nameEqStr (_r3.name) (nameNoSym "else") with false


-- 'symbtableMem n t' returns true if the string of 'n'
-- exists in table 't'.
let symtableMem : Name -> SymTable -> Bool =
  lam n. lam t.
    any (nameEqStr n) t

utest symtableMem (nameNoSym "foo") _r1.table with true
utest symtableMem (nameNoSym "foo") _r3.table with true
utest symtableMem (nameNoSym "bar") _r3.table with true
utest symtableMem (nameNoSym "else") _r3.table with false


-- 'symtableSize t' returns the number of names in
-- the symbol table 't'.
let symtableSize : SymTable -> Int =
  lam t. length t

utest symtableSize symtableEmpty with 0
utest symtableSize _r1.table with 1
utest symtableSize _r2.table with 2
utest symtableSize _r3.table with 2


-- 'symtableRemove n t' returns a new table where names with strings
-- equal to the string of 'n' are removed from 't'.
let symtableRemove : Name -> SymTable -> SymTable =
  lam n. lam t.
    filter (lam n2. not (nameEqStr n n2)) t

utest symtableMem (nameNoSym "foo") _r3.table with true
utest symtableMem (nameNoSym "foo") (symtableRemove (nameNoSym "foo") _r3.table) with false
utest symtableSize (symtableRemove (nameNoSym "foo") _r3.table) with 1
utest symtableSize (symtableRemove (nameNoSym "nothing") _r3.table) with 2
