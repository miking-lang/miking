-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The String ID library should be used when strings
-- are often compared for equality. For instance, instead
-- of inserting a string into an AST, the string identifier (SID)
-- of the string is inserted instead. Since the string ID is internally
-- represented as an integer, it is much faster to compare for equality.

include "string.mc"

-- Right now, we use an integer as the identifier,
-- so that the map intrinsics can be used.
type SID = Int

-- These definitions are only defined once
let _sidCounter = ref 0 
let _mapStringToSid = ref (mapEmpty cmpString) 
let _mapSidToString = ref (mapEmpty subi) 


-- Returns the string representation of a string ID
let sidToString : SID -> String = lam sid. 
  if mapMem sid (deref _mapSidToString) then
     mapFind sid (deref _mapSidToString)
  else
     error "SID is not defined"
     -- Note that if SID is a unique type, this cannot happen


-- Returns the string ID for a specific string
let stringToSid : String -> SID = lam str. 
  if mapMem str (deref _mapStringToSid)  then
    mapFind str (deref _mapStringToSid)
  else    
    modref _sidCounter (addi (deref _sidCounter) 1);
    let sid = deref _sidCounter in
    modref _mapStringToSid (mapInsert str sid (deref _mapStringToSid));
    modref _mapSidToString (mapInsert sid str (deref _mapSidToString));
    sid


mexpr

let sid1 = stringToSid "Foo" in
utest sid1 with sid1 in
utest sidToString sid1 with "Foo" in

let sid2 = stringToSid "Bar text" in
utest sid2 with sid2 in
utest sid2 with sid1 using neqi in
utest sidToString sid2 with "Bar text" in
utest sidToString sid1 with "Foo" in
utest sidToString sid1 with sidToString sid2 using lam x. lam y. not (eqString x y) in

let sid3 = stringToSid "Foo" in
utest sid1 with sid3 in
utest sidToString sid1 with "Foo" in
utest sidToString sid2 with "Bar text" in
utest sidToString sid3 with "Foo" in

()
