-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The String ID library should be used when strings
-- are often compared for equality. For instance, instead
-- of inserting a string into an AST, the string identifier (SID)
-- of the string is inserted instead. Since the string ID is internally
-- represented as an integer, it is much faster to compare for equality.

include "map.mc"
include "string.mc"

-- Right now, we use an integer as the identifier,
-- so that the map intrinsics can be used.
type SID = Int

let cmpSID = subi
let eqSID = eqi

-- These definitions are only defined once
let _sidCounter = ref 0
let _mapStringToSid = ref (mapEmpty cmpString)
let _mapSidToString = ref (mapEmpty subi)


-- Returns the string representation of a string ID
let sidToString : SID -> String = lam sid.
  mapFindOrElse (lam. error "SID is not defined") sid (deref _mapSidToString)
  -- Note that if SID is a unique type, the error case cannot happen


-- Returns the string ID for a specific string
let stringToSid : String -> SID = lam str.
  mapFindOrElse
    (lam.
       modref _sidCounter (addi (deref _sidCounter) 1);
       let sid = deref _sidCounter in
       modref _mapStringToSid (mapInsert str sid (deref _mapStringToSid));
       modref _mapSidToString (mapInsert sid str (deref _mapSidToString));
       sid)
    str (deref _mapStringToSid)


-- Extracts the length of an underlying string of a SID
let lengthSID : SID -> Int = lam sid. length (sidToString sid)


mexpr

let sid1 = stringToSid "Foo" in
utest sid1 with sid1 in
utest sidToString sid1 with "Foo" in

utest cmpSID sid1 sid1 with 0 in
utest eqSID sid1 sid1 with true in
utest lengthSID sid1 with 3 in

let sid2 = stringToSid "Bar text" in
utest sid2 with sid2 in
utest sid2 with sid1 using neqi in
utest sidToString sid2 with "Bar text" in
utest sidToString sid1 with "Foo" in
utest sidToString sid1 with sidToString sid2 using lam x. lam y. not (eqString x y) in

utest eqi (cmpSID sid1 sid2) 0 with false in
utest eqSID sid1 sid2 with false in
utest lengthSID sid2 with 8 in

let sid3 = stringToSid "Foo" in
utest sid1 with sid3 in
utest sidToString sid1 with "Foo" in
utest sidToString sid2 with "Bar text" in
utest sidToString sid3 with "Foo" in

utest lengthSID sid3 with 3 in

()
