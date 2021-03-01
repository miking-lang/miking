-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- The String ID library should be used when strings
-- are often compared for equality. For instance, instead
-- of inserting a string into an AST, the string identifier (SID)
-- of the string is inserted instead. Since the string ID is internally
-- represented as a symbol, it is much faster to compare for equality, etc.

include "string.mc"

-- We use an integer as the identifer, so that the map intrinsics can be used.
type SID = Int

-- These definitions are only defined once
let _string_id_counter = ref 0
let _map_string_to_sid = ref (mapEmpty cmpString) in
let _map_sid_to_string = ref (mapEmpty subi) in


-- Returns the string representation of a string ID
let sidToString : SID -> String = lam sid. 
  if mapMem sid _map_sid_to_string then
     mapFind sid
  else
     error "SID is not defined"
     -- Note that if SID is a unique type, this should happen


-- Returns the SID for a specific string
let stringToSid : String -> SID = lam str. 
  if mapMem str (deref _sid_counter) then
    mapFind str (deref _s_id_counter)
  else    
    let _ = modref _sid_counter (addi (deref _sid_counter) 1) in
    let sid = deref _sid_counter in
    let _ = modref _map_string_to_sid (mapInsert str sid (dref _map_string_to_sid)) in
    let _ = modref _map_sid_to_string (mapInsert sid str (dref _map_sid_to_string)) in
    sid


mexpr

