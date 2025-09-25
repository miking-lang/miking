-- # IncludeSet Module
--
-- The IncludeSet provides utilities to track which files have been visited
-- during code parsing/lexing. It stores each file name in a hashmap as a key,
-- mapped with a value provided as a parameter. It is later used to map each
-- path to its AST.
--
-- When inserting a new name, the IncludeSet resolves the actual full path of
-- the file from a given location. It also computes, throughout its lifetime, a
-- common prefix of all resolved paths to help reduce page URL sizes.

include "hashmap.mc"
include "stdlib.mc"
include "../global/util.mc"

-- A set of included files with metadata.
type IncludeSet a =
    {
        baseLoc: String,
        set: HashMap String a,
        prefix: String,
        programStartPos: String
    }

-- Creates a new IncludeSet with a given base location.
let includeSetNew : all a. String -> IncludeSet a = lam baseLoc.
    { baseLoc = baseLoc, set = hashmapEmpty (), prefix = baseLoc, programStartPos = sysGetCwd () }

-- Returns the current prefix stored in the IncludeSet.
let includeSetPrefix : all a. IncludeSet a -> String = lam set. set.prefix

-- Result type for inserting a new element in the IncludeSet.
type IncludeSetInsertResult a = { inserted: Bool, includeSet: IncludeSet a, path: String, isStdlib: Bool }

-- Inserts a file path into the IncludeSet, resolving absolute paths and updating the prefix.
let includeSetInsert : all a. IncludeSet a -> String -> String -> a -> IncludeSetInsertResult a = lam set. lam loc. lam includeContent. lam mapValue.
    match goHere (dirname loc) includeContent with { path = path, isStdlib = isStdlib } in
    match goHere set.programStartPos path with { path = absPath, isStdlib = isStdlib } in

    let set = if isStdlib then set else  { set with prefix = strLongestCommonPrefix (dirname absPath) set.prefix } in
    
    let res = { inserted = false, includeSet = set, isStdlib = isStdlib, path = path } in
    if hmMem path set.set then res
    else { res with includeSet = { set with set = hmInsert path mapValue set.set }, inserted = true }

-- Replaces or inserts a value in the IncludeSet with the given key.
let includeSetReplace : all a. IncludeSet a -> String -> a -> IncludeSet a = lam set. lam mapKey. lam mapValue.
    { set with set = hmInsert mapKey mapValue set.set }
    
-- Looks up a value in the IncludeSet by key.
let includeSetGetValue: all a. IncludeSet a -> String -> Option a = lam set. lam key.
    hmLookup key set.set
