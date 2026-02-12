include "hashmap.mc"
include "stdlib.mc"
include "../global/util.mc"

type IncludeSet a = HashMap String a

let includeSetNew : all a. () -> IncludeSet a = lam.
    hashmapEmpty ()

type IncludeSetInsertResult a = {
     inserted: Bool,
     includeSet: IncludeSet a,
     path: String,
     isStdlib: Bool
}

-- Inserts a file path into the IncludeSet
let includeSetInsert : all a. IncludeSet a -> String -> String -> a -> IncludeSetInsertResult a =
    lam set. lam loc. lam includeContent. lam mapValue.

    match goHere (dirname loc) includeContent with { path = path, isStdlib = isStdlib } in

    let res = { inserted = false, includeSet = set, isStdlib = isStdlib, path = path } in

    if hmMem path set then res
    else { res with includeSet = hmInsert path mapValue set, inserted = true }

let includeSetReplace : all a. IncludeSet a -> String -> a -> IncludeSet a = lam set. lam mapKey. lam mapValue.
    hmInsert mapKey mapValue set
    
let includeSetGetValue: all a. IncludeSet a -> String -> Option a = lam set. lam key.
    hmLookup key set
