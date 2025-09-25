-- # Small string & hashmap utilities
--
-- A collection of helper functions:
--
-- These utilities simplify common operations used across other modules.

include "string.mc"
include "hashmap.mc"
include "sys.mc"
include "stdlib.mc"
include "common.mc"
include "ext/file-ext.mc"

-- Changes the extension of a file.
-- If the file has an extension, it's replaced; if not, the extension is added.
-- Example: changeExt "test.txt" "md" => "test.md"
let changeExt : (String -> String -> String) = lam fileName. lam ext.
    match findiLast (eqc '.') fileName with Some i then
        concat (subsequence fileName 0 (addi 1 i)) ext
    else
        concat fileName (cons '.' ext)

utest changeExt "file.txt" "md" with "file.md"
utest changeExt "noext" "md" with "noext.md"

-- Splits an array `arr` into { left, right } at the first element matching predicate `f`.
-- The matched element goes in `left`.
let splitOnL : all a. (a -> Bool) -> [a] -> { left: [a], right: [a] } = lam f. lam arr.
    recursive let work = lam arr.
        switch arr
        case [] then { left = [], right = [] }
        case [x] ++ rest then
            if f x then
                { left = [x], right = rest }      
            else
                let res = work rest in
                { res with left = cons x res.left }
        end in
    work arr

utest splitOnL (lam x. eqi x 3) [1,2,3,4,5] with { left = [1,2,3], right = [4,5] }
utest splitOnL (lam x. eqi x 9) [1,2,3] with { left = [1,2,3], right = [] }
utest splitOnL (lam x. true) [1,2,3] with { left = [1], right = [2,3] }
    
-- Splits an array `arr` into { left, right } just before the first element matching predicate `f`.
-- The matched element stays in `right`.
let splitOnR : all a. (a -> Bool) -> [a] -> { left: [a], right: [a] } = lam f. lam arr.
    recursive let work = lam arr.
        switch arr
        case [] then { left = [], right = [] }
        case [x] ++ rest then
            if f x then
                { left = [], right = arr }      
            else
                let res = work rest in
                { res with left = cons x res.left }
        end in
    work arr

utest splitOnR (lam x. eqi x 3) [1,2,3,4,5] with { left = [1,2], right = [3,4,5] }
utest splitOnR (lam x. eqi x 9) [1,2,3] with { left = [1,2,3], right = [] }
utest splitOnR (lam x. true) [1,2,3] with { left = [], right = [1,2,3] }

let hmTraits = hashmapStrTraits
let hmInsert = lam x. hashmapInsert hmTraits x
let hmMem = lam x. hashmapMem hmTraits x
let hmValues = lam x. hashmapValues hmTraits x
let hmKeys = lam x. hashmapKeys hmTraits x
let hmLookup = lam x. hashmapLookup hmTraits x
let hmLen = lam x. hashmapCount hmTraits x

-- Normalizes a file path by resolving '.', '..', and redundant slashes.
-- Supports both absolute and relative paths.
let normalizePath = lam path.
    let isAbsolute = match path with "/" ++ s then true else false in
    let components = strSplit "/" path in
    recursive let process = lam comps. lam stack.
        switch comps
        case [] then stack
        case ["."] ++ rest then process rest stack
        case [""] ++ rest then process rest stack
        case [".."] ++ rest then
            (switch stack
             case ([] | [".."] ++ _) then process rest (cons ".." stack)
             case [_] ++ tl then process rest tl end)
        case [comp] ++ rest then process rest (cons comp stack) end
    in
    let cleaned = reverse (process components []) in
    let result = strJoin "/" cleaned in
    if isAbsolute then cons '/'  result
    else result

utest normalizePath "repo1/../repo2" with "repo2"
utest normalizePath "/repo1/../repo2" with "/repo2"
utest normalizePath "../../repo2" with "../../repo2"
utest normalizePath "./a/./b/../c" with "a/c"
utest normalizePath "/a/b/../../c" with "/c"


-- Resolves a path based on current location and target.
-- If the target is absolute, it is returned normalized.
-- If the file exists at the concatenated location, it's returned.
-- Otherwise, the target is assumed to be from the standard library.
let goHere : String -> String -> { path: String, isStdlib: Bool } = lam currentLoc. lam target.
    let currentLoc = match currentLoc with "" then "./" else currentLoc in
    match target with "" then { path = currentLoc, isStdlib = false } else
    let path = if strStartsWith "/" target then target
               else join [currentLoc, "/", target] in
    if sysFileExists path then
        { path = normalizePath path, isStdlib = strStartsWith stdlibLoc path }
    else
        { path = join [stdlibLoc, "/", target], isStdlib = true }


-- Try to open a file in a String, panic if it fails
let readOrNever : String -> String = lam fileName.
    match fileReadOpen fileName with Some rc then
        let s = fileReadString rc in
        fileReadClose rc;
        s
    else
        error (join ["Failed to read a file: file ", fileName, " doesn't exists."])

-- Returns the longest common prefix between two strings.
let strLongestCommonPrefix : String -> String -> String = lam a. lam b.
    match a with "" then ""
    else match b with "" then ""
    else match findi (lam x. neqChar x.0 x.1) (zip a b) with Some i then subsequence a 0 i
    else if gti (length a) (length b) then b
    else a


-- Concatenates two lists if the first one does not satisfy the given predicate.
let concatIfNot : all a. [a] -> ([a] -> Bool) -> [a] -> [a] =
    lam x1. lam f. lam x2. if not (f x1) then concat x1 x2 else x1


-- Counts how many elements of a list satisfy the given predicate.
let count : all a. (a -> Bool) -> [a] -> Int = lam f. lam arr.
    foldl (lam counter. lam x. if f x then addi 1 counter else counter) 0 arr


-- Trims whitespace and newlines at the beginning and end of a string.
let strFullTrim = lam s.
  recursive
  let work = lam s.
    if eqString s ""
    then s
    else match head s with '\n' | ' ' | '\t' then work (tail s)
    else s
  in
  reverse (work (reverse s))

let pwd = sysGetCwd ()
