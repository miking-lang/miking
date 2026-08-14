-- A collection of helper functions

include "string.mc"
include "hashmap.mc"
include "sys.mc"
include "stdlib.mc"
include "common.mc"
include "basic-types.mc"
include "seq.mc"
include "option.mc"
include "char.mc"
include "bool.mc"

-- Changes the extension of a file.
-- If the file has an extension, it s replaced; if not, the extension is added.
-- Example: changeExt "test.txt" "md" => "test.md"
let changeExt : (String -> String -> String) = lam fileName. lam ext.
    match findiLast (eqc '.') fileName with Some i then
        concat (subsequence fileName 0 (addi 1 i)) ext
    else
        concat fileName (cons '.' ext)

utest changeExt "file.txt" "md" with "file.md"
utest changeExt "noext" "md" with "noext.md"

-- Splits an array `seq` into (left, right) at the first element matching predicate `f`.
-- The matched element goes in `left`.
-- If nothing matches, the function returns ('seq', []).
let splitOnL : all a. (a -> Bool) -> [a] -> ([a], [a])  = lam p. lam seq.
    match findi p seq
    with Some i then splitAt seq (addi i 1)
    else (seq, [])

utest splitOnL (lam x. eqi x 3) [1,2,3,4,5] with ([1,2,3], [4,5])
utest splitOnL (lam x. eqi x 3) [1,2,3] with ([1,2,3], [])
utest splitOnL (lam x. eqi x 9) [1,2,3] with ([1,2,3], [])
utest splitOnL (lam x. true) [1,2,3] with ([1], [2,3])
    
-- Splits an array `arr` into (left, right) just before the first element matching predicate `f`.
-- The matched element stays in `right`.
-- If nothing matches, the function returns ('seq', []).
let splitOnR : all a. (a -> Bool) -> [a] -> ([a], [a]) = lam p. lam seq.
    match findi p seq
    with Some i then splitAt seq i
    else (seq, [])

utest splitOnR (lam x. eqi x 3) [1,2,3,4,5] with ([1,2], [3,4,5]) 
utest splitOnR (lam x. eqi x 9) [1,2,3] with ([1,2,3], [])
utest splitOnR (lam x. eqi x 3) [1,2,3] with ([1,2], [3])
utest splitOnR (lam x. true) [1,2,3] with ([], [1,2,3])
      

let hmTraits = hashmapStrTraits
let hmInsert = lam x. hashmapInsert hmTraits x
let hmMem = lam x. hashmapMem hmTraits x
let hmValues = lam x. hashmapValues hmTraits x
let hmKeys = lam x. hashmapKeys hmTraits x
let hmLookup = lam x. hashmapLookup hmTraits x
let hmLen = lam x. hashmapCount hmTraits x
let hmRemove = lam x. hashmapRemove hmTraits x

let hmIntTraits : HashMapTraits Int =
  { eq = eqi,
    hashfn = lam x. x }
let hmIntInsert = lam x. hashmapInsert hmIntTraits x
let hmIntMem = lam x. hashmapMem hmIntTraits x
let hmIntValues = lam x. hashmapValues hmIntTraits x
let hmIntKeys = lam x. hashmapKeys hmIntTraits x
let hmIntLookup = lam x. hashmapLookup hmIntTraits x
let hmIntLen = lam x. hashmapCount hmIntTraits x



-- Normalizes a file path by resolving '.', '..', and redundant slashes.
-- Supports both absolute and relative paths.
-- normalizePath preserves leading '..' in relative paths
-- and never removes path components past the root.
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
-- If the file exists at the concatenated location, it s returned.
-- Otherwise, the target is assumed to be from the standard library.
let goHere : String -> String -> { path: String, isStdlib: Bool } = lam currentLoc. lam target.
    let currentLoc = match currentLoc with "" then "./" else currentLoc in

    match target with "" then { path = currentLoc, isStdlib = false } else

    let path =
        if strStartsWith "/" target then target
        else join [currentLoc, "/", target]
    in

    if sysFileExists path then
        { path = normalizePath path, isStdlib = strStartsWith stdlibLoc path }
    else
        { path = join [stdlibLoc, "/", target], isStdlib = true }


-- Counts how many elements of a list satisfy the given predicate.
let count : all a. (a -> Bool) -> [a] -> Int = lam f. lam arr.
    foldl (lam counter. lam x. if f x then addi 1 counter else counter) 0 arr

-- Trims whitespace and newlines at the beginning and end of a string.
let strFullTrim = lam s.
  recursive
  let trim = lam s.
    if null s then s
    else match head s with '\r' | '\n' | ' ' | '\t' then trim (tail s)
    else s
  in
  trim (reverse (trim (reverse s)))

let pwd = sysGetCwd ()


let isFolder : String -> Bool = lam path.
  if eqi (_commandList ["test", "-d", path]) 0 then true else false

let folderFetchMcFiles : String -> Option [String] = lam dir.
  let res = sysRunCommand ["find", dir, "-type", "f", "-name", "'*.mc'"] "" "." in
  if neqi res.returncode 0 then None {} else
  let out = strTrim res.stdout in
  Some (if null out then [] else strSplit "\n" out)

    

let strSplitOnce : all a. String -> Char -> Option (String, String)  = lam s. lam mid.
    optionMap (lam i.
        (subsequence s 0 i, subsequence s (addi 1 i) (length s))
       ) (findi (eqChar mid) s)

let strCount : String -> Char -> Int = lam s. lam c. length (filter (eqChar c) s)

let pathIsInStdlib : String -> Bool =
    lam path.
    switch path
    case [] then false
    case "/" ++ _ then strStartsWith stdlibLoc path
    case _ then
         let abs = normalizePath (join [pwd, "/", path]) in
         strStartsWith stdlibLoc abs
    end

let strContains : String -> String -> Bool = lam needle. lam haystack.
  let n = length haystack in
  let m = length needle in
  if eqi m 0 then true else
  if lti n m then false else
    recursive let work = lam i.
      if gti i (subi n m) then false
      else if eqStringSlice needle haystack i m
      then true
      else work (addi i 1)
    in work 0

utest strContains "ell" "Hello" with true
utest strContains "Hello" "Hello" with true
utest strContains "Hello" "Helloo" with true
utest strContains "xyz" "Hello" with false

-- Empty needle cases
utest strContains "" "Hello" with true
utest strContains "" "" with true

-- Empty haystack cases
utest strContains "abc" "" with false
utest strContains "H" "" with false

-- Needle longer than haystack
utest strContains "HelloWorld" "Hello" with false

-- Occurrence at start
utest strContains "He" "Hello" with true

-- Occurrence at end
utest strContains "lo" "Hello" with true

-- Overlapping patterns
utest strContains "ana" "banana" with true
utest strContains "nana" "banana" with true
utest strContains "naan" "banana" with false

let strStripEndingNewlines =
  lam s.
  let reversed = reverse s in
  match splitOnR (lam c. not (eqChar '\n' c)) reversed with (_, s) in
  reverse s

-- Returns the longest common prefix between two strings.
let strLongestCommonPrefix : String -> String -> String = lam a. lam b.
    match a with "" then ""
    else match b with "" then ""
    else match findi (lam x. neqChar x.0 x.1) (zip a b) with Some i then subsequence a 0 i
    else if gti (length a) (length b) then b
    else a

let strLongestCommonPrefixArray : [String] -> String =
    lam s.
    if null s then "" else
    foldl strLongestCommonPrefix (head s) (tail s) 

let strSkipLines : String -> Int -> Option (String, String) =
    recursive let work =
        lam skiped. lam s. lam n.

        if eqi n 0 then Some (reverse skiped, s) else
        if null s then None {} else
        
        let c = head s in
        let updatedN = if eqChar c '\n' then (subi n 1) else n in
        work (cons c skiped) (tail s) updatedN
    in
    work ""

let strWalkTo : String -> Int -> Int -> (String, String) =
    lam s. lam x. lam y.
    optionGetOr (s, "")
    (optionBind (strSkipLines s y) (lam skipedLines.
        match skipedLines with (skiped, rest) in
        if lti x (length rest) then
            match splitAt rest x with (skiped2, rest) in
            Some (concat skiped skiped2, rest)
        else None {}))

let sysGetHome : () -> Option String = lam. sysGetEnv "HOME"

let hashmapWithCapacity : all k. all v. Int -> HashMap k v = lam n.
  {buckets = make n [],
   nelems = 0}

let pathConcat : String -> String -> String =
    lam p1. lam p2.
    normalizePath (join [p1, "/", p2])

let pathIsAbsolute : String -> Bool = strStartsWith "/"

let pathRemoveHome : String -> String =
    lam p.
    if strStartsWith "~/" p then
        match sysGetHome ()
        with Some h then pathConcat h (tail p)
        else p
    else p

-- Here are some function relying on the shell.
-- TODO: Replace those functions with real miking code.
let sysMoveDirContents : String -> String -> ReturnCode = lam p1. lam p2.
  _commandList [
    "bash", "-c",
    join [
        "\"",
        "set -e;",
        "mkdir -p \"", p1, "\" && ",
        "mv -f \"", p2, "\"/* \"", p1, "\"/ 2>/dev/null || true", " && ",
        "rm -rf \"", p2, "\"",
        "\""]
  ]

let sysRemoveSrcFiles : String -> ReturnCode = lam dir.
  _commandList [
    "bash", "-c",
    join [
        "\"",
        "set -e;",
        "rm -f ", dir, "/*.js ", dir, "/*.css ",
        dir, "/*.tsx ", dir, "/*.jsx ",
        "2>/dev/null",
        "\""
    ]
  ]
