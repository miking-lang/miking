-- Allocation of readable ECMAScript identifiers for MExpr `Name`s.
--
-- By the time the AST reaches the backend it has been symbolized, so names that
-- were distinct in the source may share a string, and the symbolizer has often
-- rewritten them (`a` becomes `a10`). Recovering short, source-like identifiers
-- matters more for output readability than anything else in the pipeline, so
-- this allocator hands out the plain `nameGetStr` wherever it can and only
-- disambiguates when there is a genuine collision.

include "basic-types.mc"
include "bool.mc"
include "char.mc"
include "map.mc"
include "name.mc"
include "seq.mc"
include "set.mc"
include "string.mc"

-- Words that cannot be used as binding names in an ECMAScript module.
--
-- Generated modules are strict-mode code, so this includes the strict-mode
-- reserved words and the restricted identifiers `arguments` and `eval`. It also
-- includes a few globals that are not reserved but whose shadowing would be a
-- silent bug -- notably `undefined`, which is how unit is represented and which
-- ordinary code is otherwise free to rebind.
let esReservedWords : [String] = [
  -- ECMA-262 reserved words
  "await", "break", "case", "catch", "class", "const", "continue", "debugger",
  "default", "delete", "do", "else", "enum", "export", "extends", "false",
  "finally", "for", "function", "if", "import", "in", "instanceof", "new",
  "null", "return", "super", "switch", "this", "throw", "true", "try", "typeof",
  "var", "void", "while", "with", "yield",
  -- Additionally reserved in strict mode
  "implements", "interface", "let", "package", "private", "protected", "public",
  "static",
  -- Restricted identifiers in strict mode
  "arguments", "eval",
  -- Not reserved, but unsafe to shadow in generated code
  "globalThis", "Infinity", "NaN", "undefined",
  -- Host globals that generated code and the runtime refer to directly, via
  -- `ESEGlobal`. Reserving them means no MExpr binding can shadow one.
  "Array", "BigInt", "Boolean", "Error", "JSON", "Map", "Math", "Number",
  "Object", "Promise", "RangeError", "Set", "String", "Symbol", "TypeError",
  "console", "process"
]

type ESNameEnv = {
  -- The identifier assigned to each name seen so far.
  names : Map Name String,
  -- Every identifier handed out, plus any that were reserved up front.
  used : Set String,
  -- The next suffix to try for each base string, so that allocating a name
  -- does not rescan the suffixes already handed out for it.
  next : Map String Int
}

let esNameEnvEmpty : ESNameEnv = {
  names = mapEmpty nameCmp,
  used = setOfSeq cmpString esReservedWords,
  next = mapEmpty cmpString
}

-- Claims `str` so that no name is ever allocated it. Used for identifiers that
-- generated code refers to but that are not themselves MExpr names.
let esNameReserve : ESNameEnv -> String -> ESNameEnv =
  lam env. lam str. { env with used = setInsert str env.used }

-- Rewrites an MExpr name string into something that is at least a syntactically
-- valid identifier. MExpr permits characters JS does not (`'` is common, and
-- the loader emits names such as `#var"1"` whose string is just `1`).
let esSanitize : String -> String = lam str.
  let keep = lam c. if isAlphanum c then c else if eqc c '_' then c else '_' in
  let str = map keep str in
  match str with [] then "_"
  else if isDigit (head str) then cons '_' str
  else str

-- Is `str` usable as a bare property key, as in `{ foo: 1 }`? Reserved words
-- are fine in that position, so only the character shape matters.
let esIsIdentLike : String -> Bool = lam str.
  match str with [first] ++ rest then
    if or (isAlpha first) (or (eqc first '_') (eqc first '$')) then
      forAll (lam c. or (isAlphanum c) (or (eqc c '_') (eqc c '$'))) rest
    else false
  else false

-- Returns the identifier for `id`, allocating one on first use.
--
-- The first name to ask for a given string gets it unadorned; later names that
-- sanitize to the same string get a `_1`, `_2`, ... suffix.
--
-- The search resumes from the last suffix handed out for that base rather than
-- restarting at zero, which would make allocation quadratic in the number of
-- names sharing a string -- `mi.mc` has tens of thousands sharing `t`, `x` and
-- the pattern lowerer's `_target`. The `used` check stays, since a suffixed
-- identifier can also be claimed directly, by an MExpr name spelled `x_1` or
-- by `esNameReserve`.
let esNameGet : ESNameEnv -> Name -> (ESNameEnv, String) =
  lam env. lam id.
  match mapLookup id env.names with Some str then (env, str)
  else
    let base = esSanitize (nameGetStr id) in
    recursive let pick = lam i.
      let candidate = if eqi i 0 then base else join [base, "_", int2string i] in
      if setMem candidate env.used then pick (addi i 1) else (candidate, i)
    in
    let start = match mapLookup base env.next with Some i then i else 0 in
    match pick start with (str, i) in
    ({ names = mapInsert id str env.names
     , used = setInsert str env.used
     , next = mapInsert base (addi i 1) env.next }, str)

-- `mapAccumL`-friendly variant, for printing parameter lists and the like.
let esNameGetMany : ESNameEnv -> [Name] -> (ESNameEnv, [String]) =
  lam env. lam ids. mapAccumL esNameGet env ids

mexpr

utest esSanitize "a" with "a" in
utest esSanitize "int2string" with "int2string" in
utest esSanitize "x'" with "x_" in
utest esSanitize "1" with "_1" in
utest esSanitize "" with "_" in
utest esSanitize "_target" with "_target" in

-- A name keeps its source string when nothing else has claimed it.
let a = nameSym "a" in
match esNameGet esNameEnvEmpty a with (env, s) in
utest s with "a" in

-- Asking again is stable.
match esNameGet env a with (env, s2) in
utest s2 with "a" in

-- A different name with the same string is disambiguated, not merged.
let a2 = nameSym "a" in
match esNameGet env a2 with (env, s3) in
utest s3 with "a_1" in

-- Suffixes keep counting up for further names with that string.
let a3 = nameSym "a" in
match esNameGet env a3 with (env, s4) in
utest s4 with "a_2" in

-- An identifier claimed directly is skipped rather than handed out twice.
let env = esNameReserve esNameEnvEmpty "b_1" in
let b1 = nameSym "b" in
let b2 = nameSym "b" in
let b3 = nameSym "b" in
match esNameGetMany env [b1, b2, b3] with (_, strs) in
utest strs with ["b", "b_2", "b_3"] using eqSeq eqString in

-- Reserved words are never handed out.
let cls = nameSym "class" in
match esNameGet env cls with (env, s4) in
utest s4 with "class_1" in

-- `undefined` is reserved because it is how unit is represented.
let u = nameSym "undefined" in
match esNameGet env u with (env, s5) in
utest s5 with "undefined_1" in

-- Explicitly reserved identifiers are respected.
let env2 = esNameReserve esNameEnvEmpty "env" in
let e = nameSym "env" in
match esNameGet env2 e with (_, s6) in
utest s6 with "env_1" in

()
