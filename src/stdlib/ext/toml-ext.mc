
include "map.mc"

/-
  Implements functionality for reading and writing TOML data.

  A TOML table is a sequence of (key, value) pairs, where each key is a string,
  and each value is one of:
  - integer
  - float
  - bool
  - string
  - TOML table
  - a sequence of values

  Date data types are currently not supported.
-/

type TomlTable
type TomlValue

------------------
-- READING TOML --
------------------

-- 'tomlFromString str' parses 'str' into a toml table.
external externalTomlFromStringExn ! : String -> TomlTable
let tomlFromStringExn = lam str. externalTomlFromStringExn str

utest tomlFromStringExn "key=1"; () with ()

-- 'tomlFindExn key table' returns the value bound to 'key' in 'table'.
external externalTomlFindExn ! : String -> TomlTable -> TomlValue
let tomlFindExn = lam str. lam table. externalTomlFindExn str table

utest tomlFindExn "key" (tomlFromStringExn "key=1"); () with ()

-- 'tomlBindings table' returns the bindings of 'table'.
external externalTomlBindings ! : TomlTable -> [(String, TomlValue)]
let tomlBindings = lam table. externalTomlBindings table

utest
  let binds = tomlBindings (tomlFromStringExn "intval=1\nstringval=\"abc\"") in
  let keys = map (lam b : (String, TomlValue). b.0) binds in
  keys
with ["intval", "stringval"]

-- 'tomlBindings table' converts 'table' into a map.
let tomlTableToMap : TomlTable -> Map String TomlValue = lam table.
  mapFromSeq cmpString (tomlBindings table)

-- 'tomlValueToString v' converts a toml value to a string, regardless of the
-- type of the value.
external externalTomlValueToString ! : TomlValue -> String
let tomlValueToString = lam v. externalTomlValueToString v

utest
  let t = tomlFromStringExn
  "
  key1=1
  key2=3.14
  key3=[3.14,4.1]
  key4=\"value\"
  key5=[[]]
  "
  in
  map (lam b : (String, TomlValue). tomlValueToString b.1) (tomlBindings t)
with ["1", "3.14", "[3.14, 4.1]", "\"value\"","[[]]"]

-- 'tomlValueToIntExn v' converts a toml value to an integer.
external externalTomlValueToIntExn ! : TomlValue -> Int
let tomlValueToIntExn = lam v. externalTomlValueToIntExn v

utest tomlValueToIntExn (tomlFindExn "key" (tomlFromStringExn "key=1")) with 1

-- 'tomlValueToStringExn v' converts a toml value to a string.
external externalTomlValueToStringExn ! : TomlValue -> String
let tomlValueToStringExn = lam v. externalTomlValueToStringExn v

utest tomlValueToStringExn (tomlFindExn "key" (tomlFromStringExn "key=\"value\"")) with "value"

-- 'tomlValueToFloatExn v' converts a toml value to a float.
external externalTomlValueToFloatExn ! : TomlValue -> Float
let tomlValueToFloatExn = lam v. externalTomlValueToFloatExn v

utest tomlValueToFloatExn (tomlFindExn "key" (tomlFromStringExn "key=3.14")) with 3.14

-- 'tomlValueToBoolExn v' converts a toml value to a bool.
external externalTomlValueToBoolExn ! : TomlValue -> Bool
let tomlValueToBoolExn = lam v. externalTomlValueToBoolExn v

utest tomlValueToBoolExn (tomlFindExn "key" (tomlFromStringExn "key=true")) with true

-- 'tomlValueToTableExn v' converts a toml value to a toml table.
external externalTomlValueToTableExn ! : TomlValue -> TomlTable
let tomlValueToTableExn = lam v. externalTomlValueToTableExn v

utest
  let t1 = tomlFromStringExn
  "
  [key]
  subkey=1
  "
  in
  let t2 = tomlValueToTableExn (tomlFindExn "key" t1) in
  tomlValueToIntExn (tomlFindExn "subkey" t2)
with 1

-- 'tomlValueToIntSeqExn v' converts a toml value to an integer sequence.
external externalTomlValueToIntSeqExn ! : TomlValue -> [Int]
let tomlValueToIntSeqExn = lam v. externalTomlValueToIntSeqExn v

utest tomlValueToIntSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[1,2,3]")) with [1,2,3]
utest tomlValueToIntSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[]")) with []

-- 'tomlValueToStringSeqExn v' converts a toml value to a string sequence.
external externalTomlValueToStringSeqExn ! : TomlValue -> [String]
let tomlValueToStringSeqExn = lam v. externalTomlValueToStringSeqExn v

utest tomlValueToStringSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[\"foo\", \"bar\"]")) with ["foo", "bar"]
utest tomlValueToStringSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[]")) with []

-- 'tomlValueToFloatSeqExn v' converts a toml value to a float sequence.
external externalTomlValueToFloatSeqExn ! : TomlValue -> [Float]
let tomlValueToFloatSeqExn = lam v. externalTomlValueToFloatSeqExn v

utest tomlValueToFloatSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[3.14,1e1]")) with [3.14,1e1]
utest tomlValueToFloatSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[]")) with []

-- 'tomlValueToTableSeqExn v' converts a toml value to a sequence of toml
-- tables.
external externalTomlValueToTableSeqExn ! : TomlValue -> [TomlTable]
let tomlValueToTableSeqExn = lam v. externalTomlValueToTableSeqExn v

utest
  let t1 = tomlFromStringExn
  "
  [[fruit]]
  name = \"apple\"

  [[fruit]]
  name = \"orange\"
  "
  in
  let t2 : [TomlTable] = tomlValueToTableSeqExn (tomlFindExn "fruit" t1) in
  let vals = map (lam t. tomlFindExn "name" t) t2 in
  map tomlValueToStringExn vals
with ["apple", "orange"]

utest
  let t = tomlFromStringExn "[[fruit]]" in
  tomlValueToTableSeqExn (tomlFindExn "fruit" t)
with []

-- 'tomlValueToSeqSeqExn v' converts a toml value to a sequence of sequence of
-- toml values.
external externalTomlValueToSeqSeqExn ! : TomlValue -> [TomlValue]
let tomlValueToSeqSeqExn = lam v. externalTomlValueToSeqSeqExn v

utest
  let t1 = tomlFromStringExn
  "
  seq_of_seq = [[1,2],[3]]
  "
  in
  let t2 : [TomlValue] = tomlValueToSeqSeqExn (tomlFindExn "seq_of_seq" t1) in
  map tomlValueToIntSeqExn t2
with [[1,2],[3]]

------------------
-- WRITING TOML --
------------------

let _strEqNoWhitespace = lam s1. lam s2.
  let s1 = filter (lam c. not (isWhitespace c)) s1 in
  let s2 = filter (lam c. not (isWhitespace c)) s2 in
  eqString s1 s2

-- 'tomlToString table' converts 'table' into a string.
external externalTomlToString ! : TomlTable -> String
let tomlToString = lam table. externalTomlToString table

utest tomlToString (tomlFromStringExn "key=1") with "key=1" using _strEqNoWhitespace

-- 'tomlFromBindings binds' converts 'binds' to a table.
external externalTomlFromBindings ! : [(String, TomlValue)] -> TomlTable
let tomlFromBindings = lam binds. externalTomlFromBindings binds

-- 'tomlIntToValue v' converts an integer to a toml value.
external externalTomlIntToValue ! : Int -> TomlValue
let tomlIntToValue = lam v. externalTomlIntToValue v

utest tomlToString (tomlFromBindings [("key", tomlIntToValue 1)]) with "key=1" using _strEqNoWhitespace

-- 'tomlStringToValue v' converts a string to a toml value.
external externalTomlStringToValue ! : String -> TomlValue
let tomlStringToValue = lam s. externalTomlStringToValue s

utest tomlToString (tomlFromBindings [("key", tomlStringToValue "42")]) with "key=\"42\"" using _strEqNoWhitespace

-- 'tomlFloatToValue v' converts a float to a toml value.
external externalTomlFloatToValue ! : Float -> TomlValue
let tomlFloatToValue = lam v. externalTomlFloatToValue v

utest tomlToString (tomlFromBindings [("key", tomlFloatToValue 3.14)]) with "key=3.14" using _strEqNoWhitespace

-- 'tomlTableToValue v' converts a toml table to a toml value.
external externalTomlTableToValue ! : TomlTable -> TomlValue
let tomlTableToValue = lam v. externalTomlTableToValue v

utest
  let t1 = tomlFromBindings [("subkey", tomlIntToValue 1)] in
  let t2 = tomlFromBindings [("key", tomlTableToValue t1)] in
  tomlToString t2
with
"
[key]
subkey=1
"
using _strEqNoWhitespace

-- 'tomlIntSeqToValue v' converts an integer to a toml value.
external externalTomlIntSeqToValue ! : [Int] -> TomlValue
let tomlIntSeqToValue = lam v. externalTomlIntSeqToValue v

utest tomlToString (tomlFromBindings [("key", tomlIntSeqToValue [1,2,3])]) with "key=[1,2,3]" using _strEqNoWhitespace
utest tomlToString (tomlFromBindings [("key", tomlIntSeqToValue [])]) with "key=[]" using _strEqNoWhitespace

-- 'tomlStringSeqToValue v' converts a string to a toml value.
external externalTomlStringSeqToValue ! : [String] -> TomlValue
let tomlStringSeqToValue = lam s. externalTomlStringSeqToValue s

utest tomlToString (tomlFromBindings [("key", tomlStringSeqToValue ["42","43"])]) with "key=[\"42\", \"43\"]" using _strEqNoWhitespace

-- 'tomlFloatSeqToValue v' converts a float to a toml value.
external externalTomlFloatSeqToValue ! : [Float] -> TomlValue
let tomlFloatSeqToValue = lam v. externalTomlFloatSeqToValue v

utest tomlToString (tomlFromBindings [("key", tomlFloatSeqToValue [3.14])]) with "key=[3.14]" using _strEqNoWhitespace

-- 'tomlTableSeqToValue v' converts a sequence of toml tables to a toml value.
external externalTomlTableSeqToValue ! : [TomlTable] -> TomlValue
let tomlTableSeqToValue = lam v. externalTomlTableSeqToValue v

utest
 let t1 = tomlFromBindings [("name", tomlStringToValue "apple")] in
 let t2 = tomlFromBindings [("name", tomlStringToValue "orange")] in
 let t3 = tomlFromBindings [("fruit", tomlTableSeqToValue [t1, t2])] in
 tomlToString t3
with
"
[[fruit]]
name = \"apple\"

[[fruit]]
name = \"orange\"
"
using _strEqNoWhitespace

-- 'tomlSeqSeqToValue v' converts a sequence of toml values to a toml value
external externalTomlSeqSeqToValue ! : [TomlValue] -> TomlValue
let tomlSeqSeqToValue = lam v. externalTomlSeqSeqToValue v

utest
  let t = tomlFromBindings
    [("key", tomlSeqSeqToValue [tomlIntSeqToValue [1,2], tomlIntSeqToValue [3]])] in
  tomlToString t
with "key=[[1,2],[3]]" using _strEqNoWhitespace
