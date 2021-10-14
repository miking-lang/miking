
include "map.mc"

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
  mapFromSeq (tomlBindings table)

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

-- 'tomlValueToIntSeqExn v' converts a toml value to an integer sequence.
external externalTomlValueToIntSeqExn ! : TomlValue -> [Int]
let tomlValueToIntSeqExn = lam v. externalTomlValueToIntSeqExn v

utest tomlValueToIntSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[1,2,3]")) with [1,2,3]

-- 'tomlValueToStringSeqExn v' converts a toml value to a string sequence.
external externalTomlValueToStringSeqExn ! : TomlValue -> [String]
let tomlValueToStringSeqExn = lam v. externalTomlValueToStringSeqExn v

utest tomlValueToStringSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[\"foo\", \"bar\"]")) with ["foo", "bar"]

-- 'tomlValueToFloatSeqExn v' converts a toml value to a float sequence.
external externalTomlValueToFloatSeqExn ! : TomlValue -> [Float]
let tomlValueToFloatSeqExn = lam v. externalTomlValueToFloatSeqExn v

utest tomlValueToFloatSeqExn (tomlFindExn "key" (tomlFromStringExn "key=[3.14,1e1]")) with [3.14,1e1]

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





