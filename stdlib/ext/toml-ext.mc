
type TomlTable
type TomlValue

external externalTomlFromString ! : String -> TomlTable
let tomlFromString = lam str. externalTomlFromString str

utest tomlFromString "key=1"; () with ()

external externalTomlFindExn ! : String -> TomlTable -> TomlValue
let tomlFindExn = lam str. lam table. externalTomlFindExn str table

utest tomlFindExn "key" (tomlFromString "key=1"); () with ()

external externalTomlBindings ! : TomlTable -> [(String, TomlValue)]
let tomlBindings = lam table. externalTomlBindings table

utest
  let binds = tomlBindings (tomlFromString "intval=1\nstringval=\"abc\"") in
  let keys = map (lam b : (String, TomlValue). b.0) binds in
  keys
with ["intval", "stringval"]

-- Parsing toml values
external externalTomlValueToInt ! : TomlValue -> Int
let tomlValueToInt = lam v. externalTomlValueToInt v

utest tomlValueToInt (tomlFindExn "key" (tomlFromString "key=1")) with 1
