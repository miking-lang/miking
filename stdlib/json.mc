-- Compiant with the specification from
-- https://www.json.org/json-en.html
-- Only divergence from the spec is the distinction between floats and integers

include "either.mc"
include "map.mc"
include "string.mc"

type JsonValue
con JsonObject: Map String JsonValue -> JsonValue
con JsonArray: [JsonValue] -> JsonValue
con JsonString: String -> JsonValue
con JsonFloat: Float -> JsonValue
con JsonInt: Int -> JsonValue
con JsonBool: Bool -> JsonValue
con JsonNull: () -> JsonValue


-- Parsing utilities
recursive
  let _jsonErrorString: Int -> String -> String =
    lam pos. lam msg.
    join ["Error at position ", int2string pos, ": ", msg]

  let _jsonError: Int -> String -> Either (JsonValue, String, Int) String =
    lam pos. lam msg.
    Right (_jsonErrorString pos msg)

  -- Eats whitespaces starting from the provided index
  let _jsonEatWhitespace: String -> Int -> (String, Int) =
    lam s. lam pos.
    match s with [' ' | '\n' | '\r' | '\t'] ++ ws then
      _jsonEatWhitespace ws (addi pos 1)
    else
      (s, pos)

  let _jsonEatInt: [Char] -> String -> Int -> (String, String, Int) =
    lam acc. lam s. lam pos.
    match s with [c] ++ ws then
      if and (geqChar c '0') (leqChar c '9') then
        _jsonEatInt (snoc acc c) ws (addi pos 1)
      else
        (acc, s, pos)
    else
      (acc, s, pos)

  let _jsonParse: String -> Int -> Either (JsonValue, String, Int) String =
    lam s. lam pos.
    match _jsonEatWhitespace s pos with (s, pos) in
    switch s
    case ['{'] ++ ws then
      _jsonParseObject ws (addi pos 1)
    case ['['] ++ ws then
      _jsonParseArray ws (addi pos 1)
    case ['\"'] ++ ws then
      _jsonParseString [] ws (addi pos 1)
    case ['-'] ++ ws then
      _jsonParseNegativeNumber ws (addi pos 1)
    case ['0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9'] ++ _ then
      _jsonParseNumber s pos
    case "true" ++ ws then
      Left (JsonBool true, ws, addi pos 4)
    case "false" ++ ws then
      Left (JsonBool false, ws, addi pos 5)
    case "null" ++ ws then
      Left (JsonNull (), ws, addi pos 4)
    case _ then
      _jsonError pos "Invalid start to a JSON value."
    end

  let _jsonParseObject: String -> Int -> Either (JsonValue, String, Int) String =
    lam s. lam pos.
    match _jsonEatWhitespace s pos with (s, pos) in
    let acc = mapEmpty cmpString in
    match s with ['}'] ++ ws then
      Left (JsonObject acc, ws, addi pos 1)
    else
      _jsonParseObjectContents acc s pos

  let _jsonParseObjectContents: Map String JsonValue -> String -> Int -> Either (JsonValue, String, Int) String =
    lam acc. lam s. lam pos.
    match _jsonEatWhitespace s pos with (s, pos) in
    switch _jsonParse s pos
    case Left (JsonString key, s, pos) then
      match _jsonEatWhitespace s pos with (s, pos) in
      match s with [':'] ++ ws then
        match _jsonEatWhitespace ws (addi pos 1) with (s, pos) in
        switch _jsonParse s pos
        case Left (value, s, pos) then
          let acc = mapInsert key value acc in
          match s with [','] ++ ws then
            _jsonParseObjectContents acc ws (addi pos 1)
          else match s with ['}'] ++ ws then
            Left (JsonObject acc, ws, addi pos 1)
          else
            _jsonError pos "Expected comma or closing bracket for JSON object."
        case Right err then
          Right err
        end
      else
        _jsonError pos "Expected colon after property key."
    case Left _ then
      _jsonError pos "Expected string as property key."
    case Right err then
      Right err
    end

  let _jsonParseArray: String -> Int -> Either (JsonValue, String, Int) String =
    lam s. lam pos.
    match _jsonEatWhitespace s pos with (s, pos) in
    match s with [']'] ++ ws then
      Left (JsonArray [], ws, addi pos 1)
    else
      _jsonParseArrayContents [] s pos

  let _jsonParseArrayContents: [JsonValue] -> String -> Int -> Either (JsonValue, String, Int) String =
    lam acc. lam s. lam pos.
    match _jsonEatWhitespace s pos with (s, pos) in
    let result = _jsonParse s pos in
    switch result
    case Left (value, s, pos) then
      let acc = snoc acc value in
      match _jsonEatWhitespace s pos with (s, pos) in
      match s with [','] ++ ws then
        _jsonParseArrayContents acc ws (addi pos 1)
      else match s with [']'] ++ ws then
        Left (JsonArray acc, ws, addi pos 1)
      else
        _jsonError pos "Expected comma or closing bracket of JSON array."
    case Right err then
      Right err
    end

  let _jsonParseString: [Char] -> String -> Int -> Either (JsonValue, String, Int) String =
    lam acc. lam s. lam pos.
    match s with ['\\', c] ++ ws then
      -- NOTE(johnwikman, 2022-05-13): Might look wierd to match at two
      -- characters at the same time, but since we know that the following
      -- character cannot terminate a string, we will anyways get an error if s
      -- was just the singleton string ['\\']
      switch c
      case '\"' then _jsonParseString (snoc acc ('\"')) ws (addi pos 2)
      case '\\' then _jsonParseString (snoc acc ('\\')) ws (addi pos 2)
      case '/'  then _jsonParseString (snoc acc ('/')) ws (addi pos 2)
      case 'b'  then _jsonParseString (snoc acc (int2char 8)) ws (addi pos 2)
      case 'f'  then _jsonParseString (snoc acc (int2char 12)) ws (addi pos 2)
      case 'n'  then _jsonParseString (snoc acc ('\n')) ws (addi pos 2)
      case 'r'  then _jsonParseString (snoc acc ('\r')) ws (addi pos 2)
      case 't'  then _jsonParseString (snoc acc ('\t')) ws (addi pos 2)
      case 'u' then
        match ws with [h3, h2, h1, h0] ++ ws then
          let hex2int: Char -> Option Int = lam hc.
            if and (geqChar hc '0') (leqChar hc '9') then
              Some (subi (char2int hc) (char2int '0'))
            else if and (geqChar hc 'A') (leqChar hc 'F') then
              Some (addi (subi (char2int hc) (char2int 'A')) 10)
            else if and (geqChar hc 'a') (leqChar hc 'f') then
              Some (addi (subi (char2int hc) (char2int 'a')) 10)
            else
              None ()
          in
          let conv = foldl (lam acc: Option Int. lam hc.
            match acc with Some accv then
              match hex2int hc with Some hv then
                Some (addi (muli accv 16) hv)
              else None ()
            else None ()
          ) (Some 0) [h3, h2, h1, h0] in
          match conv with Some v then
            _jsonParseString (snoc acc (int2char v)) ws (addi pos 6)
          else
            _jsonError (addi pos 2) "Expected 4 hexadecimal characters"
        else
          _jsonError (addi pos 2) "Expected 4 hexadecimal characters"
      case _ then
        _jsonError (addi pos 1) (join [
          "Invalid escape char \'", [c], "\' (decimal value: ",
          int2string (char2int c), ")"
        ])
      end
    else match s with ['\"'] ++ ws then
      Left (JsonString acc, ws, addi pos 1)
    else match s with [c] ++ ws then
      _jsonParseString (snoc acc c) ws (addi pos 1)
    else
      _jsonError pos "Non-terminated string."

  let _jsonParseNegativeNumber: String -> Int -> Either (JsonValue, String, Int) String =
    lam s. lam pos.
    let num = _jsonParseNumber s pos in
    switch num
    case Left (JsonInt i, s, pos) then
      Left (JsonInt (negi i), s, pos)
    case Left (JsonFloat f, s, pos) then
      Left (JsonFloat (negf f), s, pos)
    case Left _ then
      _jsonError pos "Internal error, did not get a number back."
    case Right err then
      Right err
    end

  let _jsonParseNumber: String -> Int -> Either (JsonValue, String, Int) String =
    lam s. lam pos.
    match s with ['0'] ++ ws then
      _jsonParseNumberDecimals "0" ws (addi pos 1)
    else match s with [c & ('1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9')] ++ ws then
      match _jsonEatInt [c] ws (addi pos 1) with (intStr, ws, pos) in
      _jsonParseNumberDecimals intStr ws pos
    else
      _jsonError pos "Expected a number."

  let _jsonParseNumberDecimals: String -> String -> Int -> Either (JsonValue, String, Int) String =
    lam intStr. lam s. lam pos.
    match s with ['.'] ++ ws then
      match _jsonEatInt [] ws (addi pos 1) with (decimals, ws, pos) in
      if null decimals then
        _jsonError pos "Expected decimals after dot in a number."
      else
        _jsonParseNumberExponent intStr decimals ws pos
    else match s with ['e'|'E'] ++ _ then
      _jsonParseNumberExponent intStr "0" s pos
    else
      Left (JsonInt (string2int intStr), s, pos)

  let _jsonParseNumberExponent: String -> String -> String -> Int -> Either (JsonValue, String, Int) String =
    lam intStr. lam decimals. lam s. lam pos.
    match s with ['e'|'E'] ++ ws then
      match ws with [c & ('+'|'-')] ++ ws then
        match _jsonEatInt [] ws (addi pos 2) with (exponent, ws, pos) in
        if null exponent then
          _jsonError pos "Expected exponent digits."
        else
          let floatStr = join [intStr, ".", decimals, "e", [c], exponent] in
          Left (JsonFloat (string2float floatStr), ws, pos)
      else
        match _jsonEatInt [] ws (addi pos 1) with (exponent, ws, pos) in
        if null exponent then
          _jsonError pos "Expected exponent digits."
        else
          let floatStr = join [intStr, ".", decimals, "e", exponent] in
          Left (JsonFloat (string2float floatStr), ws, pos)
    else
      let floatStr = join [intStr, ".", decimals] in
      Left (JsonFloat (string2float floatStr), s, pos)
end

-- Parses a JSON string, returning a `Left JsonValue` if the parsing was
-- successful. Returns a `Right String` with an error message if the formatting
-- was incorrect.
let jsonParse: String -> Either JsonValue String = lam s.
  let result = _jsonParse s 0 in
  switch result
  case Left (value, s, pos) then
    match _jsonEatWhitespace s pos with (s, pos) in
    if null s then
      Left value
    else
      Right (_jsonErrorString pos "Trailing JSON content.")
  case Right err then
    Right err
  end

-- Parse JSON string, but exit on error.
let jsonParseExn: String -> JsonValue = lam s.
  let result = jsonParse s in
  switch result
  case Left value then value
  case Right errmsg then error errmsg
  end

-- Convert JSON value to its minimal string representation
-- TODO(johnwikman, 2022-05-13): A pprint version with indentation and linebreaks
recursive let json2string: JsonValue -> String = lam value.
  switch value
  case JsonObject properties then
    let proplist = mapFoldWithKey (lam acc. lam k. lam v.
      snoc acc (join [json2string (JsonString k), ":", json2string v])
    ) [] properties in
    cons '{' (snoc (strJoin "," proplist) '}')
  case JsonArray values then
    cons '[' (snoc (strJoin "," (map json2string values)) ']')
  case JsonString s then
    let escape: [Char] -> Char -> String = lam acc. lam c.
      let cval: Int = char2int c in
      if eqi cval 8 then
        concat acc "\\b"
      else if eqi cval 12 then
        concat acc "\\f"
      else if or (lti cval 20) (eqi cval 127) then
        let tohex: Int -> Char = lam x.
          if lti x 10 then
            int2char (addi x (char2int '0'))
          else
            int2char (addi (subi x 10) (char2int 'a'))
        in
        concat acc ['\\', 'u', '0', '0', tohex (divi cval 16), tohex (modi cval 16)]
      else
        switch c
        case '\"' then concat acc "\\\""
        case '\\' then concat acc "\\\\"
        case '/' then concat acc "\\/"
        case '\n' then concat acc "\\n"
        case '\r' then concat acc "\\r"
        case '\t' then concat acc "\\t"
        case _ then
          -- NOTE(johnwikman, 2022-05-13): Ignoring the upper bound on JSON
          -- character size here.
          snoc acc c
        end
    in
    (snoc (foldl escape "\"" s) '\"')
  case JsonFloat f then
    -- TODO(johnwikman, 2022-05-13): Verify that this 2string method actually
    -- conforms to JSON. ".01" and "13." are not valid floats in JSON.
    float2string f
  case JsonInt i then
    int2string i
  case JsonBool b then
    if b then "true" else "false"
  case JsonNull () then
    "null"
  end
end

recursive let jsonEq: JsonValue -> JsonValue -> Bool =
  lam lhs. lam rhs.
  switch (lhs, rhs)
  case (JsonObject lv, JsonObject rv) then mapEq jsonEq lv rv
  case (JsonArray lv, JsonArray rv) then eqSeq jsonEq lv rv
  case (JsonString lv, JsonString rv) then eqString lv rv
  case (JsonFloat lv, JsonFloat rv) then eqf lv rv
  case (JsonInt lv, JsonInt rv) then eqi lv rv
  case (JsonBool lv, JsonBool rv) then eqBool lv rv
  case (JsonNull lv, JsonNull rv) then true
  case _ then false
  end
end


mexpr

jsonParseExn "{\"list\":[{},{}]}";

utest jsonParse "123.45" with Left (JsonFloat 123.45) in
utest json2string (JsonFloat 123.45) with "123.45" in

utest jsonParse "-1e-5" with Left (JsonFloat (negf 1e-5)) in
utest json2string (JsonFloat (negf 1e-5)) with "-1e-05" in

utest jsonParse "1233" with Left (JsonInt 1233) in
utest json2string (JsonInt 1233) with "1233" in

utest jsonParse "-1233" with Left (JsonInt (negi 1233)) in
utest json2string (JsonInt (negi 1233)) with "-1233" in

utest jsonParse "\"foo\\u0020bar\"" with Left (JsonString "foo bar") in
utest json2string (JsonString "foo bar") with "\"foo bar\"" in

utest jsonParse "true" with Left (JsonBool true) in
utest json2string (JsonBool true) with "true" in

utest jsonParse "false" with Left (JsonBool false) in
utest json2string (JsonBool false) with "false" in

utest jsonParse "null" with Left (JsonNull ()) in
utest json2string (JsonNull ()) with "null" in

utest jsonParse "{}" with Left (JsonObject (mapEmpty cmpString)) using eitherEq jsonEq eqString in
utest json2string (JsonObject (mapEmpty cmpString)) with "{}" in

utest jsonParse "[]" with Left (JsonArray []) in
utest json2string (JsonArray []) with "[]" in

utest jsonParse "{ \t\n}" with Left (JsonObject (mapEmpty cmpString)) using eitherEq jsonEq eqString in
utest jsonParse "[ \n\t]" with Left (JsonArray []) in


utest jsonParse "{\"list\":[{},{}]}" with Left (JsonObject (mapFromSeq cmpString [("list", JsonArray [JsonObject (mapEmpty cmpString), JsonObject (mapEmpty cmpString)])])) using eitherEq jsonEq eqString in
utest json2string (JsonObject (mapFromSeq cmpString [("list", JsonArray [JsonObject (mapEmpty cmpString), JsonObject (mapEmpty cmpString)])])) with "{\"list\":[{},{}]}" in
utest jsonParse "[{\n}\n,[\n{\t}]\n]" with Left (JsonArray [JsonObject (mapEmpty cmpString), JsonArray [JsonObject (mapEmpty cmpString)]]) using eitherEq jsonEq eqString in
utest json2string (JsonArray [JsonObject (mapEmpty cmpString), JsonArray [JsonObject (mapEmpty cmpString)]]) with "[{},[{}]]" in

utest jsonParse " [5, \"a\\nb\"]\t" with Left (JsonArray [JsonInt 5, JsonString "a\nb"]) in

utest jsonParse "{\"mystr\" : foo}" with Right "Error at position 11: Invalid start to a JSON value." using eitherEq jsonEq eqString in

let myJsonObject =
  JsonObject (mapFromSeq cmpString
             [ ("mylist", JsonArray [JsonObject (mapEmpty cmpString), JsonInt 2, JsonFloat 3e-2])
             , ("mystr", JsonString "foo")
             , ("mybool", JsonBool true)
             , ("mynull", JsonNull ())
             ])
in

utest jsonParse "{\"mylist\" : [{},2,3e-2], \"mystr\" : \n\"foo\", \"mybool\" :\ttrue, \"mynull\":null}"
with Left myJsonObject using eitherEq jsonEq eqString in

utest json2string myJsonObject
with "{\"mystr\":\"foo\",\"mybool\":true,\"mylist\":[{},2,0.03],\"mynull\":null}" in

utest jsonParse (json2string myJsonObject) with Left myJsonObject using eitherEq jsonEq eqString in

()
