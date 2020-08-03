include "parser.mc"

type JsonValue
con JsonObject : [ (String, JsonValue) ] -> JsonValue
con JsonArray  : [ JsonValue ]           -> JsonValue
con JsonString : String                  -> JsonValue
con JsonFloat  : Float                   -> JsonValue
con JsonInt    : Int                     -> JsonValue
con JsonBool   : Bool                    -> JsonValue
con JsonNull   : ()                      -> JsonValue


let with_ws = wrapped_in spaces spaces

let list_or_spaces = lam left. lam right. lam elem.
  (wrapped_in left right
    (apr spaces
         (sep_by (lex_char ',') elem)))


let jsonNumber =
  let maybe = lam p. alt p (pure "") in
  let decimals = label "decimals" (liftA2 cons (lex_char '.') lex_digits) in
  let exponent = label "exponent" (
    liftA2 cons (alt (lex_char 'e') (lex_char 'E'))
           (liftA2 concat (foldr1 alt [lex_string "-", lex_string "+", pure ""])
                          lex_digits))
  in
  let string2JsonFloat = lam x. JsonFloat (string2float x) in
  let string2JsonInt = lam x. JsonInt (string2int x) in
  bind (liftA2 concat (maybe (lex_string "-")) lex_digits) (lam digits.
  alt (fmap (compose string2JsonFloat (concat digits))
            (alt exponent (liftA2 concat decimals (maybe exponent))))
      (pure (string2JsonInt digits)))

let jsonString = fmap (lam x. JsonString x) lex_string_lit

let jsonNull = apr (lex_string "null") (pure (JsonNull ()))

let lexTrue = apr (lex_string "true") (pure true)
let lexFalse = apr (lex_string "false") (pure false)
let jsonBool = fmap (lam x. JsonBool x) (alt lexTrue lexFalse)

recursive
-- These functions are all eta expanded, because recursive lets must begin with a lambda.
let jsonMember = lam x.
  let makeMember = lam k. lam v. (k, v) in
  (liftA2 makeMember (apl (with_ws lex_string_lit) (lex_char ':')) jsonValue) x

let jsonObject = lam x.
  fmap (lam x. JsonObject x)
  (list_or_spaces (lex_char '{') (lex_char '}') jsonMember) x

let jsonArray = lam x.
  fmap (lam x. JsonArray x)
  (list_or_spaces (lex_char '[') (lex_char ']') jsonValue) x

-- jsonValue : Parser JsonValue
--
-- Parse a string containing a JSON value into a JsonValue.
let jsonValue = lam x.
  let jsonValues =
    [ jsonObject
    , jsonArray
    , jsonString
    , jsonNumber
    , jsonBool
    , jsonNull
    ]
  in
  (with_ws (foldr1 alt jsonValues)) x
end

-- parseJson : String -> String -> JsonValue
--
-- Parse a JSON value given a string and the name of the file it came from
let parseJson = lam filename.
  run_parser filename jsonValue

let wrapString = lam left. lam right. lam x.
  cons left (snoc x right)

let formatNull = const "null"
let formatBool = lam b. if b then "true" else "false"
let formatInt = int2string
let formatFloat = float2string
let formatString = wrapString '\"' '\"'

let formatSeq = lam left. lam right. lam show. lam x.
  let contents =
    if null x then
      ""
    else
      let i = init x in
      let l = last x in
      foldr (lam v. lam s. concat (show v) (concat ", " s)) (show l) i
  in wrapString left right contents

recursive
let formatArray = lam x. formatSeq '[' ']' formatValue x
let formatObject = lam x.
  let formatMember = lam t.
    concat (formatString t.0) (concat ": " (formatValue t.1))
  in formatSeq '{' '}' formatMember x

let formatValue : JsonValue -> String = lam x.
  match x with JsonObject o then
    formatObject o
  else match x with JsonArray a then
    formatArray a
  else match x with JsonString s then
    formatString s
  else match x with JsonFloat f then
    formatFloat f
  else match x with JsonInt n then
    formatInt n
  else match x with JsonBool b then
    formatBool b
  else match x with JsonNull n then
    formatNull n
  else
    error "formatValue: Arg is not a JSON value"
end

-- formatJson : JsonValue -> String
--
-- Format an MCore JsonValue to a JSON string representation
let formatJson = formatValue

mexpr

utest test_parser jsonNumber "123.45" with Success (JsonFloat 123.45, ("", ("", 1, 7))) in
utest test_parser jsonNumber "1233" with Success (JsonInt 1233, ("", ("", 1, 5))) in
utest test_parser jsonNumber "-1233" with Success (JsonInt (negi 1233), ("", ("", 1, 6))) in
utest test_parser jsonBool "true" with Success (JsonBool true, ("", ("", 1, 5))) in
utest test_parser jsonBool "false" with Success (JsonBool false, ("", ("", 1, 6))) in
utest test_parser jsonNull "null" with Success (JsonNull (), ("", ("", 1, 5))) in
utest test_parser jsonObject "{ \t}" with Success (JsonObject [], ("", ("", 1, 5))) in
utest test_parser jsonArray "[ \t]" with Success (JsonArray [], ("", ("", 1, 5))) in
utest show_error (test_parser jsonValue "{\"mystr\" : foo}")
with "Parse error at 1:12: Unexpected 'f'. Expected '{' or '[' or '\"' or digit or 'true' or 'false' or 'null'" in
let myJsonObject =
  JsonObject [ ("mylist", JsonArray [JsonInt 1, JsonInt 2, JsonInt 3])
             , ("mystr", JsonString "foo")
             , ("mybool", JsonBool true)
             , ("mynull", JsonNull ())
             ]
in
utest test_parser jsonValue "{\"mylist\" : [1,2,3], \"mystr\" : \"foo\", \"mybool\" :\ttrue, \"mynull\":null}"
with
Success (myJsonObject, ("", ("", 1, 70))) in
utest formatValue myJsonObject
with "{\"mylist\": [1, 2, 3], \"mystr\": \"foo\", \"mybool\": true, \"mynull\": null}" in
utest test_parser jsonValue (formatValue myJsonObject) with Success (myJsonObject, ("", ("", 1, 70))) in
()
