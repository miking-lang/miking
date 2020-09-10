include "parser-combinators.mc"

type JsonValue
con JsonObject : [ (String, JsonValue) ] -> JsonValue
con JsonArray  : [ JsonValue ]           -> JsonValue
con JsonString : String                  -> JsonValue
con JsonFloat  : Float                   -> JsonValue
con JsonInt    : Int                     -> JsonValue
con JsonBool   : Bool                    -> JsonValue
con JsonNull   : ()                      -> JsonValue


let with_ws = wrappedIn spaces spaces

let list_or_spaces = lam left. lam right. lam elem.
  (wrappedIn left right
    (apr spaces
         (sepBy (lexChar ',') elem)))


let jsonNumber =
  let maybe = lam p. alt p (pure "") in
  let decimals = label "decimals" (liftA2 cons (lexChar '.') lexDigits) in
  let exponent = label "exponent" (
    liftA2 cons (alt (lexChar 'e') (lexChar 'E'))
           (liftA2 concat (foldr1 alt [lexString "-", lexString "+", pure ""])
                          lexDigits))
  in
  let string2JsonFloat = lam x. JsonFloat (string2float x) in
  let string2JsonInt = lam x. JsonInt (string2int x) in
  bind (liftA2 concat (maybe (lexString "-")) lexDigits) (lam digits.
  alt (fmap (compose string2JsonFloat (concat digits))
            (alt exponent (liftA2 concat decimals (maybe exponent))))
      (pure (string2JsonInt digits)))

let jsonString = fmap (lam x. JsonString x) lexStringLit

let jsonNull = apr (lexString "null") (pure (JsonNull ()))

let lexTrue = apr (lexString "true") (pure true)
let lexFalse = apr (lexString "false") (pure false)
let jsonBool = fmap (lam x. JsonBool x) (alt lexTrue lexFalse)

recursive
-- These functions are all eta expanded, because recursive lets must begin with a lambda.
let jsonMember = lam x.
  let makeMember = lam k. lam v. (k, v) in
  (liftA2 makeMember (apl (with_ws lexStringLit) (lexChar ':')) jsonValue) x

let jsonObject = lam x.
  fmap (lam x. JsonObject x)
  (list_or_spaces (lexChar '{') (lexChar '}') jsonMember) x

let jsonArray = lam x.
  fmap (lam x. JsonArray x)
  (list_or_spaces (lexChar '[') (lexChar ']') jsonValue) x

-- jsonValue : Parser JsonValue
--
-- Parse a JSON value from a string
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

-- parseJson : String -> Option
--
-- Try to parse a JSON value from a string, returning None if the string is
-- not valid JSON.
let parseJson = lam str.
  match testParser jsonValue str with Success (result, _) then Some result
  else None ()

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

utest parseJson "1.234500e+2" with Some (JsonFloat 123.45) in
utest formatJson (JsonFloat 123.45) with "1.234500e+2" in

utest parseJson "-1e-5" with Some (JsonFloat (negf 1e-5)) in
utest formatJson (JsonFloat (negf 1e-5)) with "-1.0e-5" in

utest parseJson "1233" with Some (JsonInt 1233) in
utest formatJson (JsonInt 1233) with "1233" in

utest parseJson "-1233" with Some (JsonInt (negi 1233)) in
utest formatJson (JsonInt (negi 1233)) with "-1233" in

utest parseJson "true" with Some (JsonBool true) in
utest formatJson (JsonBool true) with "true" in

utest parseJson "false" with Some (JsonBool false) in
utest formatJson (JsonBool false) with "false" in

utest parseJson "null" with Some (JsonNull ()) in
utest formatJson (JsonNull ()) with "null" in

utest parseJson "{}" with Some (JsonObject []) in
utest formatJson (JsonObject []) with "{}" in

utest parseJson "[]" with Some (JsonArray []) in
utest formatJson (JsonArray []) with "[]" in

utest parseJson "{ \t\n}" with Some (JsonObject []) in
utest parseJson "[ \n\t]" with Some (JsonArray []) in

utest parseJson "{\"list\":[{},{}]}" with Some (JsonObject [("list", JsonArray [JsonObject [], JsonObject []])]) in
utest formatJson (JsonObject [("list", JsonArray [JsonObject [], JsonObject []])]) with "{\"list\": [{}, {}]}" in
utest parseJson "[{\n}\n,[\n{\t}]\n]" with Some (JsonArray [JsonObject [], JsonArray [JsonObject []]]) in
utest formatJson (JsonArray [JsonObject [], JsonArray [JsonObject []]]) with "[{}, [{}]]" in

utest showError (testParser jsonValue "{\"mystr\" : foo}")
with "Parse error at 1:12: Unexpected 'f'. Expected '{' or '[' or '\"' or digit or 'true' or 'false' or 'null'" in
let myJsonObject =
  JsonObject [ ("mylist", JsonArray [JsonObject [], JsonInt 2, JsonFloat 3e-2])
             , ("mystr", JsonString "foo")
             , ("mybool", JsonBool true)
             , ("mynull", JsonNull ())
             ]
in
utest testParser jsonValue "{\"mylist\" : [{},2,3e-2], \"mystr\" : \n\"foo\", \"mybool\" :\ttrue, \"mynull\":null}abc"
with Success (myJsonObject, ("abc", {file ="", row = 2, col = 39})) in
utest formatValue myJsonObject
with "{\"mylist\": [{}, 2, 3.0e-2], \"mystr\": \"foo\", \"mybool\": true, \"mynull\": null}" in
utest parseJson (formatValue myJsonObject) with Some myJsonObject in
()
