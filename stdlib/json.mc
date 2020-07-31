include "parser.mc"

type JsonValue
con JsonObject : [ { key: String, val: JsonValue } ] -> JsonValue
con JsonArray  : [ JsonValue ]                       -> JsonValue
con JsonString : String                              -> JsonValue
con JsonFloat  : Float                               -> JsonValue
con JsonInt    : Int                                 -> JsonValue
con JsonBool   : Bool                                -> JsonValue
con JsonNull   : ()                                  -> JsonValue

let lexJsonInt = fmap (lam x. JsonInt x) lex_number
let lexJsonFloat = fmap (lam x. JsonFloat x) lex_float

let with_ws = wrapped_in spaces spaces
let list_or_spaces = lam left. lam right. lam elem.
  (wrapped_in left right
    (alt (try (sep_by (lex_char ',') elem))
         (apr spaces (pure []))))


let lexJsonString = fmap (lam x. JsonString x) lex_string_lit

let lexJsonNumber = alt (try lexJsonFloat) lexJsonInt

let lexJsonNull = apr (lex_string "null") (pure (JsonNull ()))
let lexTrue = apr (lex_string "true") (pure true)
let lexFalse = apr (lex_string "false") (pure false)

let lexJsonBool = fmap (lam x. JsonBool x) (alt lexTrue lexFalse)

recursive
-- These functions are all eta expanded, because recursive lets must begin with a lambda.
let lexJsonMember = lam x.
  let makeMember = lam k. lam v. { key = k, val = v } in
  (liftA2 makeMember (apl (with_ws lex_string_lit) (lex_char ':')) lexJsonValue) x

let lexJsonObject = lam x.
  fmap (lam x. JsonObject x)
  (list_or_spaces (lex_char '{') (lex_char '}') lexJsonMember) x

let lexJsonArray = lam x.
  fmap (lam x. JsonArray x)
  (list_or_spaces (lex_char '[') (lex_char ']') lexJsonValue) x

let lexJsonValue = lam x.
  let jsonValues =
    [ lexJsonObject
    , lexJsonArray
    , lexJsonString
    , lexJsonNumber
    , lexJsonBool
    , lexJsonNull
    ]
  in
  (with_ws (foldr1 alt jsonValues)) x
end

let parseJson : String -> String -> JsonValue = lam filename.
  run_parser filename lexJsonValue

mexpr

utest test_parser lexJsonInt "12345" with Success (JsonInt 12345, ("", ("", 1, 6))) in
utest test_parser lexJsonFloat "123.45" with Success (JsonFloat 123.45, ("", ("", 1, 7))) in
utest test_parser lexJsonNumber "123.45" with Success (JsonFloat 123.45, ("", ("", 1, 7))) in
utest test_parser lexJsonNumber "1233" with Success (JsonInt 1233, ("", ("", 1, 5))) in
utest test_parser lexJsonBool "true" with Success (JsonBool true, ("", ("", 1, 5))) in
utest test_parser lexJsonBool "false" with Success (JsonBool false, ("", ("", 1, 6))) in
utest test_parser lexJsonNull "null" with Success (JsonNull (), ("", ("", 1, 5))) in
utest test_parser lexJsonObject "{ \t}" with Success (JsonObject [], ("", ("", 1, 5))) in
utest test_parser lexJsonArray "[ \t]" with Success (JsonArray [], ("", ("", 1, 5))) in
utest test_parser lexJsonValue "{\"mystr\" : foo}" with Failure ("'\"'", "'}'", ("\"mystr\" : foo}", ("", 1, 2))) in
utest test_parser lexJsonValue "{\"mylist\" : [1,2,3], \"mystr\" : \"foo\", \"mybool\" :\ttrue, \"mynull\":null}"
with
Success (JsonObject [ {key = "mylist", val = JsonArray [JsonInt 1, JsonInt 2, JsonInt 3]}
                    , {key = "mystr", val = JsonString "foo"}
                    , {key = "mybool", val = JsonBool true}
                    , {key = "mynull", val = JsonNull ()}
                    ], ("", ("", 1, 70))) in
()
