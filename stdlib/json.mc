include "parser.mc"

type JsonValue
con JsonObject : [ { key: String, val: JsonValue } ] -> JsonValue
con JsonArray  : [ JsonValue ]                       -> JsonValue
con JsonString : String                              -> JsonValue
con JsonFloat  : Float                               -> JsonValue
con JsonInt    : Int                                 -> JsonValue
con JsonBool   : Bool                                -> JsonValue
con JsonNull   : ()                                  -> JsonValue


let with_ws = wrapped_in spaces spaces
let list_or_spaces = lam left. lam right. lam elem.
  (wrapped_in left right
    (alt (try (sep_by (lex_char ',') elem))
         (apr spaces (pure []))))

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
  let makeMember = lam k. lam v. { key = k, val = v } in
  (liftA2 makeMember (apl (with_ws lex_string_lit) (lex_char ':')) jsonValue) x

let jsonObject = lam x.
  fmap (lam x. JsonObject x)
  (list_or_spaces (lex_char '{') (lex_char '}') jsonMember) x

let jsonArray = lam x.
  fmap (lam x. JsonArray x)
  (list_or_spaces (lex_char '[') (lex_char ']') jsonValue) x

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

let parseJson : String -> String -> JsonValue = lam filename.
  run_parser filename jsonValue

mexpr

utest test_parser jsonNumber "123.45" with Success (JsonFloat 123.45, ("", ("", 1, 7))) in
utest test_parser jsonNumber "1233" with Success (JsonInt 1233, ("", ("", 1, 5))) in
utest test_parser jsonBool "true" with Success (JsonBool true, ("", ("", 1, 5))) in
utest test_parser jsonBool "false" with Success (JsonBool false, ("", ("", 1, 6))) in
utest test_parser jsonNull "null" with Success (JsonNull (), ("", ("", 1, 5))) in
utest test_parser jsonObject "{ \t}" with Success (JsonObject [], ("", ("", 1, 5))) in
utest test_parser jsonArray "[ \t]" with Success (JsonArray [], ("", ("", 1, 5))) in
utest show_error (test_parser jsonValue "{\"mystr\" : foo}")
with "Parse error at 1:12: Unexpected 'f'. Expected '{' or '[' or '\"' or digit or 'true' or 'false' or 'null'" in
utest test_parser jsonValue "{\"mylist\" : [1,2,3], \"mystr\" : \"foo\", \"mybool\" :\ttrue, \"mynull\":null}"
with
Success (JsonObject [ {key = "mylist", val = JsonArray [JsonInt 1, JsonInt 2, JsonInt 3]}
                    , {key = "mystr", val = JsonString "foo"}
                    , {key = "mybool", val = JsonBool true}
                    , {key = "mynull", val = JsonNull ()}
                    ], ("", ("", 1, 70))) in
()
