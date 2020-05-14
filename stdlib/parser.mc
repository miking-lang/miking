include "string.mc"
include "prelude.mc" -- TODO: Should not be needed

-- Debug stuff
let debug_flag = false
let debug = lam s. if debug_flag then printLn s else ()

-- The Parser monad -----------------------------

type Pos = (String, Int, Int)

let eqpos = lam pos1 : Pos. lam pos2 : Pos.
  and (eqstr pos1.0 pos2.0)
  (and (eqi pos1.1 pos2.1) (eqi pos1.2 pos2.2))

let init_pos = lam f. (f, 1, 1)

let bump_col = lam pos. (pos.0, pos.1, addi 1 pos.2)
let bump_row = lam pos. (pos.0, addi 1 pos.1, 1)

let show_pos = lam pos.
  let file = if null pos.0
             then ""
             else concat (concat "FILE \"" pos.0) "\" "
  in
  let row_col = concat (concat (int2string pos.1) ":") (int2string pos.2) in
  concat file row_col

type State = (String, Pos)
-- The parser state is the remaining input and the current position

type ParseResult
con Success : (Dyn, State) -> ParseResult
con Failure : (String, String, State) -> ParseResult
-- Success stores result of parsing
-- Failure stores found and expected token

type Parser = State -> String -> ParseResult

type Filename = String

-- run_parser : Filename -> Parser a -> String -> ParseResult a
--
-- Run a parser with a specified filename and input.
let run_parser = lam f : Filename. lam p : Parser. lam input : String.
    p (input, (init_pos f))

-- test_parser : Parser a -> String -> ParseResult
--
-- Run a parser without a current file.
let test_parser = run_parser ""

-- fail : String -> String -> Parser a
--
-- Fail parsing with custom info
let fail = lam found. lam expected. lam st.
  Failure (found, expected, st)

-- show_error : ParseResult a -> String
--
-- Show human readable error message from failed parse.
-- Fails if argument is not a failure.
let show_error = lam f : ParseResult.
  match f with Failure t then
    let found = t.0 in
    let expected = t.1 in
    let pos = (t.2).1 in
    concat (concat (concat "Parse error at " (show_pos pos)) ": ")
    (concat (concat "Unexpected " found)
            (if gti (length expected) 0
             then concat ". Expected " expected
             else ""))
  else error "Tried to show something that is not a failure"

-- Parser is a functor

-- fmap : (a -> b) -> Parser a -> Parser b
let fmap = lam f. lam p. lam st.
  let res = p st in
  match res with Success t then
    let v = t.0 in
    let rest = t.1 in
    Success (f v, rest)
  else res

-- Parser is an applicative functor

-- pure : a -> Parser a
let pure = lam v. lam st. Success(v, st)

-- ap : Parser (a -> b) -> Parser a -> Parser b
let ap = lam pf. lam p. lam st.
  let res1 = pf st in
  match res1 with Success t1 then
    let f = t1.0 in
    let rest1 = t1.1 in
    let res2 = p rest1 in
    match res2 with Success t2 then
      let x = t2.0 in
      let rest2 = t2.1 in
      pure (f x) rest2
    else res2
  else res1

-- liftA2 : (a -> b -> c) -> Parser a -> Parser b -> Parser c
let liftA2 = lam f. lam px. lam py.
  ap (fmap f px) py

-- apl : Parser a -> Parser b -> Parser a
--
-- Run two parsers, use result of first one
let apl = lam p1. lam p2.
  liftA2 const p1 p2

-- apr : Parser a -> Parser b -> Parser b
--
-- Run two parsers, use result of second one
let apr = lam p1. lam p2.
  ap (fmap (const identity) p1) p2

-- Parser is a monad

-- bind : Parser a -> (a -> Parser b) -> Parser b
--
-- Typical usage is `bind p1 (lam x. p2)`, i.e. run `p1` and
-- pass result to a function running another parser.
let bind = lam p. lam f. lam st.
  let res = p st in
  match res with Success t then
    let x = t.0 in
    let rest = t.1 in
    f x rest
  else -- propagate Failure
    res

-- Control combinators

-- Run parser and ignore result
let void = apl (pure ())

-- when : bool -> Parser a -> Parser ()
--
-- Monadic conditional. `when b p` runs `p` (ignoring the
-- result) if `b` is true.
let when = lam b. lam p. lam st.
  if b then void p else pure ()

-- Core ------------------------------------------------

-- end_of_input : Parser ()
--
-- Fail parsing, unless the input stream is empty
let end_of_input = lam st.
  let input = st.0 in
  if null input
  then pure () st
  else fail (show_char (head input)) "end of input" st

-- next : Parser char
--
-- Read next character from input stream
-- TODO: It would most likely be faster to index into
--       an array than to take the tail of a string
let next = lam st.
  let input = st.0 in
  let pos = st.1 in
  if null input
  then fail "end of input" "" st
  else
    let c = head input in
    let pos2 = if eqstr [c] "\n" then bump_row pos else bump_col pos in
    pure c (tail input, pos2)

-- alt : Parser a -> Parser a -> Parser a
--
-- `alt p1 p2` tries to parse `p1`, but falls back
-- to `p2` if `p1` fails without consuming any input.
let alt = lam p1. lam p2. lam st.
  let res1 = p1 st in
  match res1 with Failure t1 then
    let st2 = t1.2 in
    if eqpos st.1 st2.1 then
      let res2 = p2 st in
      match res2 with Failure t2 then
        let st3 = t2.2 in
        if eqpos st2.1 st3.1 then
          let exp = concat (concat t1.1 " or ") t2.1 in
          Failure (t2.0, exp, st3)
        else res2 -- p2 consumed input, don't merge expected
      else res2 -- Propagate Success
    else res1 -- p1 consumed input, don't backtrack
  else res1 -- Propagate Success

-- not_followed_by : Parser a -> Parser ()
--
-- `not_followed_by p` succeeds (without consuming input)
-- only if `p` does not succeed.
let not_followed_by = lam p. lam st.
  let res1 = p st in
  match res1 with Failure _ then
    pure () st
  else
    let res2 = next st in
    match res2 with Success t then
      let c = t.0 in
      fail (show_char c) "" st
    else res2

-- satisfy : (Char -> Bool) -> String -> Parser Char
--
-- `satisfy cnd exp` succeeds with the next character
-- if `cnd` returns true for that character. `exp` is
-- the expected token.
let satisfy = lam cnd. lam expected. lam st.
  bind next (lam c.
  if cnd c
  then pure c
  else lam _. fail (show_char c) expected st) st

-- try : Parser a -> Parser a
--
-- `try p` is used for backtracking. It parses `p`, but
-- fails without consuming input if `p` fails.
let try = lam p. lam st.
  let res = p st in
  match res with Failure t then
    Failure (t.0, t.1, st)
  else -- Propagate Success
    res

-- label : String -> Parser p -> Parser p
--
-- `label l p` parses `p` but changes the "expected" token
-- to `l` if `p` fails. Typical use is for big chains of
-- `alt`, e.g., `label "expression" (alt (alt let_ lam_) ...)`
let label = lam l. lam p. lam st.
  let res = p st in
  match res with Failure t then
  if eqpos (t.2).1 st.1
  then Failure (t.0, l, t.2)
  else res
  else -- Propagate success
    res

-- Combinators ---------------------------------

-- many : Parser a -> Parser [a]
--
-- Parse zero or more occurrences of a parser.
recursive
  let many = lam p.
    bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
    if null hd
    then pure []
    else bind (many p) (lam tl. pure (concat hd tl)))
end

-- many1 : Parser a -> Parser [a]
--
-- Parse one or more occurrences of a parser.
let many1 = lam p.
  bind p (lam hd.
  bind (many p) (lam tl.
  pure (cons hd tl)))

-- optional : Parser a -> Parser (Option a)
let optional = lam p.
  alt (fmap (lam x. Some x) p) (pure (None()))

-- wrapped_in : Parser l -> Parser r -> Parser a -> Parser a
--
-- `wrapped_in pl pr p` parses `p` preceded by `pl` and
-- succeeded by `pr`.
let wrapped_in = lam pl. lam pr. lam p.
  apr pl (apl p pr)

-- sep_by : Parser s -> Parser a -> Parser [a]
--
-- `sep_by sep p` parses zero or more occurrences of
-- `p` separated by single occurrences of `sep`.
let sep_by = lam sep. lam p.
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  bind (many (apr sep p)) (lam tl.
  pure (concat hd tl)))

-- Lexers ---------------------------------------------

-- Lexers are parsers that do not consume trailing whitespace

-- lex_char : Char -> Parser Char
--
-- Parse a specific character.
let lex_char = lam c. satisfy (eqchar c) (show_char c)

-- lex_number : Parser Int
--
-- Parse a natural number.
let lex_number = fmap string2int (many1 (satisfy is_digit "digit"))

-- lex_string : String -> Parser String
--
-- Parse a specific string.
recursive
  let lex_string = lam s.
    if null s
    then pure ""
    else
      let c = head s in
      let cs = tail s in
      label (concat "'" (concat s "'")) (
        try ( -- This 'try' makes the parser consume the whole string or nothing
          bind (lex_char c) (lam _.
          bind (lex_string cs) (lam _.
          pure (cons c cs)))
        ))
end


-- Parser Char
--
-- Parse a character literal.
-- TODO: Support escaped characters (also in OCaml parser)
let lex_char_lit = wrapped_in (lex_char ''') (lex_char ''') next

-- Parser String
--
-- Parse a string literal.
let lex_string_lit =
  -- TODO: Are other escaped characters handled correctly?
  let escaped =
    try (alt (apr (lex_string "\\\\") (pure (head "\\")))
             (apr (lex_string "\\") (fmap head (lex_string "\""))))
  in
  wrapped_in (lex_string "\"") (lex_string "\"")
             (many (alt escaped (satisfy (lam c. not (eqstr [c] "\"")) "")))

-- lex_float : Parser Float
--
-- Parse a floating point number
let lex_float =
  let decimals =
    label "decimals" (
    bind (apr (lex_char '.') (fmap int2string lex_number)) (lam d.
    pure (concat "." d)))
  in
  let fractional =
    bind (fmap int2string lex_number) (lam n.
    bind (alt decimals (pure "")) (lam d.
    pure (concat n d)))
  in
  let exp =
    label "exponent" (
    apr (lex_char 'e') (
    bind (alt (alt (lex_string "-") (lex_string "+")) (pure "")) (lam sign.
    bind fractional (lam p.
    pure (concat (concat "e" sign) p)))))
  in
  bind (fmap int2string lex_number) (lam n.
  bind (alt exp
       (bind decimals (lam d.
        bind (alt exp (pure "")) (lam e.
        pure (concat d e)))))
  (lam f. pure (string2float (concat n f))))

-- spaces : Parser ()
--
-- Parse zero or more whitespace characters.
let spaces = void (many (satisfy is_whitespace "whitespace"))

-- spaces1 : Parser ()
--
-- Parse one or more whitespace characters.
let spaces1 = void (many1 (satisfy is_whitespace "whitespace"))

-- lex_token : Parser () -> Parser a -> Parser a
--
-- `lex_token ws p` parses `p`, using `ws` to consume any trailing
-- whitespace or comments.
let lex_token = lam ws. lam p. apl p ws

mexpr

-- Position tests
utest show_pos (init_pos "foo.mc") with "FILE \"foo.mc\" 1:1" in
utest show_pos (init_pos "") with "1:1" in

-- Core tests
utest test_parser end_of_input "" with Success((), ("", init_pos "")) in

utest test_parser next "abc" with Success ('a', ("bc", ("", 1, 2))) in
utest test_parser next "\"" with Success (head "\"", ("", ("", 1, 2))) in
utest show_error (test_parser next "")
with "Parse error at 1:1: Unexpected end of input" in

utest
  test_parser (
    bind next (lam c1.
    bind next (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", ("", 1, 3))) in

utest
  show_error (test_parser (
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2]))
  ) "a")
with "Parse error at 1:2: Unexpected end of input" in

-- Lexer tests

utest test_parser (lex_char 'a') "ab" with Success ('a', ("b", ("", 1, 2))) in
utest show_error (test_parser (lex_char 'b') "ab")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'" in

utest test_parser (
    bind (lex_char 'a') (lam c1.
    bind (lex_char 'b') (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", ("", 1, 3))) in

utest show_error (
  test_parser (
    bind (lex_char 'b') (lam c1.
    bind (lex_char 'b') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'" in

utest show_error (
  test_parser (
    bind (lex_char 'a') (lam c1.
    bind (lex_char 'a') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:2: Unexpected 'b'. Expected 'a'" in

utest test_parser (alt (lex_char 'a') (lex_char 'b')) "abc"
with Success('a', ("bc", ("", 1, 2))) in
utest test_parser (alt (lex_char 'b') (lex_char 'a')) "abc"
with Success('a', ("bc", ("", 1, 2))) in
utest show_error (
  test_parser (
    alt (lex_char 'b') (lex_char 'c')
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b' or 'c'" in

utest test_parser (not_followed_by (lex_char 'b')) "abc"
with Success((), ("abc", ("", 1, 1))) in
utest show_error (test_parser (not_followed_by (lex_char 'a')) "abc")
with "Parse error at 1:1: Unexpected 'a'" in

utest test_parser (many (lex_char 'a')) "abc"
with Success("a", ("bc", ("", 1,2))) in
utest test_parser (many (lex_char 'a')) "aaabc"
with Success("aaa", ("bc", ("", 1,4))) in
utest test_parser (many (lex_char 'a')) "bc"
with Success("", ("bc", ("", 1,1))) in

utest test_parser (many1 (lex_char 'a')) "abc"
with Success("a", ("bc", ("", 1, 2))) in
utest test_parser (many1 (lex_char 'a')) "aaabc"
with Success("aaa", ("bc", ("", 1, 4))) in
utest show_error (
  test_parser (
    many1 (lex_char 'a')
  ) "bc")
with "Parse error at 1:1: Unexpected 'b'. Expected 'a'" in

utest test_parser (lex_number) "123abc"
with Success(123, ("abc", ("", 1, 4))) in
utest show_error (test_parser lex_number "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected digit" in

utest test_parser (lex_string "abc") "abcdef"
with Success("abc", ("def", ("", 1, 4))) in
utest test_parser (lex_string "abcdef") "abcdef"
with Success("abcdef", ("", ("", 1, 7))) in
utest show_error (test_parser (lex_string "abc") "def")
with "Parse error at 1:1: Unexpected 'd'. Expected 'abc'" in

utest
  test_parser (
    bind (lex_string "ab") (lam s1.
    bind (lex_string "cd") (lam s2.
    pure (concat s1 s2)))
  ) "abcde"
with Success ("abcd", ("e", ("", 1, 5))) in

utest test_parser lex_char_lit "'\n'" with Success (head "\n", ("", ("", 2, 2))) in

utest test_parser lex_string_lit ['"','"'] with Success ("", ("", ("", 1, 3))) in
utest test_parser lex_string_lit "\"FILE \\\"foo.mc\\\"\""
with Success ("FILE \"foo.mc\"", ("", ("", 1, 18))) in
utest test_parser (apr (lex_string "foo") lex_string_lit) "foo\"\\\"\""
with Success ("\"", ("", ("", 1, 8))) in

utest test_parser lex_float "3.14159" with Success(3.14159, ("", ("", 1, 8))) in
utest test_parser lex_float "3.2e-2" with Success(0.032, ("", ("", 1, 7))) in
utest test_parser lex_float "3.2e2" with Success(320.0, ("", ("", 1, 6))) in
utest test_parser lex_float "3e+2" with Success(300.0, ("", ("", 1, 5))) in
utest show_error(test_parser lex_float "42")
with "Parse error at 1:3: Unexpected end of input. Expected exponent or decimals" in

utest test_parser spaces "   abc"
with Success ((), ("abc", ("", 1, 4))) in
utest test_parser spaces "	  abc"
with Success ((), ("abc", ("", 1, 4))) in
utest test_parser spaces1 "	  abc"
with Success ((), ("abc", ("", 1, 4))) in
utest test_parser spaces "abc"
with Success ((), ("abc", ("", 1, 1))) in
utest show_error (test_parser spaces1 "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected whitespace" in
()
