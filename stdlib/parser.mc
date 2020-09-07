include "string.mc"
include "prelude.mc" -- TODO: Should not be needed

-- Debug stuff
let debug_flag = false
let debug = lam s. if debug_flag then printLn s else ()

-- The Parser monad -----------------------------

type Pos = {file: String, row: Int, col: Int}
-- A position carries a file name, a row number, and a column number

-- show_pos : Pos -> String
--
-- `show_pos pos` gives a string representation of `pos`.
let show_pos = lam pos.
  let file = if null pos.file
             then ""
             else concat (concat "FILE \"" pos.file) "\" "
  in
  let row_col = concat (concat (int2string pos.row) ":") (int2string pos.col) in
  concat file row_col

-- eqpos : Pos -> Pos -> Bool
--
-- Check if two positions are equal.
let eqpos = lam pos1 : Pos. lam pos2 : Pos.
  and (eqstr pos1.file pos2.file)
  (and (eqi pos1.row pos2.row) (eqi pos1.col pos2.col))

-- init_pos : String -> Pos
--
-- `init_pos "foo.ext"` gives a position which is at the start of
-- the file "foo.ext".
let init_pos = lam f. {file = f, row = 1, col = 1}

utest show_pos (init_pos "foo.mc") with "FILE \"foo.mc\" 1:1"
utest show_pos (init_pos "") with "1:1"

-- bumb_row : Pos -> Pos
--
-- Increase the row number by 1 and set column number to 1.
let bump_row = lam pos. {{pos with row = addi 1 pos.row} with col = 1}

-- bumb_col : Pos -> Pos
--
-- Increase the column number by 1.
let bump_col = lam pos. {pos with col = addi 1 pos.col}

type State = (String, Pos)
-- The parser state is the remaining input and the current position

type ParseResult
con Success : (Dyn, State) -> ParseResult
con Failure : (String, String, State) -> ParseResult
-- Success stores result of parsing
-- Failure stores found and expected token

type Parser = State -> ParseResult

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

utest test_parser end_of_input "" with Success((), ("", init_pos ""))

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

-- Core tests
utest test_parser next "abc"
with Success ('a', ("bc", {file = "", row = 1, col = 2}))

utest test_parser next "\""
with Success (head "\"", ("", {file = "", row = 1, col = 2}))

utest show_error (test_parser next "")
with "Parse error at 1:1: Unexpected end of input"

utest
  test_parser (
    bind next (lam c1.
    bind next (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", {file = "", row = 1, col = 3}))

utest
  show_error (test_parser (
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2]))
  ) "a")
with "Parse error at 1:2: Unexpected end of input"


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

utest test_parser (lex_char 'a') "ab"
with Success ('a', ("b", {file = "", row = 1, col = 2}))

utest show_error (test_parser (lex_char 'b') "ab")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'"

utest test_parser (
    bind (lex_char 'a') (lam c1.
    bind (lex_char 'b') (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", {file = "", row = 1, col = 3}))

utest show_error (
  test_parser (
    bind (lex_char 'b') (lam c1.
    bind (lex_char 'b') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'"

utest show_error (
  test_parser (
    bind (lex_char 'a') (lam c1.
    bind (lex_char 'a') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:2: Unexpected 'b'. Expected 'a'"

utest test_parser (alt (lex_char 'a') (lex_char 'b')) "abc"
with Success('a', ("bc", {file = "", row = 1, col = 2}))

utest test_parser (alt (lex_char 'b') (lex_char 'a')) "abc"
with Success('a', ("bc", {file = "", row = 1, col = 2}))

utest show_error (
  test_parser (
    alt (lex_char 'b') (lex_char 'c')
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b' or 'c'"

utest test_parser (not_followed_by (lex_char 'b')) "abc"
with Success((), ("abc", {file = "", row = 1, col = 1}))

utest show_error (test_parser (not_followed_by (lex_char 'a')) "abc")
with "Parse error at 1:1: Unexpected 'a'"

utest test_parser (many (lex_char 'a')) "abc"
with Success("a", ("bc", {file = "", row = 1, col = 2}))

utest test_parser (many (lex_char 'a')) "aaabc"
with Success("aaa", ("bc", {file = "", row = 1, col = 4}))

utest test_parser (many (lex_char 'a')) "bc"
with Success("", ("bc", {file = "", row = 1, col = 1}))

utest test_parser (many1 (lex_char 'a')) "abc"
with Success("a", ("bc", {file = "", row = 1, col = 2}))

utest test_parser (many1 (lex_char 'a')) "aaabc"
with Success("aaa", ("bc", {file = "", row = 1, col = 4}))

utest show_error (
  test_parser (
    many1 (lex_char 'a')
  ) "bc")
with "Parse error at 1:1: Unexpected 'b'. Expected 'a'"

-- lex_digits : Parser String
--
-- Parse a sequence of digits
let lex_digits = many1 (satisfy is_digit "digit")

-- lex_number : Parser Int
--
-- Parse a natural number.
let lex_number = fmap string2int lex_digits

utest test_parser (lex_number) "123abc"
with Success(123, ("abc", {file = "", row = 1, col = 4}))

utest show_error (test_parser lex_number "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected digit"

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

utest test_parser (lex_string "abc") "abcdef"
with Success("abc", ("def", {file = "", row = 1, col = 4}))
utest test_parser (lex_string "abcdef") "abcdef"
with Success("abcdef", ("", {file = "", row = 1, col = 7}))
utest show_error (test_parser (lex_string "abc") "def")
with "Parse error at 1:1: Unexpected 'd'. Expected 'abc'"

utest
  test_parser (
    bind (lex_string "ab") (lam s1.
    bind (lex_string "cd") (lam s2.
    pure (concat s1 s2)))
  ) "abcde"
with Success ("abcd", ("e", {file = "", row = 1, col = 5}))

-- Parser Char
--
-- Parse a character literal.
-- TODO: Support escaped characters (also in OCaml parser)
let lex_char_lit = wrapped_in (lex_char ''') (lex_char ''') next

utest test_parser lex_char_lit "'\n'"
with Success (head "\n", ("", {file = "", row = 2, col = 2}))

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

utest test_parser lex_string_lit ['"','"']
with Success ("", ("", {file = "", row = 1, col = 3}))

utest test_parser lex_string_lit "\"FILE \\\"foo.mc\\\"\""
with Success ("FILE \"foo.mc\"", ("", {file = "", row = 1, col = 18}))

utest test_parser (apr (lex_string "foo") lex_string_lit) "foo\"\\\"\""
with Success ("\"", ("", {file = "", row = 1, col = 8}))

-- lex_numeral : Parser String
--
-- Parse a string representing a floating point numeral
let lex_numeral =
  let maybe = lam p. alt p (pure "") in
  let decimals = label "decimals" (liftA2 cons (lex_char '.') lex_digits) in
  let exponent = label "exponent" (
    liftA2 cons (lex_char 'e')
           (liftA2 concat (foldr1 alt [lex_string "-", lex_string "+", pure ""])
                   lex_digits))
  in liftA2 concat lex_digits
            (alt exponent (liftA2 concat decimals (maybe exponent)))

-- lex_float : Parser Float
--
-- Parse a floating point number
let lex_float = fmap string2float lex_numeral

utest test_parser lex_float "3.14159"
with Success(3.14159, ("", {file = "", row = 1, col = 8}))

utest test_parser lex_float "3.2e-2"
with Success(0.032, ("", {file = "", row = 1, col = 7}))

utest test_parser lex_float "3.2e2"
with Success(320.0, ("", {file = "", row = 1, col = 6}))

utest test_parser lex_float "3e+2"
with Success(300.0, ("", {file = "", row = 1, col = 5}))

utest show_error(test_parser lex_float "42")
with "Parse error at 1:3: Unexpected end of input. Expected exponent or decimals"

-- spaces : Parser ()
--
-- Parse zero or more whitespace characters.
let spaces = void (many (satisfy is_whitespace "whitespace"))

-- spaces1 : Parser ()
--
-- Parse one or more whitespace characters.
let spaces1 = void (many1 (satisfy is_whitespace "whitespace"))

utest test_parser spaces "   abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest test_parser spaces "	  abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest test_parser spaces1 "	  abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest test_parser spaces "abc"
with Success ((), ("abc", {file = "", row = 1, col = 1}))

utest show_error (test_parser spaces1 "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected whitespace"

-- lex_token : Parser () -> Parser a -> Parser a
--
-- `lex_token ws p` parses `p`, using `ws` to consume any trailing
-- whitespace or comments.
let lex_token = lam ws. lam p. apl p ws


mexpr
-- The following code is meant to serve as an example of how
-- to write a parser for a small language. The definitions would
-- typically be top-level, but are kept local here.

-- Here is the AST type for the untyped lambda calculus with
-- numbers, let bindings and if expressions.

type Expr in

con Abs : (String, Expr) -> Expr in
con App : (Expr, Expr) -> Expr in
con Var : String -> Expr in
con Num : Int -> Expr in
con Let : (String, Expr, Expr) -> Expr in
con If  : (Expr, Expr, Expr) -> Expr in

-- We start by defining the tokens of the language.

-- line_comment : Parser ()
--
-- Parse a line comment, ignoring its contents.
let line_comment =
  void (apr (apr (lex_string "--")
                 (many (satisfy (lam c. not (eqstr "\n" [c])) "")))
            (alt (lex_string "\n") end_of_input))
in

-- ws : Parser ()
--
-- Parse whitespace or comments.
let ws = void (many (alt line_comment spaces1)) in

-- token : Parser a -> Parser a
--
-- `token p` parses `p` and any trailing whitespace or comments.
let token = lex_token ws in

-- string : String -> Parser String
--
-- `string s` parses the string `s` as a token
let string = lam s. token (lex_string s) in

-- symbol : String -> Parser String
--
-- `symbol` is an alias for `string`
let symbol = string in

-- is_valid_char : Char -> Bool
--
-- Check if a character is valid in an identifier.
let is_valid_char = lam c.
  or (is_alphanum c) (eqchar c '_')
in

-- reserved : String -> Parser String
--
-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved = lam s.
  void (token (apl (lex_string s) (not_followed_by (satisfy is_valid_char ""))))
in

-- number : Parser Int
let number = token lex_number in

-- List of reserved keywords
let keywords =
  ["lam", "let", "in", "if", "then", "else"]
in

-- ident : Parser String
--
-- Parse an identifier, but require that it is not in the list
-- of reserved keywords.
let identifier =
  let valid_id =
    bind (satisfy (lam c. or (is_alpha c) (eqchar '_' c)) "valid identifier") (lam c.
    bind (token (many (satisfy is_valid_char ""))) (lam cs.
    pure (cons c cs)))
  in
  try (
    bind valid_id (lam x.
    if any (eqstr x) keywords
    then fail (concat (concat "keyword '" x) "'") "identifier"
    else pure x)
  )
in

-- We now use the tokens to define the main parser for our
-- language:

recursive
-- atom : Parser Expr
--
-- Innermost expression parser.
  let atom = lam st.
    let var_access =
      let _ = debug "== Parsing var_access" in
      fmap (lam x. Var x) identifier in
    let num =
      let _ = debug "== Parsing num ==" in
      fmap (lam n. Num n) number
    in
      label "atomic expression"
      (alt var_access num) st

  -- expr: Parser Expr
  --
  -- Main expression parser.
  let expr = lam st.
    -- left : Parser Expr
    --
    -- Left recursive expressions, i.e. function application
    let left =
      bind (many1 atom) (lam as.
      pure (foldl1 (curry (lam x. App x)) as))
    in
    let abs =
      let _ = debug "== Parsing abstraction ==" in
      bind (reserved "lam") (lam _.
      bind identifier (lam x.
      bind (symbol ".") (lam _.
      bind expr (lam e.
      pure (Abs (x, e))))))
    in
    let let_ =
      let _ = debug "== Parsing let ==" in
      bind (reserved "let") (lam _.
      bind identifier (lam x.
      bind (symbol "=") (lam _.
      bind expr (lam e.
      bind (symbol "in") (lam _.
      bind expr (lam body.
      pure (Let (x, e, body))))))))
    in
    let if_ =
      let _ = debug "== Parsing if ==" in
      bind (reserved "if") (lam _.
      bind expr (lam cnd.
      bind (reserved "then") (lam _.
      bind expr (lam thn.
      bind (reserved "else") (lam _.
      bind expr (lam els.
      pure (If(cnd, thn, els))))))))
    in
    label "expression"
    (alt left
    (alt abs
    (alt let_
    if_))) st
in

let prog_string = "let f = lam x . if lt 0 x then addi x 1 else 0 in f 5\n-- This line will be ignored" in

let prog =
  Let ("f",
    Abs ("x",
      If (App (App (Var "lt", Num 0), Var "x"),
          App (App (Var "addi", Var "x"), Num 1),
          Num 0)),
    App (Var "f", Num 5))
in

utest test_parser expr prog_string
with Success (prog, ("", {file = "", row = 2, col = 29})) in

let bad_prog_string = "let f = lam x . x in" in

utest show_error (test_parser expr bad_prog_string)
with "Parse error at 1:21: Unexpected end of input. Expected expression" in
()