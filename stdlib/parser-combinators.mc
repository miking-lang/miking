include "string.mc"
include "prelude.mc" -- TODO(?,?): Should not be needed

-- Debug stuff
let debugFlag = false
let debug = lam s. if debugFlag then printLn s else ()

-- The Parser monad -----------------------------

type Pos = {file: String, row: Int, col: Int}
-- A position carries a file name, a row number, and a column number

-- showPos : Pos -> String
--
-- `showPos pos` gives a string representation of `pos`.
let showPos = lam pos.
  let file = if null pos.file
             then ""
             else concat (concat "FILE \"" pos.file) "\" "
  in
  let rowCol = concat (concat (int2string pos.row) ":") (int2string pos.col) in
  concat file rowCol

-- eqpos : Pos -> Pos -> Bool
--
-- Check if two positions are equal.
let eqpos = lam pos1 : Pos. lam pos2 : Pos.
  and (eqString pos1.file pos2.file)
  (and (eqi pos1.row pos2.row) (eqi pos1.col pos2.col))

-- initPos : String -> Pos
--
-- `initPos "foo.ext"` gives a position which is at the start of
-- the file "foo.ext".
let initPos = lam f. {file = f, row = 1, col = 1}

utest showPos (initPos "foo.mc") with "FILE \"foo.mc\" 1:1"
utest showPos (initPos "") with "1:1"

-- bumbRow : Pos -> Pos
--
-- Increase the row number by 1 and set column number to 1.
let bumpRow = lam pos. {{pos with row = addi 1 pos.row} with col = 1}

-- bumbCol : Pos -> Pos
--
-- Increase the column number by 1.
let bumpCol = lam pos. {pos with col = addi 1 pos.col}

type State = (String, Pos)
-- The parser state is the remaining input and the current position

type ParseResult
con Success : (Dyn, State) -> ParseResult
con Failure : (String, String, State) -> ParseResult
-- Success stores result of parsing
-- Failure stores found and expected token

type Parser = State -> ParseResult

type Filename = String

-- runParser : Filename -> Parser a -> String -> ParseResult a
--
-- Run a parser with a specified filename and input.
let runParser = lam f : Filename. lam p : Parser. lam input : String.
    p (input, (initPos f))

-- testParser : Parser a -> String -> ParseResult
--
-- Run a parser without a current file.
let testParser = runParser ""

-- fail : String -> String -> Parser a
--
-- Fail parsing with custom info
let fail = lam found. lam expected. lam st.
  Failure (found, expected, st)

-- showError : ParseResult a -> String
--
-- Show human readable error message from failed parse.
-- Fails if argument is not a failure.
let showError = lam f : ParseResult.
  match f with Failure t then
    let found = t.0 in
    let expected = t.1 in
    let pos = (t.2).1 in
    concat (concat (concat "Parse error at " (showPos pos)) ": ")
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

-- endOfInput : Parser ()
--
-- Fail parsing, unless the input stream is empty
let endOfInput = lam st.
  let input = st.0 in
  if null input
  then pure () st
  else fail (showChar (head input)) "end of input" st

utest testParser endOfInput "" with Success((), ("", initPos ""))

-- next : Parser char
--
-- Read next character from input stream
-- TODO(?,?): It would most likely be faster to index into
--       an array than to take the tail of a string
let next = lam st.
  let input = st.0 in
  let pos = st.1 in
  if null input
  then fail "end of input" "" st
  else
    let c = head input in
    let pos2 = if eqString [c] "\n" then bumpRow pos else bumpCol pos in
    pure c (tail input, pos2)

-- Core tests
utest testParser next "abc"
with Success ('a', ("bc", {file = "", row = 1, col = 2}))

utest testParser next "\""
with Success (head "\"", ("", {file = "", row = 1, col = 2}))

utest showError (testParser next "")
with "Parse error at 1:1: Unexpected end of input"

utest
  testParser (
    bind next (lam c1.
    bind next (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", {file = "", row = 1, col = 3}))

utest
  showError (testParser (
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

-- notFollowedBy : Parser a -> Parser ()
--
-- `notFollowedBy p` succeeds (without consuming input)
-- only if `p` does not succeed.
let notFollowedBy = lam p. lam st.
  let res1 = p st in
  match res1 with Failure _ then
    pure () st
  else
    let res2 = next st in
    match res2 with Success t then
      let c = t.0 in
      fail (showChar c) "" st
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
  else lam _ . fail (showChar c) expected st) st

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
-- `alt`, e.g., `label "expression" (alt (alt let Lam) ...)`
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

-- wrappedIn : Parser l -> Parser r -> Parser a -> Parser a
--
-- `wrappedIn pl pr p` parses `p` preceded by `pl` and
-- succeeded by `pr`.
let wrappedIn = lam pl. lam pr. lam p.
  apr pl (apl p pr)

-- sepBy : Parser s -> Parser a -> Parser [a]
--
-- `sepBy sep p` parses zero or more occurrences of
-- `p` separated by single occurrences of `sep`.
let sepBy = lam sep. lam p.
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  bind (many (apr sep p)) (lam tl.
  pure (concat hd tl)))


-- Lexers ---------------------------------------------

-- Lexers are parsers that do not consume trailing whitespace

-- lexChar : Char -> Parser Char
--
-- Parse a specific character.
let lexChar = lam c. satisfy (eqChar c) (showChar c)

utest testParser (lexChar 'a') "ab"
with Success ('a', ("b", {file = "", row = 1, col = 2}))

utest showError (testParser (lexChar 'b') "ab")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'"

utest testParser (
    bind (lexChar 'a') (lam c1.
    bind (lexChar 'b') (lam c2.
    pure [c1, c2]))
  ) "abc"
with Success ("ab", ("c", {file = "", row = 1, col = 3}))

utest showError (
  testParser (
    bind (lexChar 'b') (lam c1.
    bind (lexChar 'b') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b'"

utest showError (
  testParser (
    bind (lexChar 'a') (lam c1.
    bind (lexChar 'a') (lam c2.
    pure [c1, c2]))
  ) "abc")
with "Parse error at 1:2: Unexpected 'b'. Expected 'a'"

utest testParser (alt (lexChar 'a') (lexChar 'b')) "abc"
with Success('a', ("bc", {file = "", row = 1, col = 2}))

utest testParser (alt (lexChar 'b') (lexChar 'a')) "abc"
with Success('a', ("bc", {file = "", row = 1, col = 2}))

utest showError (
  testParser (
    alt (lexChar 'b') (lexChar 'c')
  ) "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected 'b' or 'c'"

utest testParser (notFollowedBy (lexChar 'b')) "abc"
with Success((), ("abc", {file = "", row = 1, col = 1}))

utest showError (testParser (notFollowedBy (lexChar 'a')) "abc")
with "Parse error at 1:1: Unexpected 'a'"

utest testParser (many (lexChar 'a')) "abc"
with Success("a", ("bc", {file = "", row = 1, col = 2}))

utest testParser (many (lexChar 'a')) "aaabc"
with Success("aaa", ("bc", {file = "", row = 1, col = 4}))

utest testParser (many (lexChar 'a')) "bc"
with Success("", ("bc", {file = "", row = 1, col = 1}))

utest testParser (many1 (lexChar 'a')) "abc"
with Success("a", ("bc", {file = "", row = 1, col = 2}))

utest testParser (many1 (lexChar 'a')) "aaabc"
with Success("aaa", ("bc", {file = "", row = 1, col = 4}))

utest showError (
  testParser (
    many1 (lexChar 'a')
  ) "bc")
with "Parse error at 1:1: Unexpected 'b'. Expected 'a'"

-- lexDigits : Parser String
--
-- Parse a sequence of digits
let lexDigits = many1 (satisfy isDigit "digit")

-- lexNumber : Parser Int
--
-- Parse a natural number.
let lexNumber = fmap string2int lexDigits

utest testParser (lexNumber) "123abc"
with Success(123, ("abc", {file = "", row = 1, col = 4}))

utest showError (testParser lexNumber "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected digit"

-- lexString : String -> Parser String
--
-- Parse a specific string.
recursive
  let lexString = lam s.
    if null s
    then pure ""
    else
      let c = head s in
      let cs = tail s in
      label (concat "'" (concat s "'")) (
        try ( -- This 'try' makes the parser consume the whole string or nothing
          bind (lexChar c) (lam _ .
          bind (lexString cs) (lam _ .
          pure (cons c cs)))
        ))
end

utest testParser (lexString "abc") "abcdef"
with Success("abc", ("def", {file = "", row = 1, col = 4}))
utest testParser (lexString "abcdef") "abcdef"
with Success("abcdef", ("", {file = "", row = 1, col = 7}))
utest showError (testParser (lexString "abc") "def")
with "Parse error at 1:1: Unexpected 'd'. Expected 'abc'"

utest
  testParser (
    bind (lexString "ab") (lam s1.
    bind (lexString "cd") (lam s2.
    pure (concat s1 s2)))
  ) "abcde"
with Success ("abcd", ("e", {file = "", row = 1, col = 5}))

-- Parser Char
--
-- Parse a character literal.
-- TODO(?,?): Support escaped characters (also in OCaml parser)
let lexCharLit = wrappedIn (lexChar ''') (lexChar ''') next

utest testParser lexCharLit "'\n'"
with Success (head "\n", ("", {file = "", row = 2, col = 2}))

-- Parser String
--
-- Parse a string literal.
let lexStringLit =
  -- TODO(?,?): Are other escaped characters handled correctly?
  let escaped =
    try (alt (apr (lexString "\\\\") (pure (head "\\")))
             (apr (lexString "\\") (fmap head (lexString "\""))))
  in
  wrappedIn (lexString "\"") (lexString "\"")
             (many (alt escaped (satisfy (lam c. not (eqString [c] "\"")) "")))

utest testParser lexStringLit ['"','"']
with Success ("", ("", {file = "", row = 1, col = 3}))

utest testParser lexStringLit "\"FILE \\\"foo.mc\\\"\""
with Success ("FILE \"foo.mc\"", ("", {file = "", row = 1, col = 18}))

utest testParser (apr (lexString "foo") lexStringLit) "foo\"\\\"\""
with Success ("\"", ("", {file = "", row = 1, col = 8}))

-- lexNumeral : Parser String
--
-- Parse a string representing a floating point numeral
let lexNumeral =
  let maybe = lam p. alt p (pure "") in
  let decimals = label "decimals" (liftA2 cons (lexChar '.') lexDigits) in
  let exponent = label "exponent" (
    liftA2 cons (lexChar 'e')
           (liftA2 concat (foldr1 alt [lexString "-", lexString "+", pure ""])
                   lexDigits))
  in liftA2 concat lexDigits
            (alt exponent (liftA2 concat decimals (maybe exponent)))

-- lexFloat : Parser Float
--
-- Parse a floating point number
let lexFloat = fmap string2float lexNumeral

utest testParser lexFloat "3.14159"
with Success(3.14159, ("", {file = "", row = 1, col = 8}))

utest testParser lexFloat "3.2e-2"
with Success(0.032, ("", {file = "", row = 1, col = 7}))

utest testParser lexFloat "3.2e2"
with Success(320.0, ("", {file = "", row = 1, col = 6}))

utest testParser lexFloat "3e+2"
with Success(300.0, ("", {file = "", row = 1, col = 5}))

utest showError(testParser lexFloat "42")
with "Parse error at 1:3: Unexpected end of input. Expected exponent or decimals"

-- spaces : Parser ()
--
-- Parse zero or more whitespace characters.
let spaces = void (many (satisfy isWhitespace "whitespace"))

-- spaces1 : Parser ()
--
-- Parse one or more whitespace characters.
let spaces1 = void (many1 (satisfy isWhitespace "whitespace"))

utest testParser spaces "   abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest testParser spaces "	  abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest testParser spaces1 "	  abc"
with Success ((), ("abc", {file = "", row = 1, col = 4}))

utest testParser spaces "abc"
with Success ((), ("abc", {file = "", row = 1, col = 1}))

utest showError (testParser spaces1 "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected whitespace"

-- lexToken : Parser () -> Parser a -> Parser a
--
-- `lexToken ws p` parses `p`, using `ws` to consume any trailing
-- whitespace or comments.
let lexToken = lam ws. lam p. apl p ws


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

-- lineComment : Parser ()
--
-- Parse a line comment, ignoring its contents.
let lineComment =
  void (apr (apr (lexString "--")
                 (many (satisfy (lam c. not (eqString "\n" [c])) "")))
            (alt (lexString "\n") endOfInput))
in

-- ws : Parser ()
--
-- Parse whitespace or comments.
let ws = void (many (alt lineComment spaces1)) in

-- token : Parser a -> Parser a
--
-- `token p` parses `p` and any trailing whitespace or comments.
let token = lexToken ws in

-- string : String -> Parser String
--
-- `string s` parses the string `s` as a token
let string = lam s. token (lexString s) in

-- symbol : String -> Parser String
--
-- `symbol` is an alias for `string`
let symbol = string in

-- isValidChar : Char -> Bool
--
-- Check if a character is valid in an identifier.
let isValidChar = lam c.
  or (isAlphanum c) (eqChar c '_')
in

-- reserved : String -> Parser String
--
-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved = lam s.
  void (token (apl (lexString s) (notFollowedBy (satisfy isValidChar ""))))
in

-- number : Parser Int
let number = token lexNumber in

-- List of reserved keywords
let keywords =
  ["lam", "let", "in", "if", "then", "else"]
in

-- ident : Parser String
--
-- Parse an identifier, but require that it is not in the list
-- of reserved keywords.
let identifier =
  let validId =
    bind (satisfy (lam c. or (isAlpha c) (eqChar '_' c)) "valid identifier") (lam c.
    bind (token (many (satisfy isValidChar ""))) (lam cs.
    pure (cons c cs)))
  in
  try (
    bind validId (lam x.
    if any (eqString x) keywords
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
    let varAccess =
      let _ = debug "== Parsing varAccess" in
      fmap (lam x. Var x) identifier in
    let num =
      let _ = debug "== Parsing num ==" in
      fmap (lam n. Num n) number
    in
      label "atomic expression"
      (alt varAccess num) st

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

let progString = "let f = lam x . if lt 0 x then addi x 1 else 0 in f 5\n-- This line will be ignored" in

let prog =
  Let ("f",
    Abs ("x",
      If (App (App (Var "lt", Num 0), Var "x"),
          App (App (Var "addi", Var "x"), Num 1),
          Num 0)),
    App (Var "f", Num 5))
in

utest testParser expr progString
with Success (prog, ("", {file = "", row = 2, col = 29})) in

let badProgString = "let f = lam x . x in" in

utest showError (testParser expr badProgString)
with "Parse error at 1:21: Unexpected end of input. Expected expression" in
()
