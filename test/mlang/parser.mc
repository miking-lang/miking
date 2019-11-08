include "seq.mc"
include "string.mc"

main
-- Printing stuff
let print_ln = lam s. print (concat s "\n") in
let debug_flag = false in
let debug = lam s. if debug_flag then print_ln s else () in

-- Auxiliary stuff
let curry = lam f. lam x. lam y. f(x, y) in

-- The Parser monad -----------------------------

-- type Pos = (String, Int, Int)
let eqpos = lam pos1. lam pos2.
  and (eqstr pos1.0 pos2.0)
  (and (eqi pos1.1 pos2.1) (eqi pos1.2 pos2.2))
in

let init_pos = lam f. (f, 1, 1) in

let show_pos = lam pos.
  let file = if null pos.0
             then ""
             else concat (concat "FILE \"" pos.0) "\" "
  in
  let row_col = concat (concat (int2string pos.1) ":") (int2string pos.2) in
  concat file row_col
in

utest show_pos (init_pos "foo.mc") with "FILE \"foo.mc\" 1:1" in
utest show_pos (init_pos "") with "1:1" in

-- type State = (String, Pos)

let bump_col = lam pos. (pos.0, pos.1, addi 1 pos.2) in
let bump_row = lam pos. (pos.0, addi 1 pos.1, 1) in

con Success : (Dyn, Dyn) in -- Success : (a, (String, Pos)) -> ParseResult a
con Failure : (Dyn, Dyn, Dyn) in -- Failure : (String, String, (String, Pos)) -> ParseResult a
-- Success stores result of parsing, rest of input and current position
-- Failure stores found and expected token, rest of input and position of failure

-- type Parser a = String -> ParseResult a

let run_parser = lam f. lam p. lam input. p (input, (init_pos f)) in
let test_parser = run_parser "" in

-- fail : String -> String -> Parser a
--
-- Fail parsing with custom info
let fail = lam found. lam expected. lam env.
  Failure (found, expected, env)
in

-- show_error : ParseResult a -> String
--
-- Show human readable error message from failed parse.
-- Fails if argument is not a failure.
let show_error = lam f.
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
in

-- fmap : (a -> b) -> Parser a -> Parser b
let fmap = lam f. lam p. lam env.
  let res = p env in
  match res with Success t then
    let v = t.0 in
    let rest = t.1 in
    Success (f v, rest)
  else res
in

-- pure : a -> Parser a
let pure = lam v. lam env. Success(v, env) in

-- ap : Parser (a -> b) -> Parser a -> Parser b
let ap = lam pf. lam p. lam env.
  let res1 = pf env in
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
in

-- apl : Parser a -> Parser b -> Parser a
--
-- Run two parser, use result of first one
let apl = lam p1. lam p2. lam env.
  let res1 = p1 env in
  match res1 with Success t1 then
    let v1 = t1.0 in
    let rest1 = t1.1 in
    let res2 = p2 rest1 in
    match res2 with Success t2 then
      let rest2 = t2.1 in
      pure v1 rest2
    else res2
  else res1
in

-- apr : Parser a -> Parser b -> Parser b
--
-- Run two parser, use result of second one
let apr = lam p1. lam p2. lam env.
  let res1 = p1 env in
  match res1 with Success t1 then
    let rest1 = t1.1 in
    let res2 = p2 rest1 in
    match res2 with Success t2 then
      let v2 = t2.0 in
      let rest2 = t2.1 in
      pure v2 rest2
    else res2
  else res1
in

-- bind : Parser a -> (a -> Parser b) -> Parser b
--
-- Typical usage is `bind p1 (lam x. p2)`, i.e. run `p1` and
-- pass result to a function running another parser.
let bind = lam p. lam f. lam env.
  let res = p env in
  match res with Success t then
    let x = t.0 in
    let rest = t.1 in
    f x rest
  else -- propagate Failure
    res
in

-- Run parser and ignore result
let void = apl (pure ()) in

-- when : bool -> Parser a -> Parser ()
--
-- Monadic conditional. `when b p` runs `p` (ignoring the
-- result) if `b` is true.
let when = lam b. lam p. lam env.
  if b then void p else pure ()
in

-- Core ------------------------------------------------

let end_of_input = lam env.
  let input = env.0 in
  if null input
  then pure () env
  else fail (show_char (head input)) "end of input" env
in

utest test_parser end_of_input "" with Success((), ("", init_pos "")) in

-- next : Parser char
--
-- Read next character from input stream
-- TODO: It would most likely be faster to index into
--       an array than to take the tail of a string
let next = lam env.
  let input = env.0 in
  let pos = env.1 in
  if null input
  then fail "end of input" "" env
  else
    let c = head input in
    let pos2 = if eqstr [c] "\n" then bump_row pos else bump_col pos in
    pure c (tail input, pos2)
in

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

-- alt : Parser a -> Parser a -> Parser a
--
-- `alt p1 p2` tries to parse `p1`, but falls back
-- to `p2` if `p1` fails without consuming any input.
let alt = lam p1. lam p2. lam env.
  let res1 = p1 env in
  match res1 with Failure t1 then
    let env2 = t1.2 in
    if eqpos env.1 env2.1 then
      let res2 = p2 env in
      match res2 with Failure t2 then
        let env3 = t2.2 in
        if eqpos env2.1 env3.1 then
          let exp = concat (concat t1.1 " or ") t2.1 in
          Failure (t2.0, exp, env3)
        else res2 -- p2 consumed input, don't merge expected
      else res2 -- Propagate Success
    else res1 -- p1 consumed input, don't backtrack
  else res1 -- Propagate Success
in

-- not_followed_by : Parser a -> Parser ()
--
-- `not_followed_by p` succeeds (without consuming input)
-- only if `p` does not succeed.
let not_followed_by = lam p. lam env.
  let res1 = p env in
  match res1 with Failure _ then
    pure () env
  else
    let res2 = next env in
    match res2 with Success t then
      let c = t.0 in
      fail (show_char c) "" env
    else res2
in

-- satisfy : (Char -> Bool) -> String -> Parser Char
--
-- `satisfy cnd exp` succeeds with the next character
-- if `cnd` returns true for that character. `exp` is
-- the expected token.
let satisfy = lam cnd. lam expected. lam env.
  bind next (lam c.
  if cnd c
  then pure c
  else lam _. fail (show_char c) expected env) env
in

-- try : Parser a -> Parser a
--
-- `try p` is used for backtracking. It parses `p`, but
-- fails without consuming input if `p` fails.
let try = lam p. lam env.
  let res = p env in
  match res with Failure t then
    Failure (t.0, t.1, env)
  else -- Propagate Success
    res
in

-- label : String -> Parser p -> Parser p
--
-- `label l p` parses `p` but changes the "expected" token
-- to `l` if `p` fails. Typical use is for big chains of
-- `alt`, e.g., `label "expression" (alt (alt let_ lam_) ...)`
let label = lam l. lam p. lam env.
  let res = p env in
  match res with Failure t then
  if eqpos (t.2).1 env.1
  then Failure (t.0, l, t.2)
  else res
  else -- Propagate success
    res
in

-- Combinators ---------------------------------

-- many : Parser a -> Parser [a]
--
-- Parse zero or more occurrences of a parser.
let many = fix (lam many. lam p.
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  if null hd
  then pure []
  else bind (many p) (lam tl. pure (concat hd tl)))
) in

-- many1 : Parser a -> Parser [a]
--
-- Parse one or more occurrences of a parser.
let many1 = lam p.
  bind p (lam hd.
  bind (many p) (lam tl.
  pure (cons hd tl)))
in

con Some : Dyn in -- Some : Option a
con None in       -- None : Option a

-- optional : Parser a -> Parser (Option a)
let optional = lam p.
  alt (fmap Some p) (pure None)
in

-- wrapped_in : Parser l -> Parser r -> Parser a -> Parser a
--
-- `wrapped_in pl pr p` parses `p` preceded by `pl` and
-- succeeded by `pr`.
let wrapped_in = lam pl. lam pr. lam p.
  apr pl (apl p pr)
in

-- sep_by : Parser s -> Parser a -> Parser [a]
--
-- `sep_by sep p` parses zero or more occurrences of
-- `p` separated by single occurrences of `sep`.
let sep_by = lam sep. lam p.
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  bind (many (apr sep p)) (lam tl.
  pure (concat hd tl)))
in

-- Lexers ---------------------------------------------

-- Lexers are parsers that do not consume trailing whitespace

-- lex_char : Char -> Parser Char
--
-- Parse a specific character.
let lex_char = lam c. satisfy (eqchar c) (show_char c) in

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

-- lex_number : Parser Int
--
-- Parse a natural number.
let lex_number = fmap string2int (many1 (satisfy is_digit "digit")) in

utest test_parser (lex_number) "123abc"
with Success(123, ("abc", ("", 1, 4))) in
utest show_error (test_parser lex_number "abc")
with "Parse error at 1:1: Unexpected 'a'. Expected digit" in

-- lex_string : String -> Parser String
--
-- Parse a specific string.
let lex_string = fix (lam lex_string. lam s.
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
) in

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

-- Parser Char
--
-- Parse a character literal.
-- TODO: Support escaped characters (also in OCaml parser)
let lex_char_lit = wrapped_in (lex_char ''') (lex_char ''') next in

utest test_parser lex_char_lit "'\n'" with Success (head "\n", ("", ("", 2, 2))) in

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
in

utest test_parser lex_string_lit ['"','"'] with Success ("", ("", ("", 1, 3))) in
utest test_parser lex_string_lit "\"FILE \\\"foo.mc\\\"\""
with Success ("FILE \"foo.mc\"", ("", ("", 1, 18))) in
utest test_parser (apr (lex_string "foo") lex_string_lit) "foo\"\\\"\""
with Success ("\"", ("", ("", 1, 8))) in

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
in

utest test_parser lex_float "3.14159" with Success(3.14159, ("", ("", 1, 8))) in
utest test_parser lex_float "3.2e-2" with Success(0.032, ("", ("", 1, 7))) in
utest test_parser lex_float "3.2e2" with Success(320.0, ("", ("", 1, 6))) in
utest test_parser lex_float "3e+2" with Success(300.0, ("", ("", 1, 5))) in
utest show_error(test_parser lex_float "42")
with "Parse error at 1:3: Unexpected end of input. Expected exponent or decimals" in


-- spaces : Parser ()
--
-- Parse zero or more whitespace characters.
let spaces = void (many (satisfy is_whitespace "whitespace")) in

-- spaces1 : Parser ()
--
-- Parse one or more whitespace characters.
let spaces1 = void (many1 (satisfy is_whitespace "whitespace")) in

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

-- lex_token : Parser () -> Parser a -> Parser a
--
-- `lex_token ws p` parses `p`, using `ws` to consume any trailing
-- whitespace or comments.
let lex_token = lam ws. lam p. apl p ws in

-- MCore tokens ----------------------------------

-- line_comment : Parser ()
--
-- Parse a line comment, ignoring its contents.
let line_comment =
  void (apr (apr (alt (lex_string "--") (lex_string "//"))
                 (many (satisfy (lam c. not (eqstr "\n" [c])) "")))
            (alt (lex_string "\n") end_of_input))
in

utest test_parser line_comment "-- this is a comment
this is not"
with Success((), ("this is not", ("",2,1))) in

-- ws : Parser ()
--
-- Parse whitespace or comments.
let ws = void (many (alt line_comment spaces1)) in

utest test_parser ws "   -- this is a comment
--
    foo" with Success((), ("foo", ("", 3, 5))) in

-- token : Parser a -> Parser a
--
-- `token p` parses `p` and any trailing whitespace or comments.
let token = lex_token ws in

-- string : String -> Parser String
let string = lam s. token (lex_string s) in

utest test_parser (string "ab") "abc"
with Success("ab", ("c", ("", 1, 3))) in
utest test_parser (string "abc") "abc def"
with Success("abc", ("def", ("", 1, 5))) in
utest test_parser (many (alt (string "ab") (string "cd"))) "ab cd ef"
with Success(["ab", "cd"], ("ef", ("", 1, 7))) in

-- symbol : String -> Parser String
let symbol = string in

utest test_parser (symbol "(") "(abc)"
with Success("(", ("abc)", ("", 1, 2))) in
utest test_parser (symbol "(") "(  abc)"
with Success("(", ("abc)", ("", 1, 4))) in

let is_valid_char = lam c.
  or (is_alphanum c) (eqchar c '_')
in

utest is_valid_char '0' with true in
utest is_valid_char '9' with true in
utest is_valid_char 'A' with true in
utest is_valid_char 'z' with true in
utest is_valid_char '_' with true in

-- reserved : String -> Parser String
--
-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved = lam s.
  void (token (apl (lex_string s) (not_followed_by (satisfy is_valid_char ""))))
in

utest test_parser (reserved "lam") "lam x. x"
with Success((), ("x. x", ("", 1, 5))) in
utest show_error (test_parser (reserved "lam") "lambda")
with "Parse error at 1:4: Unexpected 'b'" in
utest show_error (test_parser (reserved "fix") "fix_")
with "Parse error at 1:4: Unexpected '_'" in
utest show_error (test_parser (reserved "lam") "la")
with "Parse error at 1:1: Unexpected end of input. Expected 'lam'" in

-- number : Parser Int
let number = token lex_number in

-- float : Parser Float
let float = token lex_float in

-- parens : Parser a -> Parser a
let parens = wrapped_in (symbol "(") (symbol ")") in

-- brackets : Parser a -> Parser a
let brackets = wrapped_in (symbol "[") (symbol "]") in

utest test_parser (parens (lex_string "abc")) "(abc)"
with Success("abc", ("", ("", 1, 6))) in
utest test_parser (brackets (many (string "abc"))) "[abc abc]"
with Success(["abc", "abc"], ("", ("", 1, 10))) in
utest show_error (test_parser (parens (lex_string "abc")) "(abc")
with "Parse error at 1:5: Unexpected end of input. Expected ')'" in

-- char_lit : Parser Char
let char_lit = token lex_char_lit in

utest test_parser (char_lit) "'a'"
with Success('a', ("", ("", 1,4))) in
utest test_parser (char_lit) "'a' bc"
with Success('a', ("bc", ("", 1,5))) in

-- string_lit : Parser String
let string_lit = token lex_string_lit in

utest test_parser (string_lit) "\"foobar\""
with Success("foobar", ("", ("", 1,9))) in
utest test_parser (string_lit) "\"\" rest"
with Success("", ("rest", ("", 1,4))) in

-- comma_sep : Parser a -> Parser [a]
let comma_sep = sep_by (symbol ",") in

utest test_parser (comma_sep (string "a")) "a, a, a"
with Success(["a", "a", "a"],("", ("", 1,8))) in
utest test_parser (comma_sep (string "a")) "a"
with Success(["a"],("", ("", 1,2))) in
utest show_error (test_parser (comma_sep (string "a")) "a ,a,b")
with "Parse error at 1:6: Unexpected 'b'. Expected 'a'" in
utest test_parser (brackets (comma_sep number)) "[ 1 , 2, 3]"
with Success([1,2,3], ("", ("", 1, 12))) in

-- List of reserved keywords
let keywords =
  ["let", "in", "if", "then", "else", "match", "with", "con", "lam", "fix", "utest"]
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

utest test_parser identifier "foo" with Success("foo", ("", ("", 1, 4))) in
utest test_parser identifier "fix_" with Success("fix_", ("", ("", 1, 5))) in

-- MCore parsers ----------------------------------------

con TyDyn in
con TyProd : Dyn in
con TyUnit in

con TmLet : (Dyn, Dyn, Dyn) in
con TmLam : (Dyn, Dyn, Dyn) in
con TmIf  : (Dyn, Dyn, Dyn) in
con TmConDef : (Dyn, Dyn, Dyn) in
-- TmMatch : (Expr, String, String, Expr, Expr)
con TmMatch : (Dyn, Dyn, Dyn, Dyn, Dyn) in
con TmUtest : (Dyn, Dyn, Dyn) in

con TmApp : (Dyn, Dyn) in
con TmVar : Dyn in
con TmTuple : Dyn in
con TmProj : (Dyn, Dyn) in
con TmConst : (Dyn) in
con TmFix in
con TmSeq : Dyn in
con TmConFun : Dyn in

con CUnit in
con CInt : Dyn in
con CFloat : Dyn in
con CBool : Dyn in
con CChar : Dyn in

-- ty : Parser Type
let ty = fix (lam ty. lam env.
  let tuple =
    bind (parens (comma_sep ty)) (lam ts.
      if null ts
      then pure TyUnit
      else if eqi (length ts) 1
      then pure (head ts)
      else pure (TyProd ts))
  in
  let dyn = apr (reserved "Dyn") (pure TyDyn) in
  label "type"
  (alt tuple dyn) env
) in

utest test_parser ty "Dyn"
with Success(TyDyn, ("", ("", 1, 4))) in
utest test_parser (ty) "((), ((Dyn), Dyn)) rest"
with Success(TyProd[TyUnit,TyProd[TyDyn, TyDyn]], ("rest", ("", 1, 20))) in
utest show_error (test_parser ty "dyn")
with "Parse error at 1:1: Unexpected 'd'. Expected type" in
utest show_error (test_parser ty "(Dyn, dyn, Dyn)")
with "Parse error at 1:7: Unexpected 'd'. Expected type" in

-- atom : Parser Expr
--
-- Innermost expression parser.
let atom = fix (lam atom. lam expr. lam input.
  let var_access =
    let _ = debug "== Parsing var_access" in
    fmap TmVar identifier in
  let fix_ =
    let _ = debug "== Parsing fix ==" in
    apr (reserved "fix") (pure TmFix)
  in
  let seq =
    let _ = debug "== Parsing seq ==" in
    fmap TmSeq (brackets (comma_sep expr))
  in
  let tuple =
    let _ = debug "== Parsing tuple ==" in
    bind (parens (comma_sep expr)) (lam es.
    if null es
    then pure (TmConst CUnit)
    else if eqi (length es) 1
    then pure (head es)
    else pure (TmTuple es))
  in
  let num =
    let _ = debug "== Parsing num ==" in
    fmap (lam n. TmConst (CInt n)) number
  in
  let float =
    let _ = debug "== Parsing float ==" in
    fmap (lam f. TmConst (CFloat f)) float
  in
  let bool =
    let _ = debug "== Parsing bool ==" in
    alt (apr (reserved "true")  (pure (TmConst (CBool true))))
        (apr (reserved "false") (pure (TmConst (CBool false))))
  in
  let str_lit =
    let _ = debug "== Parsing string ==" in
    fmap TmSeq string_lit
  in
  let chr_lit =
    let _ = debug "== Parsing character ==" in
    fmap (lam c. TmConst (CChar c)) char_lit
  in
    label "atomic expression"
    (alt var_access
    (alt fix_
    (alt seq
    (alt tuple
    (alt (try float)
    (alt num
    (alt bool
    (alt str_lit char_lit)))))))) input
) in

-- left : Parser Expr
--
-- Left recursive expressions, i.e. function application
-- and tuple projection.
let left = lam expr.
  let atom_or_proj =
    bind (atom expr) (lam a.
    bind (many (apr (symbol ".") number)) (lam is.
    if null is
    then pure a
    else pure (foldl (curry TmProj) a is)))
  in
  bind (many1 atom_or_proj) (lam as.
  pure (foldl1 (curry TmApp) as))
in

-- expr: Parser Expr
--
-- Main expression parser.
let expr = fix (lam expr. lam env.
  let let_ =
    let _ = debug "== Parsing let ==" in
    bind (reserved "let") (lam _.
    bind identifier (lam x.
    bind (symbol "=") (lam _.
    bind expr (lam e.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmLet(x, e, body))))))))
  in
  let lam_ =
    let _ = debug "== Parsing lam ==" in
    bind (reserved "lam") (lam _.
    bind identifier (lam x.
    bind (optional (apr (symbol ":") ty)) (lam t.
    bind (symbol ".") (lam _.
    bind expr (lam e.
    pure (TmLam(x, t, e)))))))
  in
  let if_ =
    let _ = debug "== Parsing if ==" in
    bind (reserved "if") (lam _.
    bind expr (lam cnd.
    bind (reserved "then") (lam _.
    bind expr (lam thn.
    bind (reserved "else") (lam _.
    bind expr (lam els.
    pure (TmIf(cnd, thn, els))))))))
  in
  let match_ =
    let _ = debug "== Parsing match ==" in
    bind (reserved "match") (lam _.
    bind expr (lam e.
    bind (reserved "with") (lam _.
    bind identifier (lam k.
    bind (optional identifier) (lam x.
    bind (reserved "then") (lam _.
    bind expr (lam thn.
    bind (reserved "else") (lam _.
    bind expr (lam els.
    pure (TmMatch(e, k, x, thn, els)))))))))))
  in
  let con_ =
    let _ = debug "== Parsing con ==" in
    bind (reserved "con") (lam _.
    bind identifier (lam k.
    bind (optional (apr (symbol ":") ty)) (lam t.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmConDef(k, t, body)))))))
  in
  let utest_ =
    let _ = debug "== Parsing utest ==" in
    bind (reserved "utest") (lam _.
    bind expr (lam e1.
    bind (reserved "with") (lam _.
    bind expr (lam e2.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmUtest(e1, e2, body))))))))
  in
  label "expression"
  (alt (left expr)
  (alt let_
  (alt lam_
  (alt if_
  (alt match_
  (alt con_ utest_)))))) env
) in


utest test_parser (left expr) "f x"
with Success(TmApp(TmVar "f", TmVar "x"), ("", ("", 1, 4))) in
utest test_parser (left expr) "f x y"
with Success(TmApp(TmApp(TmVar "f", TmVar "x"), TmVar "y"), ("", ("", 1, 6))) in

utest test_parser expr "let f = lam x. x in f x"
with Success(TmLet("f", TmLam ("x", None, TmVar "x"),
             TmApp (TmVar "f", TmVar "x")), ("", ("", 1,24))) in

utest test_parser expr "let f = lam x : Dyn. x in f (x, y) z"
with Success(TmLet("f", TmLam ("x", Some TyDyn, TmVar "x"),
             TmApp (TmApp (TmVar "f", TmTuple [TmVar "x", TmVar "y"]), TmVar "z")),
             ("", ("", 1, 37))) in

utest test_parser expr "let f = lam x. x in f \"foo\""
with Success(TmLet("f", TmLam ("x", None, TmVar "x"),
             TmApp (TmVar "f", TmSeq "foo")), ("", ("", 1, 28))) in

utest test_parser expr "f t.0.1 u.0"
with Success(TmApp(TmApp(TmVar "f",
                         TmProj(TmProj(TmVar "t", 0), 1)),
                   TmProj(TmVar "u", 0)), ("", ("", 1, 12))) in

utest show_error(test_parser expr "let lam = 42 in lam")
with "Parse error at 1:5: Unexpected keyword 'lam'. Expected identifier" in

utest show_error(test_parser expr "let x = 42 in")
with "Parse error at 1:14: Unexpected end of input. Expected expression" in

utest show_error(test_parser expr "lam x : 42. x")
with "Parse error at 1:9: Unexpected '4'. Expected type" in

utest show_error(test_parser expr "let x = [1,2 in nth x 0")
with "Parse error at 1:14: Unexpected 'i'. Expected ']'" in

utest show_error(test_parser expr "(1, (2,3).1")
with "Parse error at 1:12: Unexpected end of input. Expected ')'" in

utest show_error(test_parser expr "")
with "Parse error at 1:1: Unexpected end of input. Expected expression" in

-- program : Parser Expr
let program = apl (apr ws expr) end_of_input in

utest show_error (test_parser program "f let x = 42 in x")
with "Parse error at 1:3: Unexpected 'l'. Expected end of input" in

if or (eqstr (nth argv 1) "test") (lti (length argv) 3) then
  ()
else
  let file = nth argv 2 in
  if fileExists file then
    let contents = readFile file in
    let res = run_parser file program contents in
    match res with Success t then
      print_ln "Parsing successful!"
    else
      print_ln (show_error res)
  else
    print_ln (concat "Unknown file: " file)