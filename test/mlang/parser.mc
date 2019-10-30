-- Auxiliary stuff
let curry = lam f. lam x. lam y. f(x, y) in
let head = lam seq. nth seq 0 in
let tail = lam seq. slice seq 1 (length seq) in
let null = lam seq. eqi 0 (length seq) in
let any  = fix (lam any. lam p. lam seq.
  if eqi (length seq) 0
  then false
  else or (p (head seq)) (any p (tail seq))
) in
let foldl = fix (lam foldl. lam f. lam acc. lam l.
  if eqi (length l) 0
  then acc
  else foldl f (f acc (head l)) (tail l)
) in
let foldl1 = lam f. lam l. foldl f (head l) (tail l) in

let eqchar = lam c1. lam c2. eqi (char2int c1) (char2int c2) in
let eqstr = fix (lam eqstr. lam s1. lam s2.
    if neqi (length s1) (length s2)
    then false
    else if null s1
         then true
         else if eqchar (head s1) (head s2)
         then eqstr (tail s1) (tail s2)
         else false
) in
let show_char = lam c. concat "'" (concat [c] "'") in

let string2int = fix (lam string2int. lam s.
  let len = length s in
  let last = subi len 1 in
  if eqi len 0
  then 0
  else
    let lsd = subi (char2int (nth s last)) (char2int '0') in
    let rest = muli 10 (string2int (slice s 0 last)) in
    addi rest lsd
) in

utest string2int "5" with 5 in
utest string2int "25" with 25 in
utest string2int "314159" with 314159 in

-- TODO: It would be nicer with escape codes in chars!
let is_whitespace = lam c.
  or (or (eqchar c ' ') (eqchar c (head "\n"))) (eqchar c (head "\t"))
in

utest is_whitespace ' ' with true in
utest is_whitespace '	' with true in
utest is_whitespace '
' with true in
utest is_whitespace 'a' with false in

let is_alpha = lam c.
  or (and (leqi (char2int 'A') (char2int c)) (leqi (char2int c) (char2int 'Z')))
     (and (leqi (char2int 'a') (char2int c)) (leqi (char2int c) (char2int 'z')))
in

utest is_alpha 'a' with true in
utest is_alpha 'm' with true in
utest is_alpha 'z' with true in
utest is_alpha '`' with false in
utest is_alpha '{' with false in
utest is_alpha 'A' with true in
utest is_alpha 'M' with true in
utest is_alpha 'Z' with true in
utest is_alpha '@' with false in
utest is_alpha '[' with false in

let is_digit = lam c.
  and (leqi (char2int '0') (char2int c)) (leqi (char2int c) (char2int '9'))
in

utest is_digit '0' with true in
utest is_digit '5' with true in
utest is_digit '9' with true in
utest is_digit '/' with false in
utest is_digit ':' with false in

let is_alphanum = lam c.
  or (is_alpha c) (is_digit c)
in

utest is_alphanum '0' with true in
utest is_alphanum '9' with true in
utest is_alphanum 'A' with true in
utest is_alphanum 'z' with true in
utest is_alphanum '_' with false in

let is_valid_char = lam c.
  or (is_alphanum c) (eqchar c '_')
in

utest is_valid_char '0' with true in
utest is_valid_char '9' with true in
utest is_valid_char 'A' with true in
utest is_valid_char 'z' with true in
utest is_valid_char '_' with true in


-- The Parser monad -----------------------------
-- TODO: Track position
con Success : (Dyn, Dyn) in -- Success : (a, String) -> ParseResult a
con Failure : (Dyn, Dyn, Dyn) in -- Failure : (String, String, String) -> ParseResult a
-- Success stores result of parsing and rest of input
-- Failure stores found and expected token, and rest of input

-- type Parser a = String -> ParseResult a

-- fail : String -> String -> Parser a
--
-- Fail parsing with custom info
let fail = lam found. lam expected. lam input.
  Failure (found, expected, input)
in

-- show_error : ParseResult a -> String
--
-- Show human readable error message from failed parse.
-- Fails if argument is not a failure.
let show_error = lam f.
  match f with Failure t then
    let found = t.0 in
    let expected = t.1 in
    concat (concat "Unexpected " found)
           (if gti (length expected) 0
            then concat ". Expected " expected
            else "")
  else error "Tried to show something that is not a failure"
in

-- fmap : (a -> b) -> Parser a -> Parser b
let fmap = lam f. lam p. lam input.
  let res = p input in
  match res with Success t then
    let v = t.0 in
    let rest = t.1 in
    Success (f v, rest)
  else res
in

-- pure : a -> Parser a
let pure = lam v. lam input. Success(v, input) in

-- ap : Parser (a -> b) -> Parser a -> Parser b
let ap = lam pf. lam p. lam input.
  let res1 = pf input in
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
let apl = lam p1. lam p2. lam input.
  let res1 = p1 input in
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
let apr = lam p1. lam p2. lam input.
  let res1 = p1 input in
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
let bind = lam p. lam f. lam input.
  let res = p input in
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
let when = lam b. lam p. lam input.
  if b then void p else pure ()
in

-- Core ------------------------------------------------

-- next : Parser char
--
-- Read next character from input stream
let next = lam input.
  if null input
  then fail "end of input" "" input
  else pure (head input) (tail input)
in

utest next "abc" with Success ('a', "bc") in
utest show_error (next "") with "Unexpected end of input" in

utest
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2])) "abc"
with Success ("ab", "c") in

utest
  show_error (
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2])) "a"
  )
with "Unexpected end of input" in

let end_of_input = lam input.
  if null input
  then pure ((), input)
  else fail (show_char (head input)) "end of input" input
in

-- alt : Parser a -> Parser a -> Parser a
--
-- `alt p1 p2` tries to parse `p1`, but falls back
-- to `p2` if `p1` fails without consuming any input.
let alt = lam p1. lam p2. lam input.
  let res1 = p1 input in
  match res1 with Failure t1 then
    let input2 = t1.2 in
    if eqi (length input) (length input2) then
      let res2 = p2 input in
      match res2 with Failure t2 then
        let input3 = t2.2 in
        if eqi (length input2) (length input3) then
          let exp = concat (concat t1.1 " or ") t2.1 in
          Failure (t2.0, exp, input3)
        else res2 -- p2 consumed input, don't merge expected
      else res2 -- Propagate Success
    else res1 -- p1 consumed input, don't backtrack
  else res1 -- Propagate Success
in

-- not_followed_by : Parser a -> Parser ()
--
-- `not_followed_by p` succeeds (without consuming input)
-- only if `p` does not succeed.
let not_followed_by = lam p. lam input.
  let res1 = p input in
  match res1 with Failure _ then
    pure () input
  else
    let res2 = next input in
    match res2 with Success t then
      let c = t.0 in
      fail (show_char c) "" input
    else res2
in

-- satisfy : (Char -> Bool) -> String -> Parser Char
--
-- `satisfy cnd exp` succeeds with the next character
-- if `cnd` returns true for that character. `exp` is
-- the expected token.
let satisfy = lam cnd. lam expected. lam input.
  bind next (lam c.
  if cnd c
  then pure c
  else lam _. fail (show_char c) expected input) input
in

-- try : Parser a -> Parser a
--
-- `try p` is used for backtracking. It parses `p`, but
-- fails without consuming input if `p` fails.
let try = lam p. lam input.
  let res = p input in
  match res with Failure t then
    Failure (t.0, t.1, input)
  else -- Propagate Success
    res
in

-- label : String -> Parser p -> Parser p
--
-- `label l p` parses `p` but changes the "expected" token
-- to `l` if `p` fails. Typical use is for big chains of
-- `alt`, e.g., `label "expression" (alt (alt let_ lam_) ...)`
let label = lam l. lam p. lam input.
  let res = p input in
  match res with Failure t then
  if eqi (length t.2) (length input)
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

utest lex_char 'a' "ab" with Success ('a', "b") in
utest show_error (lex_char 'b' "ab") with "Unexpected 'a'. Expected 'b'" in

utest
  bind (lex_char 'a') (lam c1.
  bind (lex_char 'b') (lam c2.
  pure [c1, c2])) "abc"
with Success ("ab", "c") in

utest show_error (
  bind (lex_char 'b') (lam c1.
  bind (lex_char 'b') (lam c2.
  pure [c1, c2])) "abc")
with "Unexpected 'a'. Expected 'b'" in

utest show_error (
  bind (lex_char 'a') (lam c1.
  bind (lex_char 'a') (lam c2.
  pure [c1, c2])) "abc")
with "Unexpected 'b'. Expected 'a'" in

utest alt (lex_char 'a') (lex_char 'b') "abc" with Success('a', "bc") in
utest alt (lex_char 'b') (lex_char 'a') "abc" with Success('a', "bc") in
utest show_error (
  alt (lex_char 'b') (lex_char 'c') "abc")
with "Unexpected 'a'. Expected 'b' or 'c'" in

utest not_followed_by (lex_char 'b') "abc" with Success((), "abc") in
utest show_error (not_followed_by (lex_char 'a') "abc")
with "Unexpected 'a'" in

utest many (lex_char 'a') "abc" with Success("a", "bc") in
utest many (lex_char 'a') "aaabc" with Success("aaa", "bc") in
utest many (lex_char 'a') "bc" with Success("", "bc") in

utest many1 (lex_char 'a') "abc" with Success("a", "bc") in
utest many1 (lex_char 'a') "aaabc" with Success("aaa", "bc") in
utest show_error (many1 (lex_char 'a') "bc") with "Unexpected 'b'. Expected 'a'" in

-- lex_number : Parser Int
--
-- Parse a natural number.
let lex_number = fmap string2int (many1 (satisfy is_digit "digit")) in

utest lex_number "123abc" with Success(123, "abc") in
utest show_error (lex_number "abc") with "Unexpected 'a'. Expected digit" in

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

utest lex_string "abc" "abcdef" with Success("abc", "def") in
utest lex_string "abcdef" "abcdef" with Success("abcdef", "") in
utest show_error (lex_string "abc" "def")
with "Unexpected 'd'. Expected 'abc'" in

utest
  bind (lex_string "ab") (lam s1.
  bind (lex_string "cd") (lam s2.
  pure (concat s1 s2))) "abcde"
with Success ("abcd", "e") in

-- Parser Char
--
-- Parse a character literal.
let lex_char_lit = wrapped_in (lex_string "'") (lex_string "'") next in

-- Parser String
--
-- Parse a string literal.
let lex_string_lit =
  wrapped_in (lex_string "\"") (lex_string "\"")
             (many (satisfy (lam c. not (eqstr [c] "\"")) ""))
in

-- spaces : Parser ()
--
-- Parse zero or more whitespace characters.
let spaces = void (many (satisfy is_whitespace "whitespace")) in

-- spaces1 : Parser ()
--
-- Parse one or more whitespace characters.
let spaces1 = void (many1 (satisfy is_whitespace "whitespace")) in

utest spaces "   abc" with Success ((), "abc") in
utest spaces "	  abc" with Success ((), "abc") in
utest spaces1 "	  abc" with Success ((), "abc") in
utest spaces "abc" with Success ((), "abc") in
utest show_error (spaces1 "abc") with "Unexpected 'a'. Expected whitespace" in

-- line_comment : Parser ()
--
-- Parse a line comment, ignoring its contents.
-- TODO: This should not be in the library!
let line_comment =
  void (apr (apr (alt (lex_string "--") (lex_string "//"))
                 (many (satisfy (lam c. not (eqstr "\n" [c])) "")))
            (lex_string "\n"))
in

utest line_comment "-- this is a comment
this is not" with Success((),"this is not") in

-- ws : Parser ()
--
-- Parse whitespace or comments.
let ws = void (many (alt line_comment spaces1)) in

utest ws "   -- this is a comment
--
    foo" with Success((), "foo") in

-- Parsers ----------------------------------

-- token : Parser a -> Parser a
--
-- `token p` parses `p` and any trailing whitespace
-- or comments.
-- TODO: Comment parser should be a parameter!
let token = lam p. apl p ws in

-- string : String -> Parser String
let string = lam s. token (lex_string s) in

utest string "ab" "abc" with Success("ab", "c") in
utest string "abc" "abc def" with Success("abc", "def") in
utest
  many (alt (string "ab") (string "cd")) "ab cd ef"
with Success(["ab", "cd"], "ef") in

-- symbol : String -> Parser String
let symbol = string in

utest symbol "(" "(abc)" with Success("(", "abc)") in
utest symbol "(" "(  abc)" with Success("(", "abc)") in

-- reserved : String -> Parser String
--
-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved = lam s.
  void (token (apl (lex_string s) (not_followed_by (satisfy is_valid_char "")))) in

utest reserved "lam" "lam x. x" with Success((), "x. x") in
utest show_error (reserved "lam" "lambda") with "Unexpected 'b'" in
utest show_error (reserved "lam" "la")
with "Unexpected end of input. Expected 'lam'" in

-- number : Parser Int
let number = token lex_number in

-- parens : Parser a -> Parser a
let parens = wrapped_in (symbol "(") (symbol ")") in

-- brackets : Parser a -> Parser a
let brackets = wrapped_in (symbol "[") (symbol "]") in

utest parens (lex_string "abc") "(abc)" with Success("abc","") in
utest brackets (many (string "abc")) "[abc abc]"
with Success(["abc", "abc"], "") in
utest show_error (parens (lex_string "abc") "(abc")
with "Unexpected end of input. Expected ')'" in

-- char_lit : Parser Char
let char_lit = token lex_char_lit in

utest char_lit "'a'" with Success('a', "") in
utest char_lit "'a' bc" with Success('a', "bc") in

-- string_lit : Parser String
let string_lit = token lex_string_lit in

utest string_lit "\"foobar\"" with Success("foobar", "") in
utest string_lit "\"\" rest" with Success("", "rest") in

-- comma_sep : Parser a -> Parser [a]
let comma_sep = sep_by (symbol ",") in

utest comma_sep (string "a") "a, a, a" with Success(["a", "a", "a"],"") in
utest comma_sep (string "a") "a" with Success(["a"],"") in
utest show_error (comma_sep (string "a") "a ,a,b")
with "Unexpected 'b'. Expected 'a'" in
utest brackets (comma_sep number) "[ 1 , 2, 3]" with Success([1,2,3], "") in

-- identifier : Parser String
--
-- Parse a valid identifier.
-- TODO: Should not be in library
let identifier =
  bind (satisfy (lam c. or (is_alpha c) (eqchar '_' c)) "valid identifier") (lam c.
  bind (token (many (satisfy is_valid_char ""))) (lam cs.
  pure (cons c cs)))
in

utest identifier "foo" with Success("foo", "") in

-- MCore parser ----------------------------------------

-- List of reserved keywords
let keywords =
  ["let", "in", "if", "then", "else", "match", "with", "con", "lam", "fix", "utest"]
in

con TyDyn in
con TyProd : Dyn in
con TyUnit in

con TmLet : (Dyn, Dyn, Dyn) in
con TmLam : (Dyn, Dyn, Dyn) in
con TmIf  : (Dyn, Dyn, Dyn) in
con TmConDef : (Dyn, Dyn) in
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
con CBool : Dyn in
con CChar : Dyn in

-- ident : Parser String
--
-- Parse an identifier, but require that it is not in the list
-- of reserved keywords.
let ident =
  try (
    bind identifier (lam x.
    if any (eqstr x) keywords
    then fail (concat (concat "keyword '" x) "'") "identifier"
    else pure x)
  )
in

-- ty : Parser Type
let ty = fix (lam ty. lam input.
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
  (alt tuple dyn) input
) in

utest ty "Dyn" with Success(TyDyn, "") in
utest ty "((), ((Dyn), Dyn)) rest"
with Success(TyProd[TyUnit,TyProd[TyDyn, TyDyn]], "rest") in
utest show_error (ty "dyn") with "Unexpected 'd'. Expected type" in
utest show_error (ty "(Dyn, dyn, Dyn)") with "Unexpected 'd'. Expected type" in

-- atom : Parser Expr
--
-- Innermost expression parser.
-- TODO: Other constants? Floats are annoying since there is no
--       primitive string2float function!
let atom = fix (lam atom. lam expr. lam input.
  let var_access = fmap TmVar ident in
  let fix_ = apr (reserved "fix") (pure TmFix) in
  let seq = fmap TmSeq (brackets (comma_sep expr)) in
  let tuple =
    bind (parens (comma_sep expr)) (lam es.
    if null es
    then pure (TmConst CUnit)
    else if eqi (length es) 1
    then pure (head es)
    else pure (TmTuple es))
  in
  let num = fmap (lam n. TmConst (CInt n)) number in
  let bool = alt (apr (reserved "true")  (pure (TmConst (CBool true))))
                 (apr (reserved "false") (pure (TmConst (CBool false))))
  in
  let str_lit = fmap TmSeq string_lit in
  let chr_lit = fmap (lam c. TmConst (CChar c)) char_lit in
    label "atomic expression"
    (alt fix_
    (alt seq
    (alt tuple
    (alt num
    (alt bool
    (alt char_lit
    (alt str_lit var_access))))))) input
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
let expr = fix (lam expr. lam input.
  let let_ =
    bind (reserved "let") (lam _.
    bind ident (lam x.
    bind (symbol "=") (lam _.
    bind expr (lam e.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmLet(x, e, body))))))))
  in
  let lam_ =
    bind (reserved "lam") (lam _.
    bind ident (lam x.
    bind (optional (apr (symbol ":") ty)) (lam t.
    bind (symbol ".") (lam _.
    bind expr (lam e.
    pure (TmLam(x, t, e)))))))
  in
  let if_ =
    bind (reserved "if") (lam _.
    bind expr (lam cnd.
    bind (reserved "then") (lam _.
    bind expr (lam thn.
    bind (reserved "else") (lam _.
    bind expr (lam els.
    pure (TmIf(cnd, thn, els))))))))
  in
  let match_ =
    bind (reserved "match") (lam _.
    bind expr (lam e.
    bind (reserved "with") (lam _.
    bind ident (lam k.
    bind (optional ident) (lam x.
    bind (reserved "then") (lam _.
    bind expr (lam thn.
    bind (reserved "else") (lam _.
    bind expr (lam els.
    pure (TmMatch(e, k, x, thn, els)))))))))))
  in
  let con_ =
    bind (reserved "con") (lam _.
    bind ident (lam k.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmConDef(k, body))))))
  in
  let utest_ =
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
  (alt con_ utest_)))))) input
) in

utest (left expr) "f x"
with Success (TmApp(TmVar "f", TmVar "x"), "") in
utest (left expr) "f x y"
with Success (TmApp(TmApp(TmVar "f", TmVar "x"), TmVar "y"), "") in

utest expr "let f = lam x. x in f x"
with Success(TmLet("f", TmLam ("x", None, TmVar "x"),
             TmApp (TmVar "f", TmVar "x")), "") in

utest expr "let f = lam x : Dyn. x in f (x, y) z"
with Success(TmLet("f", TmLam ("x", Some TyDyn, TmVar "x"),
             TmApp (TmApp (TmVar "f", TmTuple [TmVar "x", TmVar "y"]), TmVar "z")), "") in

utest expr "let f = lam x. x in f \"foo\""
with Success(TmLet("f", TmLam ("x", None, TmVar "x"),
             TmApp (TmVar "f", TmSeq "foo")), "") in

utest expr "f t.0.1 u.0"
with Success(TmApp(TmApp(TmVar "f",
                         TmProj(TmProj(TmVar "t", 0), 1)),
                   TmProj(TmVar "u", 0)),"") in

utest show_error(expr "let lam = 42 in lam")
with "Unexpected keyword 'lam'. Expected identifier" in

utest show_error(expr "let x = 42 in")
with "Unexpected end of input. Expected expression" in

utest show_error(expr "lam x : 42. x")
with "Unexpected '4'. Expected type" in

utest show_error(expr "let x = [1,2 in nth x 0")
with "Unexpected 'i'. Expected ']'" in

utest show_error(expr "(1, (2,3).1")
with "Unexpected end of input. Expected ')'" in

utest show_error(expr "")
with "Unexpected end of input. Expected expression" in

-- program : Parser Expr
let program = apl (apr ws expr) end_of_input in

utest show_error (program "f let x = 42 in x")
with "Unexpected 'l'. Expected end of input" in

()
