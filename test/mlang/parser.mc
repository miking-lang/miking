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
con Success : (Dyn, Dyn) in -- Success : (a, String) -> ParseResult e a
con Failure : Dyn in        -- Failure : e -> ParseResult e a

let fail = lam msg. lam input.
  Failure msg
in

let fmap = lam f. lam p. lam input.
  let res = p input in
  match res with Success t then
    let v = t.0 in
    let rest = t.1 in
    Success (f v, rest)
  else res
in

-- TODO: Error reporting is based on second parser
-- TODO: MegaParsec does not explore alternatives if first
--       parser consumes any input
-- alt : M a -> M a -> M a
let alt = lam p1. lam p2. lam input.
  let res = p1 input in
  match res with Failure _
  then p2 input
  else res -- Propagate Success or EOF
in

-- pure : a -> M a
let pure = lam v. lam input. Success(v, input) in

-- ap : M (a -> b) -> M a -> M b
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

-- bind : M a -> (a -> M b) -> M b
let bind = lam p. lam f. lam input.
  let res = p input in
  match res with Success t then
    let x = t.0 in
    let rest = t.1 in
    f x rest
  else -- propagate Failure
    res
in

let void = apl (pure ()) in

-- when : bool -> M a -> M ()
let when = lam b. lam m. lam input.
  if b then void m else pure ()
in

-- Core ------------------------------------------------
let next = lam input.
  if null input
  then Failure "Unexpected end of input"
  else pure (head input) (tail input)
in

utest next "abc" with Success ('a', "bc") in
utest next "" with Failure "Unexpected end of input" in

utest
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2])) "abc"
with Success ("ab", "c") in

utest
  bind next (lam c1.
  bind next (lam c2.
  pure [c1, c2])) "a"
with Failure "Unexpected end of input" in

let not_followed_by = lam p. lam input.
  let res1 = p input in
  match res1 with Failure _ then
    pure () input
  else
    let res2 = next input in
    match res2 with Success t then
      let c = t.0 in
      Failure (concat "Unexpected " (show_char c))
    else res2
in

-- TODO: Add expected argument
let satisfy = lam cnd. lam expected.
  bind next (lam c.
  if cnd c
  then pure c
  else
    let msg =
      if eqi (length expected) 0
      then concat "Unexpected " (show_char c)
      else concat (concat "Unexpected " (show_char c))
                  (concat ". Expected " expected)
    in
    fail msg)
in

-- Combinators ---------------------------------
let many = fix (lam many. lam p.
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  if null hd
  then pure []
  else bind (many p) (lam tl. pure (concat hd tl)))
) in

let many1 = lam p.
  bind p (lam hd.
  bind (many p) (lam tl.
  pure (cons hd tl)))
in

-- Lexers ---------------------------------------------
let lex_char = lam c. satisfy (eqchar c) (show_char c) in

utest lex_char 'a' "ab" with Success ('a', "b") in
utest lex_char 'b' "ab" with Failure "Unexpected 'a'. Expected 'b'" in

utest
  bind (lex_char 'a') (lam c1.
  bind (lex_char 'b') (lam c2.
  pure [c1, c2])) "abc"
with Success ("ab", "c") in

utest
  bind (lex_char 'b') (lam c1.
  bind (lex_char 'b') (lam c2.
  pure [c1, c2])) "abc"
with Failure "Unexpected 'a'. Expected 'b'" in

utest
  bind (lex_char 'a') (lam c1.
  bind (lex_char 'a') (lam c2.
  pure [c1, c2])) "abc"
with Failure "Unexpected 'b'. Expected 'a'" in

utest alt (lex_char 'a') (lex_char 'b') "abc" with Success('a', "bc") in
utest alt (lex_char 'b') (lex_char 'a') "abc" with Success('a', "bc") in
utest alt (lex_char 'b') (lex_char 'c') "abc"
with Failure "Unexpected 'a'. Expected 'c'" in

utest not_followed_by (lex_char 'b') "abc" with Success((), "abc") in
utest not_followed_by (lex_char 'a') "abc"
with Failure "Unexpected 'a'" in

utest many (lex_char 'a') "abc" with Success("a", "bc") in
utest many (lex_char 'a') "aaabc" with Success("aaa", "bc") in
utest many (lex_char 'a') "bc" with Success("", "bc") in

utest many1 (lex_char 'a') "abc" with Success("a", "bc") in
utest many1 (lex_char 'a') "aaabc" with Success("aaa", "bc") in
utest many1 (lex_char 'a') "bc" with Failure "Unexpected 'b'. Expected 'a'" in

let lex_number = fmap string2int (many1 (satisfy is_digit "digit")) in

utest lex_number "123abc" with Success(123, "abc") in
utest lex_number "abc" with Failure "Unexpected 'a'. Expected digit" in

let lex_string = fix (lam lex_string. lam s.
  if null s
  then pure ""
  else
    let c = head s in
    let cs = tail s in
    bind (lex_char c) (lam _.
    bind (lex_string cs) (lam _.
    pure (cons c cs)))
) in

utest lex_string "abc" "abcdef" with Success("abc", "def") in
utest lex_string "abcdef" "abcdef" with Success("abcdef", "") in
utest lex_string "abc" "def" with Failure "Unexpected 'd'. Expected 'a'" in

utest
  bind (lex_string "ab") (lam s1.
  bind (lex_string "cd") (lam s2.
  pure (concat s1 s2))) "abcde"
with Success ("abcd", "e") in

let spaces = void (many (satisfy is_whitespace "whitespace")) in
let spaces1 = void (many1 (satisfy is_whitespace "whitespace")) in

utest spaces "   abc" with Success ((), "abc") in
utest spaces "	  abc" with Success ((), "abc") in
utest spaces1 "	  abc" with Success ((), "abc") in
utest spaces "abc" with Success ((), "abc") in
utest spaces1 "abc" with Failure "Unexpected 'a'. Expected whitespace" in

let line_comment =
  void (apr (apr (alt (lex_string "--") (lex_string "//"))
                 (many (satisfy (lam c. not (eqstr "\n" [c])) "")))
            (lex_string "\n"))
in

utest line_comment "-- this is a comment
this is not" with Success((),"this is not") in

let ws = void (many (alt line_comment spaces1)) in

utest ws "   -- this is a comment
--
    foo" with Success((), "foo") in
-- Parsers ----------------------------------

let token = lam p. apl p ws in
let string = lam s. token (lex_string s) in

utest string "ab" "abc" with Success("ab", "c") in
utest string "abc" "abc def" with Success("abc", "def") in
utest
  many (alt (string "ab") (string "cd")) "ab cd ef"
with Success(["ab", "cd"], "ef") in

let symbol = string in

utest symbol "(" "(abc)" with Success("(", "abc)") in
utest symbol "(" "(  abc)" with Success("(", "abc)") in

let reserved = lam s.
  void (token (apl (lex_string s) (not_followed_by (satisfy is_valid_char "")))) in

utest reserved "lam" "lam x. x" with Success((), "x. x") in
utest reserved "lam" "lambda" with Failure "Unexpected 'b'" in
utest reserved "lam" "la" with Failure "Unexpected end of input" in

let number = token lex_number in

let wrapped_in = lam pl. lam pr. lam p.
  apr pl (apl p pr)
in

let parens = wrapped_in (symbol "(") (symbol ")") in
let brackets = wrapped_in (symbol "[") (symbol "]") in

utest parens (lex_string "abc") "(abc)" with Success("abc","") in
utest brackets (many (string "abc")) "[abc abc]" with Success(["abc", "abc"], "") in
utest parens (lex_string "abc") "(abc" with Failure "Unexpected end of input" in

let lex_string_lit =
  wrapped_in (lex_string "\"") (lex_string "\"")
             (many (satisfy (lam c. not (eqstr [c] "\"")) ""))
in
let string_lit = token lex_string_lit in

utest string_lit "\"foobar\"" with Success("foobar", "") in
utest string_lit "\"\" rest" with Success("", "rest") in

let lex_char_lit = wrapped_in (lex_string "'") (lex_string "'") next in
let char_lit = token lex_char_lit in

utest char_lit "'a'" with Success('a', "") in
utest char_lit "'a' bc" with Success('a', "bc") in

let sep_by = lam sep. lam p.
  let inner = fix (lam inner.
    bind (apr sep p) (lam hd.
    bind (alt inner (pure [])) (lam tl.
    pure (cons hd tl)))
  ) in
  bind (alt (bind p (lam v. pure [v])) (pure [])) (lam hd.
  bind (alt inner (pure [])) (lam tl.
  pure (concat hd tl)))
in

let comma_sep = sep_by (symbol ",") in

utest comma_sep (string "a") "a, a, a" with Success(["a", "a", "a"],"") in
utest comma_sep (string "a") "a" with Success(["a"],"") in
utest comma_sep (string "a") "a ,a,b" with Success(["a", "a"],",b") in
utest brackets (comma_sep number) "[ 1 , 2, 3]" with Success([1,2,3], "") in

let identifier =
  bind (satisfy (lam c. or (is_alpha c) (eqchar '_' c)) "valid identifier") (lam c.
  bind (token (many (satisfy is_valid_char ""))) (lam cs.
  pure (cons c cs)))
in

utest identifier "foo" with Success("foo", "") in

-- TODO: left-recursive stuff?

-- MCore parser ----------------------------------------
let keywords =
  ["let", "in", "if", "then", "else", "match", "with", "con", "lam", "fix", "utest"]
in

con TmLet : (Dyn, Dyn, Dyn) in
con TmLam : (Dyn, Dyn) in
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

let ident =
  bind identifier (lam x.
  if any (eqstr x) keywords
  then fail (concat (concat "Cannot use keyword '" x) "' as identifier")
  else pure x)
in

-- TODO: Other constants?
let atom = fix (lam atom. lam expr. lam input.
  let var_access = fmap TmVar ident in
  let fix_ = apr (reserved "fix") (pure TmFix) in
  let seq = fmap TmSeq (brackets (comma_sep expr)) in
  let tuple =
    bind (parens (comma_sep expr)) (lam es.
    if eqi (length es) 0
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
    alt var_access
    (alt fix_
    (alt seq
    (alt tuple
    (alt num
    (alt bool
    (alt char_lit str_lit)))))) input
) in

let left = lam expr.
  let atom_or_proj =
    bind (atom expr) (lam a.
    bind (many (apr (symbol ".") number)) (lam is.
    if eqi (length is) 0
    then pure a
    else pure (foldl (curry TmProj) a is)))
  in
  bind (many1 atom_or_proj) (lam as.
  pure (foldl1 (curry TmApp) as))
in

-- TODO: Type annotations
let expr = fix (lam expr. lam input.
  let let_ =
    bind (reserved "let") (lam _.
    bind identifier (lam x.
    bind (symbol "=") (lam _.
    bind expr (lam e.
    bind (reserved "in") (lam _.
    bind expr (lam body.
    pure (TmLet(x, e, body))))))))
  in
  let lam_ =
    bind (reserved "lam") (lam _.
    bind identifier (lam x.
    bind (symbol ".") (lam _.
    bind expr (lam e.
    pure (TmLam(x, e))))))
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
    bind identifier (lam k.
    bind identifier (lam x.
    bind (reserved "then") (lam _.
    bind expr (lam thn.
    bind (reserved "else") (lam _.
    bind expr (lam els.
    pure (TmMatch(e, k, x, thn, els)))))))))))
  in
  let con_ =
    bind (reserved "con") (lam _.
    bind identifier (lam k.
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
  -----------
  alt (left expr)
  (alt let_
  (alt lam_
  (alt if_
  (alt match_
  (alt con_ utest_))))) input
) in

utest (left expr) "f x"
with Success (TmApp(TmVar "f", TmVar "x"), "") in
utest (left expr) "f x y"
with Success (TmApp(TmApp(TmVar "f", TmVar "x"), TmVar "y"), "") in

utest expr "let f = lam x. x in f x"
with Success(TmLet("f", TmLam ("x", TmVar "x"),
             TmApp (TmVar "f", TmVar "x")), "") in

utest expr "let f = lam x. x in f (x, y) z"
with Success(TmLet("f", TmLam ("x", TmVar "x"),
             TmApp (TmApp (TmVar "f", TmTuple [TmVar "x", TmVar "y"]), TmVar "z")), "") in

utest expr "let f = lam x. x in f \"foo\""
with Success(TmLet("f", TmLam ("x", TmVar "x"),
             TmApp (TmVar "f", TmSeq "foo")), "") in

utest expr "f t.0.1 u.0" with Success(TmApp(TmApp(TmVar "f", TmProj(TmProj(TmVar "t", 0), 1)), TmProj(TmVar "u", 0)),"") in

let program = apr ws expr in

()