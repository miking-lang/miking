include "parser.mc"

-- MCore tokens ----------------------------------

-- line_comment : Parser ()
--
-- Parse a line comment, ignoring its contents.
let line_comment =
  void (apr (apr (alt (lex_string "--") (lex_string "//"))
                 (many (satisfy (lam c. not (eqstr "\n" [c])) "")))
            (alt (lex_string "\n") end_of_input))

-- ws : Parser ()
--
-- Parse whitespace or comments.
let ws = void (many (alt line_comment spaces1))

-- token : Parser a -> Parser a
--
-- `token p` parses `p` and any trailing whitespace or comments.
let token = lex_token ws

-- string : String -> Parser String
let string = lam s. token (lex_string s)

-- symbol : String -> Parser String
let symbol = string

let is_valid_char = lam c.
  or (is_alphanum c) (eqchar c '_')

-- reserved : String -> Parser String
--
-- Parse a specific string and fail if it is followed by
-- additional valid identifier characters.
let reserved = lam s.
  void (token (apl (lex_string s) (not_followed_by (satisfy is_valid_char ""))))

-- number : Parser Int
let number = token lex_number

-- float : Parser Float
let float = token lex_float

-- parens : Parser a -> Parser a
let parens = wrapped_in (symbol "(") (symbol ")")

-- brackets : Parser a -> Parser a
let brackets = wrapped_in (symbol "[") (symbol "]")

-- char_lit : Parser Char
let char_lit = token lex_char_lit

-- string_lit : Parser String
let string_lit = token lex_string_lit

-- comma_sep : Parser a -> Parser [a]
let comma_sep = sep_by (symbol ",")

-- List of reserved keywords
let keywords =
  ["let", "in", "if", "then", "else", "match", "with", "con", "lam", "fix", "utest"]

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

-- MCore parsers ----------------------------------------

type Type

con TyDyn : Type
con TyProd : [Type] -> Type
con TyUnit : Type

type Const
con CUnit : Const
con CInt : Int -> Const
con CFloat : Float -> Const
con CBool : Bool -> Const
con CChar : Char -> Const

type MExpr

con TmLet : (String, MExpr, MExpr) -> MExpr
con TmLam : (String, Option, MExpr) -> MExpr
con TmIf  : (MExpr, MExpr, MExpr) -> MExpr
con TmConDef : (String, Option, Dyn) -> MExpr
con TmMatch : (MExpr, String, String, MExpr, MExpr) -> MExpr
con TmUtest : (MExpr, MExpr, MExpr) -> MExpr

con TmApp : (MExpr, MExpr) -> MExpr
con TmVar : String -> MExpr
con TmTuple : [MExpr] -> MExpr
con TmProj : (MExpr, Int) -> MExpr
con TmConst : Const -> MExpr
con TmFix : MExpr
con TmSeq : [MExpr] -> MExpr
con TmConFun : String -> MExpr

-- ty : Parser Type
let ty = fix (lam ty. lam st.
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
  (alt tuple dyn) st)

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
    (alt str_lit char_lit)))))))) input)

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

-- expr: Parser Expr
--
-- Main expression parser.
let expr = fix (lam expr. lam st.
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
  (alt con_ utest_)))))) st)

-- program : Parser Expr
let program = apl (apr ws expr) end_of_input

main

-- MCore token tests

utest test_parser line_comment "-- this is a comment
this is not"
with Success((), ("this is not", ("",2,1))) in

utest test_parser ws "   -- this is a comment
--
    foo" with Success((), ("foo", ("", 3, 5))) in

utest test_parser (string "ab") "abc"
with Success("ab", ("c", ("", 1, 3))) in
utest test_parser (string "abc") "abc def"
with Success("abc", ("def", ("", 1, 5))) in
utest test_parser (many (alt (string "ab") (string "cd"))) "ab cd ef"
with Success(["ab", "cd"], ("ef", ("", 1, 7))) in

utest test_parser (symbol "(") "(abc)"
with Success("(", ("abc)", ("", 1, 2))) in
utest test_parser (symbol "(") "(  abc)"
with Success("(", ("abc)", ("", 1, 4))) in

utest is_valid_char '0' with true in
utest is_valid_char '9' with true in
utest is_valid_char 'A' with true in
utest is_valid_char 'z' with true in
utest is_valid_char '_' with true in

utest test_parser (reserved "lam") "lam x. x"
with Success((), ("x. x", ("", 1, 5))) in
utest show_error (test_parser (reserved "lam") "lambda")
with "Parse error at 1:4: Unexpected 'b'" in
utest show_error (test_parser (reserved "fix") "fix_")
with "Parse error at 1:4: Unexpected '_'" in
utest show_error (test_parser (reserved "lam") "la")
with "Parse error at 1:1: Unexpected end of input. Expected 'lam'" in

utest test_parser (parens (lex_string "abc")) "(abc)"
with Success("abc", ("", ("", 1, 6))) in
utest test_parser (brackets (many (string "abc"))) "[abc abc]"
with Success(["abc", "abc"], ("", ("", 1, 10))) in
utest show_error (test_parser (parens (lex_string "abc")) "(abc")
with "Parse error at 1:5: Unexpected end of input. Expected ')'" in

utest test_parser (char_lit) "'a'"
with Success('a', ("", ("", 1,4))) in
utest test_parser (char_lit) "'a' bc"
with Success('a', ("bc", ("", 1,5))) in

utest test_parser (string_lit) "\"foobar\""
with Success("foobar", ("", ("", 1,9))) in
utest test_parser (string_lit) "\"\" rest"
with Success("", ("rest", ("", 1,4))) in

utest test_parser (comma_sep (string "a")) "a, a, a"
with Success(["a", "a", "a"],("", ("", 1,8))) in
utest test_parser (comma_sep (string "a")) "a"
with Success(["a"],("", ("", 1,2))) in
utest show_error (test_parser (comma_sep (string "a")) "a ,a,b")
with "Parse error at 1:6: Unexpected 'b'. Expected 'a'" in
utest test_parser (brackets (comma_sep number)) "[ 1 , 2, 3]"
with Success([1,2,3], ("", ("", 1, 12))) in

utest test_parser identifier "foo" with Success("foo", ("", ("", 1, 4))) in
utest test_parser identifier "fix_" with Success("fix_", ("", ("", 1, 5))) in

-- MCore parser tests

utest test_parser ty "Dyn"
with Success(TyDyn, ("", ("", 1, 4))) in
utest test_parser (ty) "((), ((Dyn), Dyn)) rest"
with Success(TyProd[TyUnit,TyProd[TyDyn, TyDyn]], ("rest", ("", 1, 20))) in
utest show_error (test_parser ty "dyn")
with "Parse error at 1:1: Unexpected 'd'. Expected type" in
utest show_error (test_parser ty "(Dyn, dyn, Dyn)")
with "Parse error at 1:7: Unexpected 'd'. Expected type" in

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

utest show_error (test_parser program "f let x = 42 in x")
with "Parse error at 1:3: Unexpected 'l'. Expected end of input" in

-- Main logic

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