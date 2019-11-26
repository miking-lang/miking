include "mexpr.mc"
include "parser.mc"

mexpr

-- TODO: Re-implementing parts MCore parser. Needs top-level use to
-- have parser use the same datatypes...
use MExpr in

-- MCore tokens ----------------------------------

-- line_comment : Parser ()
--
-- Parse a line comment, ignoring its contents.
let line_comment =
  void (apr (apr (alt (lex_string "--") (lex_string "//"))
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
let string = lam s. token (lex_string s) in

-- symbol : String -> Parser String
let symbol = string in

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

-- float : Parser Float
let float = token lex_float in

-- parens : Parser a -> Parser a
let parens = wrapped_in (symbol "(") (symbol ")") in

-- brackets : Parser a -> Parser a
let brackets = wrapped_in (symbol "[") (symbol "]") in

-- char_lit : Parser Char
let char_lit = token lex_char_lit in

-- string_lit : Parser String
let string_lit = token lex_string_lit in

-- comma_sep : Parser a -> Parser [a]
let comma_sep = sep_by (symbol ",") in

-- List of reserved keywords
let keywords =
  ["let", "in", "if", "then", "else", "true", "false", "match", "with", "con", "lam", "utest", "recursive"]
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

-- MCore parsers ----------------------------------------

type Type in

con TyDyn : Type in
con TyProd : [Type] -> Type in
con TyUnit : Type in

-- type Const
con CFloat : Float -> Const in
con CChar : Char -> Const in

-- ty : Parser Type
recursive
  let ty = lam st.
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
    (alt tuple dyn) st
in

recursive
  -- atom : Parser Expr
  --
  -- Innermost expression parser.
  let atom = lam input.
    let var_access =
      let _ = debug "== Parsing var_access" in
      fmap TmVar identifier in
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
      (alt seq
      (alt tuple
      (alt (try float)
      (alt num
      (alt bool
      (alt str_lit char_lit))))))) input

  -- expr: Parser Expr
  --
  -- Main expression parser.
  let expr = lam st.
    -- left : Parser Expr
    --
    -- Left recursive expressions, i.e. function application
    -- and tuple projection.
    let left =
      let atom_or_proj =
        bind atom (lam a.
        bind (many (apr (symbol ".") number)) (lam is.
        if null is
        then pure a
        else pure (foldl (curry TmProj) a is)))
      in
      bind (many1 atom_or_proj) (lam as.
      pure (foldl1 (curry TmApp) as))
    in
    let letbinding =
      let _ = debug "== Parsing letbinding ==" in
      bind (reserved "let") (lam _.
      bind identifier (lam x.
      bind (symbol "=") (lam _.
      bind expr (lam e.
      pure (x, e)))))
    in
    let reclets =
      let _ = debug "== Parsing recursive lets ==" in
      bind (reserved "recursive") (lam _.
      bind (many1 letbinding) (lam bindings.
      bind (reserved "in") (lam _.
      bind expr (lam body.
      pure (TmRecLets(bindings, body))))))
    in
    let let_ =
      let _ = debug "== Parsing let ==" in
      bind letbinding (lam binding.
      bind (reserved "in") (lam _.
      bind expr (lam body.
      pure (TmLet(binding.0, binding.1, body)))))
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
    (alt left
    (alt reclets
    (alt let_
    (alt lam_
    (alt if_
    (alt match_
    (alt con_ utest_))))))) st
in

-- program : Parser Expr
let program = apl (apr ws (apr (reserved "mexpr") expr)) end_of_input in

-- TODO: Define remaining built-ins
let builtins =
    [("not", TmConst CNot)
    ,("and", TmConst CAnd)
    ,("or", TmConst COr)
    ,("addi", TmConst CAddi)
    ,("eqi", TmConst CEqi)
] in

if or (eqstr (nth argv 1) "test") (lti (length argv) 3) then
  ()
else
  let file = nth argv 2 in
  if fileExists file then
    let contents = readFile file in
    let res = run_parser file program contents in
    match res with Success t then
      let _ = print_ln "Parsing successful!" in
      let p = t.0 in
      eval builtins p
    else
      print_ln (show_error res)
  else
    print_ln (concat "Unknown file: " file)
