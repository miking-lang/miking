include "option.mc"

-- The commented out fragments are part of things that should produce error messages,
-- but we don't have a way to assert breakage yet

-- lang SameBroken
--   sem foo =
--   | (true, _) -> true
--   | (_, true) -> false
-- end

lang OkA
  sem foo =
  | (true, _) -> true
end
lang OkB
  sem foo =
  | (_, true) -> false
end
-- lang CombinedBroken = OkA + OkB

lang CatchAll
  sem foo =
  | _ -> "catchall"
end
lang MidSpecific = CatchAll
  sem foo =
  | (true, _) -> "mid"
end
lang FullSpecific = MidSpecific
  sem foo =
  | (true, true) -> "spec"
end

lang OrderIndependentA
  sem foo =
  | _ -> "catchall"
  | (true, _) -> "mid"
  | (true, true) -> "spec"
end
lang OrderIndependentB
  sem foo =
  | (true, _) -> "mid"
  | _ -> "catchall"
  | (true, true) -> "spec"
end

-- lang SemanticsOverSyntax
--   sem foo =
--   | {red = true} & {blue = true} -> true
--   | {red = true, blue = true} -> false
-- end

-- We probably want these sorts of patterns to give a warning or something, at least later
lang EmptyPatterns
  sem foo =
  | !_ -> true
end
lang EmptyPatterns
  sem foo =
  | true & false -> false
end

-- lang RecordsWithNegationAmbiguous
--   sem foo =
--   | {red = _} -> 1
--   | !{blue = _} -> 2
--   | !{blue = true} -> 3
-- end
lang RecordsWithNegation
  sem foo =
  | !{blue = _} -> 2
  | !{blue = true} -> 3
  | {blue = true} -> 4
end

lang LexBase
  syn Tok =
  sem lex =
  | [] -> Some []
  | str -> None ()
end

lang LexDecimal = LexBase
  syn Tok =
  | IntTok [Char]

  sem lex =
  | (['0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'] ++ _) & str ->
    match lex_int "" str with (n, rest) then
      optionMap (cons (IntTok n)) (lex rest)
    else never

  sem lex_int (prev_digits : [Char]) =
  | [('0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9') & digit] ++ rest ->
    lex_int (snoc prev_digits digit) rest
  | rest ->
    (prev_digits, rest)
end

lang LexSpace = LexBase
  sem lex =
  | " " ++ rest -> lex rest
end

lang LexBinary = LexBase
  syn Tok =
  | BinaryIntTok [Char]  -- NOTE(?,?): this should probably reuse IntTok and do conversion, but that's not relevant for this test

  sem lex =
  | (['0', 'b', '0' | '1'] ++ _) & ([_, _] ++ str) ->
    match lex_binary "" str with (n, rest) then
      optionMap (cons (BinaryIntTok n)) (lex rest)
    else never

  sem lex_binary (prev_digits : [Char]) =
  | [('0' | '1') & digit] ++ rest ->
    lex_binary (snoc prev_digits digit) rest
  | rest ->
    (prev_digits, rest)
end

lang Lexer = LexSpace + LexBinary + LexDecimal end

-- lang Broken
--   sem foo =
--   | "a" ++ _ -> true
--   | _ ++ "a" -> false
-- end

-- lang Broken
--   sem foo =
--   | [_] -> true
--   | "a" ++ _ -> false
-- end

-- lang Broken
--   sem foo =
--   | [!'a'] ++ _ -> true
--   | _ ++ [!'b'] -> false
-- end

mexpr

utest use CatchAll in foo (true, true) with "catchall" in
utest use MidSpecific in foo (true, true) with "mid" in
utest use MidSpecific in foo (true, false) with "mid" in
utest use MidSpecific in foo (false, false) with "catchall" in
utest use FullSpecific in foo (true, true) with "spec" in
utest use FullSpecific in foo (true, false) with "mid" in
utest use FullSpecific in foo (false, false) with "catchall" in

utest use OrderIndependentA in foo (true, true) with use OrderIndependentB in foo (true, true) in
utest use OrderIndependentA in foo (false, false) with use OrderIndependentB in foo (false, false) in
utest use OrderIndependentA in foo (true, false) with use OrderIndependentB in foo (true, false) in
utest use OrderIndependentA in foo (false, true) with use OrderIndependentB in foo (false, true) in

utest use RecordsWithNegation in foo {blue = true} with 4 in
utest use RecordsWithNegation in foo {blue = false} with 3 in

use Lexer in
  utest lex "" with Some [] in
  utest lex "0" with Some [IntTok "0"] in
  utest lex "0109" with Some [IntTok "0109"] in
  utest lex "0109 32" with Some [IntTok "0109", IntTok "32"] in
  utest lex "0b10 0109 32" with Some [BinaryIntTok "10", IntTok "0109", IntTok "32"] in
  utest lex "0b 10" with None () in
  utest lex "  32 " with Some [IntTok "32"] in
  ()
