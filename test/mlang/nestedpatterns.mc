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
utest use RecordsWithNegation in foo {red = true} with 2 in
utest use RecordsWithNegation in foo {blue = false} with 3 in

()
