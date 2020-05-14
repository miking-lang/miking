-- lang SameBroken
--   sem foo =
--   | (true, _) -> true
--   | (_, true) -> false
-- end

-- lang BrokenA
--   sem foo =
--   | (true, _) -> true
-- end
-- lang BrokenB
--   sem foo =
--   | (_, true) -> false
-- end
-- lang CombinedBroken = BrokenA + BrokenB

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
()
