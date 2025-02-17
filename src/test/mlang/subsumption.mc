lang A
  syn Expr =
  | Foo Int
  sem foo =
  | Foo 1 -> 1
end

lang B = A
  sem foo =
  | Foo 2 -> 2
end

lang AB = A + B
  sem bar =
  | _ -> 2
  sem foo =
  | Foo _ -> 42
end

lang AB2 = AB
end

lang AB2
end

lang CatchAll
  sem foo =
  | _ -> 42
end

lang Specific = CatchAll
  sem foo =
  | 3 -> 3
end

mexpr

utest use A in foo (Foo 1) with 1 in
utest use B in foo (Foo 1) with 1 in
utest use B in foo (Foo 2) with 2 in
utest use AB in foo (Foo 1) with 1 in
utest use AB in foo (Foo 3) with 42 in

let bar = lam x. x in
utest use A in bar 3 with 3 in
utest use AB in bar 3 with 2 in

utest use CatchAll in foo 3 with 42 in
utest use Specific in foo 3 with 3 in
utest use Specific in foo 4 with 42 in

()
