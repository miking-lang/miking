lang L1
  syn D1 =
  | Foo Int

  sem run =
  | Foo n -> n
  | _ -> negi 1
end

lang L2
  syn D2 =
  | Foo Int
end

let run_l1 = lam d.
  use L1 in
  run d

let wrapped1 = use L1 in Foo 42
let wrapped2 = use L2 in Foo 42

mexpr

utest run_l1 wrapped1 with 42 in
utest run_l1 wrapped2 with negi 1 in
()