lang A
  syn Expr =
  | TmA {}

  sem f =
  | TmA _ -> 1
end

let f1 = lam x.
  use A in
  f (TmA {})

let f2 = lam x.
  use A in
  f (TmA {})

mexpr
()
