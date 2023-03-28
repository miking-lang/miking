lang A
  syn Expr =
  | TmA {}

  sem f =
  | TmA _ -> 1
end

lang B
  syn Expr =
  | TmB {}

  sem f =
  | TmB _ -> 2
end

lang C
  syn Expr =
  | TmC {}

  sem f =
  | TmC _ -> 3
end

lang AB = A + B
lang ABC = AB + C

mexpr
use ABC in
()
