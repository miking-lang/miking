lang Pre
  syn Expr =
  sem f =
end

lang A = Pre
  syn Expr =
  | TmA {}

  sem f =
  | TmA _ -> 1
end

lang B = Pre
  syn Expr =
  | TmB {}

  sem f =
  | TmB _ -> 2
end

lang C = Pre
  syn Expr =
  | TmC {}

  sem f =
  | TmC _ -> 3
end

lang AB = A + B end
lang ABC = AB + C end

mexpr
use ABC in
()
