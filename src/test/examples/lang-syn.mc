lang A
  syn Expr =
  | TmA {}
end

lang B
  syn Expr =
  | TmB {}
end

lang C
  syn Expr =
  | TmC {}
end

lang AB = A + B
lang ABC = AB + C

mexpr
use ABC in
()
