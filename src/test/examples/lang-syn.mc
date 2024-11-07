lang Pre
  syn Expr =
end
lang A = Pre
  syn Expr =
  | TmA {}
end

lang B = Pre
  syn Expr =
  | TmB {}
end

lang C = Pre
  syn Expr =
  | TmC {}
end

lang AB = A + B end
lang ABC = AB + C end

mexpr
use ABC in
()
