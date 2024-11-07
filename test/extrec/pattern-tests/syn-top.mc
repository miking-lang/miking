lang SomeLang
  syn Foo =
  | TmBar {x : Int, y : Int}

  sem f =
  | TmBar {x = x} -> addi x 1
end

mexpr
use SomeLang in
utest f (TmBar {x = 22}) with 23 in
()