let x = gensym ()
let y = gensym ()

mexpr
utest eqs x x with true in
utest eqs y y with true in
utest eqs y x with false in
utest eqs x y with false in
()
