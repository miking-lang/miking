-- Remembering constructors from individual language fragments

lang ExprDef
  syn Expr =
end

lang A = ExprDef
    syn Expr =
    | TmFoo ()
end

lang B
    syn Expr =
    | TmFoo ()
end

let isA = use A in lam x. match x with TmFoo () then true else false
let isB = use B in lam x. match x with TmFoo () then true else false

lang C = ExprDef
    syn Expr =
    | TmBar ()
end

lang AC = A + C end

mexpr
let fooA = use A in (TmFoo ()) in
let fooA2 = use A in (TmFoo ()) in
let fooAC = use AC in (TmFoo ()) in

utest fooA2 with fooA in
utest fooAC with fooA in

use A in
  utest isA (TmFoo ()) with true in
  ();

use AC in
  utest isA (TmFoo ()) with true in
  ();


use B in
  utest isB (TmFoo ()) with true in
  ()
