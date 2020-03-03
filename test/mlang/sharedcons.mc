-- Remembering constructors from individual language fragments

lang A
    syn Expr =
    | TmFoo ()
end

lang B
    syn Expr =
    | TmFoo ()
end

let isA = use A in lam x. match x with TmFoo () then true else false
let isB = use B in lam x. match x with TmFoo () then true else false

lang C
    syn Expr =
    | TmBar ()
end

lang AC = A + C

mexpr
let fooA = use A in (TmFoo ()) in
let fooA2 = use A in (TmFoo ()) in
let fooAC = use AC in (TmFoo ()) in

utest fooA2 with fooA in
utest fooAC with fooA in

let _ = 
  use A in
  utest isA (TmFoo ()) with true in
  utest isB (TmFoo ()) with false in
  ()
in

let _ = 
  use AC in
  utest isA (TmFoo ()) with true in
  utest isB (TmFoo ()) with false in
  ()
in

let _ = 
  use B in
  utest isA (TmFoo ()) with false in
  utest isB (TmFoo ()) with true in
  ()
in
()
