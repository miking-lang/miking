include "bool.mc"

type Pos = { x: Int, y: Int }

let pos0 = { x = 0, y = 0 }

let getPos : Int -> Int -> Pos = lam x. lam y. { x = x, y = y }

-- Equality
let eqPos : Pos -> Pos -> Bool =
  lam p1. lam p2.
    and (eqi p1.y p2.y) (eqi p1.x p2.x)

-- Strictly less-than (earlier in text)
let ltPos : Pos -> Pos -> Bool =
  lam p1. lam p2.
    if lti p1.y p2.y then
      true
    else if eqi p1.y p2.y then
      lti p1.x p2.x
    else
      false

-- Strictly greater-than (further in text)
let gtPos : Pos -> Pos -> Bool =
  lam p1. lam p2.
    ltPos p2 p1

-- Less-than or equal
let lePos : Pos -> Pos -> Bool =
  lam p1. lam p2.
    or (ltPos p1 p2) (eqPos p1 p2)

-- Greater-than or equal
let gePos : Pos -> Pos -> Bool =
  lam p1. lam p2.
    or (gtPos p1 p2) (eqPos p1 p2)
