-- This program should parse to the following
--
-- external foo! : (Float) -> ((Float) -> (Float))
-- in
-- external boo! : Int
-- in
-- let c =
--   foo
--     1.0e-0
--     2.0e+0
-- in
-- let d =
--   boo
-- in
-- {}


external foo! : Float -> Float -> Float

external boo! : Int

external boo2! : Int

external bar : Int


let a = foo

let b = foo 1.0

let c = foo 1.0 2.0

let d = boo

let e = bar
