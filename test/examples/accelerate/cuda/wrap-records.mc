-- This file tests that wrapping of possibly nested records is supported. This
-- applies both to inputs (arguments) and outputs (return values).

include "common.mc" -- printLn
include "string.mc"

let addBoolToInt : {a : {c : Int, d : Float}, b : Bool} -> {c : Int, d : Float} =
  lam r.
  {c = addi r.a.c (if r.b then 1 else 0), d = r.a.d}

mexpr

let r = {a = {c = 4, d = 2.5}, b = false} in

let t : Int = accelerate (
  let t1 : {c : Int, d : Float} =
    { c = addi r.a.c (if r.b then 1 else 0)
    , d = r.a.d } in
  let t2 : Int = addi t1.c (floorfi t1.d) in
  t2
) in

printLn (int2string t)
