/-
  This library implements runtime reflection functions, use with caution.
 -/

-- is the value a float?
external isfloat : Float -> Bool

utest isfloat 0. with true
utest isfloat (unsafeCoerce 1) with false
