-- Example showing how the scope of an accelerate term may have a big impact on
-- the performance gains.

include "common.mc" -- printLn

let timeFunction = lam f : Unit -> Unit.
  let t1 = wallTimeMs () in
  f ();
  let t2 = wallTimeMs () in
  printLn (float2string (divf (subf t2 t1) 1000.0))

mexpr

let s : [Int] = create 10 (lam i. i) in

-- Accelerate the function that is then applied on each element.
print "Accelerating each function call: ";
timeFunction
  (lam.
    let f1 : Int -> Int = lam x. accelerate (addi x 1) in
    let s1 : [Int] = map f1 s in
    ());

-- As each accelerate call has a non-negligible overhead, it is often more
-- efficient to accelerate the entire map term.
print "Accelerating the map term      : ";
timeFunction
  (lam.
    let f2 : Int -> Int = lam x. addi x 1 in
    let s2 : [Int] = accelerate ((let m : (Int -> Int) -> [Int] -> [Int] = map in m) f2 s) in
    ())
