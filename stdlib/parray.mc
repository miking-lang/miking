
include "string.mc"

-- This file contains an implementation of pure arrays, a way to use random access in
-- arrays in a pure setting. The operations have low constant factor and a time complexity
-- of O(log n).

-- Pure Array
type PA a
con PAData  : all a. (Int,a,a,a,a,a,a,a,a,a,a) -> PA a
con PANode  : all a. (Int,Int,PA a,PA a,PA a,PA a,PA a,PA a,PA a,PA a,PA a,PA a) -> PA a
con PAEmpty : all a. () -> PA a
con PANext  : all a. (PA a) -> PA a

let empty = PAEmpty()

-- Helper function for prettyPA, for generating a pretty print string for
-- debugging
recursive
let workPrettyPA = lam ident. lam pa. lam f.
  match pa with PAData(i,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
   join ["\n", ident, "PAData(", int2string i,",",
           f x0, ",", f x1, ",", f x2, ",", f x3, ",",
           f x4, ",", f x5, ",", f x6, ",", f x7, ",",
           f x8, ",", f x9, ")"] else
  match pa with PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
   let g = lam pa. workPrettyPA (concat ident "  ") pa f in
   join ["\n", ident, "PANode(", int2string i, ",", int2string l, ",",
                    g x0, ",", g x1, ",", g x2, ",", g x3, ",",
                    g x4, ",", g x5, ",", g x6, ",", g x7, ",",
                    g x8, ",", g x9, ")"] else
  match pa with PAEmpty() then "E" else
  match pa with PANext(pa2) in workPrettyPA ident pa2 f
end

-- `prettyPA pa f` is a simple pretty printer, mostly for internal debugging,
-- where f : a -> String is a pretty printer for the element of the array.
-- The function returns a string.
let prettyPA = workPrettyPA ""

recursive
let workAddPA = lam pa. lam y. lam l.
  match pa with PAEmpty() then
    if leqi l 1
      then PAData(1,y,y,y,y,y,y,y,y,y,y)
      else PANode(0,l,workAddPA empty y (divi l 10),
           empty,empty,empty,empty,empty,empty,empty,empty,empty)
  else
  match pa with PAData(1,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(2,x0,y ,x2,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(2,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(3,x0,x1,y ,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(3,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(4,x0,x1,x2,y ,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(4,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(5,x0,x1,x2,x3,y ,x5,x6,x7,x8,x9) else
  match pa with PAData(5,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(6,x0,x1,x2,x3,x4,y ,x6,x7,x8,x9) else
  match pa with PAData(6,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(7,x0,x1,x2,x3,x4,x5,y ,x7,x8,x9) else
  match pa with PAData(7,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(8,x0,x1,x2,x3,x4,x5,x6,y ,x8,x9) else
  match pa with PAData(8,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,y ,x9) else
  match pa with PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
           if eqi l 0 then PANode(1,10,PAData(
                   10,x0,x1,x2,x3,x4,x5,x6,x7,x8,y),
                   empty,empty,empty,empty,empty,empty,empty,empty,empty)
           else
            PANext(PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,y)) else
  match pa with PANode(i,l2,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) in
    let e = (match i with 0 then x0 else match i with 1 then x1 else
             match i with 2 then x2 else match i with 3 then x3 else
             match i with 4 then x4 else match i with 5 then x5 else
             match i with 6 then x6 else match i with 7 then x7 else
             match i with 8 then x8 else x9) in
    let e2 = workAddPA e y (divi l2 10) in
    let setNode = lam e. lam i. lam i2.
      match i with 0 then PANode(i2,l2,e,x1,x2,x3,x4,x5,x6,x7,x8,x9) else
      match i with 1 then PANode(i2,l2,x0,e,x2,x3,x4,x5,x6,x7,x8,x9) else
      match i with 2 then PANode(i2,l2,x0,x1,e,x3,x4,x5,x6,x7,x8,x9) else
      match i with 3 then PANode(i2,l2,x0,x1,x2,e,x4,x5,x6,x7,x8,x9) else
      match i with 4 then PANode(i2,l2,x0,x1,x2,x3,e,x5,x6,x7,x8,x9) else
      match i with 5 then PANode(i2,l2,x0,x1,x2,x3,x4,e,x6,x7,x8,x9) else
      match i with 6 then PANode(i2,l2,x0,x1,x2,x3,x4,x5,e,x7,x8,x9) else
      match i with 7 then PANode(i2,l2,x0,x1,x2,x3,x4,x5,x6,e,x8,x9) else
      match i with 8 then PANode(i2,l2,x0,x1,x2,x3,x4,x5,x6,x7,e,x9) else
                          PANode(i2,l2,x0,x1,x2,x3,x4,x5,x6,x7,x8,e) in
    match e2 with PANext e3 then
      if eqi i 9 then
        if eqi l 0 then
            PANode(1, muli l2 10,setNode e3 i 10,
              empty,empty,empty,empty,empty,empty,empty,empty,empty)
          else PANext (setNode e3 i 10)
      else setNode e3 i (addi i 1)
    else setNode e2 i i
end



-- `addPA pa y` adds an element `y` to the end of the
-- pure array `pa` and returns a new pure array
-- Either keep track of the number of elements in your pure array in another
-- variable, or use `lengthPA` to get the current number of elements.
let addPA = lam pa. lam y.
  workAddPA pa y 0



/-
recursive
let addPA : all a. PA a -> a -> PA a = lam pa. lam y.
  match pa with PAEmpty()
           then PAData(1,y,y,y,y,y,y,y,y,y,y) else
  match pa with PAData(1,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(2,x0,y ,x2,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(2,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(3,x0,x1,y ,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(3,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(4,x0,x1,x2,y ,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(4,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(5,x0,x1,x2,x3,y ,x5,x6,x7,x8,x9) else
  match pa with PAData(5,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(6,x0,x1,x2,x3,x4,y ,x6,x7,x8,x9) else
  match pa with PAData(6,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(7,x0,x1,x2,x3,x4,x5,y ,x7,x8,x9) else
  match pa with PAData(7,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(8,x0,x1,x2,x3,x4,x5,x6,y ,x8,x9) else
  match pa with PAData(8,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,y ,x9) else
  match pa with PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,y) else
  match pa with PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(1,10,PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       PAEmpty(),PAEmpty(),PAEmpty(),PAEmpty(),PAEmpty(),
                       PAEmpty(),PAEmpty(),PAEmpty()) else
  match pa with PAData(1,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(2,x0,y ,x2,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(2,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(3,x0,x1,y ,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(3,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(4,x0,x1,x2,y ,x4,x5,x6,x7,x8,x9) else
  match pa with PAData(4,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(5,x0,x1,x2,x3,y ,x5,x6,x7,x8,x9) else
  match pa with PAData(5,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(6,x0,x1,x2,x3,x4,y ,x6,x7,x8,x9) else
  match pa with PAData(6,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(7,x0,x1,x2,x3,x4,x5,y ,x7,x8,x9) else
  match pa with PAData(7,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(8,x0,x1,x2,x3,x4,x5,x6,y ,x8,x9) else
  match pa with PAData(8,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,y ,x9) else
  match pa with PAData(9,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,y) else
  match pa with PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(1,10,PAData(10,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9),
  match pa with PANode(1,l,x0,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(2,l,x0,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x3,x4,x5,x6,x7,x8,x9) else
  match pa with PANode(2,l,x0,x1,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x3,x4,x5,x6,x7,x8,x9)
           then PANode(3,l,x0,x1,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x4,x5,x6,x7,x8,x9) else
  match pa with PANode(3,l,x0,x1,x2,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x4,x5,x6,x7,x8,x9)
           then PANode(4,l,x0,x1,x2,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x5,x6,x7,x8,x9) else
  match pa with PANode(4,l,x0,x1,x2,x3,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x5,x6,x7,x8,x9)
           then PANode(5,l,x0,x1,x2,x3,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x6,x7,x8,x9) else
  match pa with PANode(5,l,x0,x1,x2,x3,x4,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x6,x7,x8,x9)
           then PANode(6,l,x0,x1,x2,x3,x4,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x7,x8,x9) else
  match pa with PANode(6,l,x0,x1,x2,x3,x4,x5,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x7,x8,x9)
           then PANode(7,l,x0,x1,x2,x3,x4,x5,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x8,x9) else
  match pa with PANode(7,l,x0,x1,x2,x3,x4,x5,x6,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x8,x9)
           then PANode(8,l,x0,x1,x2,x3,x4,x5,x6,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y),
                       x9) else
  match pa with PANode(8,l,x0,x1,x2,x3,x4,x5,x6,x7,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       x9)
           then PANode(9,l,x0,x1,x2,x3,x4,x5,x6,x7,
                       PAData(10,z0,z1,z2,z3,z4,z5,z6,z7,z8,z9),
                       PAData(1,y,y,y,y,y,y,y,y,y,y)
                       ) else
  match pa with PANode(1,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(1,l,x0,addPA x1 y,x2,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PANode(2,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(2,l,x0,x1,addPA x2 y,x3,x4,x5,x6,x7,x8,x9) else
  match pa with PANode(3,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(3,l,x0,x1,x2,addPA x3 y,x4,x5,x6,x7,x8,x9) else
  match pa with PANode(4,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(4,l,x0,x1,x2,x3,addPA x4 y,x5,x6,x7,x8,x9) else
  match pa with PANode(5,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(5,l,x0,x1,x2,x3,x4,addPA x5 y,x6,x7,x8,x9) else
  match pa with PANode(6,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(6,l,x0,x1,x2,x3,x4,x5,addPA x6 y,x7,x8,x9) else
  match pa with PANode(7,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(7,l,x0,x1,x2,x3,x4,x5,x6,addPA x7 y,x8,x9) else
  match pa with PANode(8,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           then PANode(8,l,x0,x1,x2,x3,x4,x5,x6,x7,addPA x8 y,x9) else
  match pa with PANode(9,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9)
           in PANode(9,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,addPA x9 y)
end
-/

-- `getPA pa n` returns the element at position `n` from `pa`.
-- The complexity of the function is O(log n) with a low constant factor
recursive
let getPA = lam pa. lam n.
  match pa with PANode(_,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    let n2 = modi n l in
    let i = divi n l in
    (match i with 0 then getPA x0 n2 else
     match i with 1 then getPA x1 n2 else
     match i with 2 then getPA x2 n2 else
     match i with 3 then getPA x3 n2 else
     match i with 4 then getPA x4 n2 else
     match i with 5 then getPA x5 n2 else
     match i with 6 then getPA x6 n2 else
     match i with 7 then getPA x7 n2 else
     match i with 8 then getPA x8 n2 else
     match i with 9 in   getPA x9 n2)
     else
  match pa with PAData(_,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) in
    (match n with 0 then x0 else
     match n with 1 then x1 else
     match n with 2 then x2 else
     match n with 3 then x3 else
     match n with 4 then x4 else
     match n with 5 then x5 else
     match n with 6 then x6 else
     match n with 7 then x7 else
     match n with 8 then x8 else
     match n with 9 in   x9)
end

-- `setPA pa n y` sets value (random access) `y` at index `n` using `pa`. Note that
-- the input `pa` is not affected. The updated pure array is the result value.
-- The complexity of the function is O(log n) with a low constant factor
recursive
let setPA = lam pa. lam n. lam y.
  match pa with PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    let n2 = modi n l in
    let i2 = divi n l in
    (match i2 with 0 then PANode(i,l,setPA x0 n2 y,x1,x2,x3,x4,x5,x6,x7,x8,x9) else
     match i2 with 1 then PANode(i,l,x0,setPA x1 n2 y,x2,x3,x4,x5,x6,x7,x8,x9) else
     match i2 with 2 then PANode(i,l,x0,x1,setPA x2 n2 y,x3,x4,x5,x6,x7,x8,x9) else
     match i2 with 3 then PANode(i,l,x0,x1,x2,setPA x3 n2 y,x4,x5,x6,x7,x8,x9) else
     match i2 with 4 then PANode(i,l,x0,x1,x2,x3,setPA x4 n2 y,x5,x6,x7,x8,x9) else
     match i2 with 5 then PANode(i,l,x0,x1,x2,x3,x4,setPA x5 n2 y,x6,x7,x8,x9) else
     match i2 with 6 then PANode(i,l,x0,x1,x2,x3,x4,x5,setPA x6 n2 y,x7,x8,x9) else
     match i2 with 7 then PANode(i,l,x0,x1,x2,x3,x4,x5,x6,setPA x7 n2 y,x8,x9) else
     match i2 with 8 then PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,setPA x8 n2 y,x9) else
     match i2 with 9 in   PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,setPA x9 n2 y))
     else
  match pa with PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    (match n with 0 then PAData(k,y,x1,x2,x3,x4,x5,x6,x7,x8,x9) else
     match n with 1 then PAData(k,x0,y,x2,x3,x4,x5,x6,x7,x8,x9) else
     match n with 2 then PAData(k,x0,x1,y,x3,x4,x5,x6,x7,x8,x9) else
     match n with 3 then PAData(k,x0,x1,x2,y,x4,x5,x6,x7,x8,x9) else
     match n with 4 then PAData(k,x0,x1,x2,x3,y,x5,x6,x7,x8,x9) else
     match n with 5 then PAData(k,x0,x1,x2,x3,x4,y,x6,x7,x8,x9) else
     match n with 6 then PAData(k,x0,x1,x2,x3,x4,x5,y,x7,x8,x9) else
     match n with 7 then PAData(k,x0,x1,x2,x3,x4,x5,x6,y,x8,x9) else
     match n with 8 then PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,y,x9) else
     match n with 9 in   PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,x8,y))
  else pa
end


-- Helper for `makePA`
recursive
let workMakePA = lam k. lam n. lam f. lam acc.
  if eqi k n then acc
  else workMakePA (addi k 1) n f (addPA acc (f k))
end

-- `makePA n f` creates a pure array of size `n`, where each element is
-- initalized by calling function `f k`, where `k` is the index for the element
let makePA = lam n. lam f.
  workMakePA 0 n f empty

-- `lengthPA pa` returns an integer giving the length of the pure array `pa`.
recursive
let lengthPA = lam pa.
  match pa with PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    addi (muli i l)
      (match i with 1 then lengthPA x1 else
       match i with 2 then lengthPA x2 else
       match i with 3 then lengthPA x3 else
       match i with 4 then lengthPA x4 else
       match i with 5 then lengthPA x5 else
       match i with 6 then lengthPA x6 else
       match i with 7 then lengthPA x7 else
       match i with 8 then lengthPA x8 else
       match i with 9 in   lengthPA x9)
    else
  match pa with PAData(i,_,_,_,_,_,_,_,_,_,_) then i
  else 0
end

-- helper for `pa2seq`
recursive
let workPA2seq = lam pa. lam n. lam acc.
  if lti n 0 then acc
  else workPA2seq pa (subi n 1) (cons (getPA pa n) acc)
end

-- `pa2seq pa` converts a pure array to a sequences.
let pa2seq = lam pa.
  workPA2seq pa (subi (lengthPA pa) 1) []

-- ==== utests =====

utest prettyPA (makePA 12 (lam x.x)) int2string with
"
PANode(1,10,
  PAData(10,0,1,2,3,4,5,6,7,8,9),
  PAData(2,10,11,10,10,10,10,10,10,10,10),E,E,E,E,E,E,E,E)"

utest lengthPA (makePA 0 (lam. 0)) with 0
utest lengthPA (makePA 8 (lam. 0)) with 8
utest lengthPA (makePA 12 (lam. 0)) with 12

utest pa2seq (makePA 5 (lam x. muli x 2)) with [0,2,4,6,8]
utest pa2seq (makePA 12 (lam x.x)) with [0,1,2,3,4,5,6,7,8,9,10,11]

-- One large test, including all functions
let testlen = 1320
let setlist = [(2,23),(3,77),(4,22),(4,220),(4,891),(4,1317),(4,999)]
utest
  let pa = makePA testlen (lam x.x) in
  let pav =
      foldl (lam acc. lam x. match x with (i,v) in setPA acc i v) pa setlist in
  (lengthPA pav, pa2seq pav)
with
  let ls = createList testlen (lam x.x) in
  let ls2 =
    foldl (lam acc. lam x. match x with (i,v) in set acc i v) ls setlist in
  (testlen, ls2)
