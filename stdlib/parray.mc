
include "string.mc"

-- This file contains an implementation of pure arrays, a way to use
-- random access in arrays in a pure setting. The operations have low
-- constant factor and a time complexity of O(log n).
-- The main functions are (see specific documentation below):
--   emptyPA   An empty pure array
--   makePA    Creates a pure array of a given size, O(n log n)
--   addPA     Increases the size of the array by 1, O(log n)
--   setPA     Set an element in an array, O(log n)
--   getPA     Get an element from an array, O(log n)
--   lengthPA  Get the length of an array, O(log n)
--   seq2pa    Converts a sequence to a pure array O(n log n)
--   pa2seq    Converts a pure array to a sequence, O(n log n)
--   prettyPA  Returns a pretty printed string of the internal structure
--             of a pure array (for debugging purpose)

-- Pure Array
type PA a
con PAData  : all a. (Int,a,a,a,a,a,a,a,a,a,a) -> PA a
con PANode  : all a. (Int,Int,PA a,PA a,PA a,PA a,PA a,
                      PA a,PA a,PA a,PA a,PA a) -> PA a
con PAEmpty : all a. () -> PA a
con PANext  : all a. (PA a) -> PA a

let emptyPA = PAEmpty()

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
      else PANode(0,l,workAddPA emptyPA y (divi l 10),
           emptyPA,emptyPA,emptyPA,emptyPA,emptyPA,emptyPA,
           emptyPA,emptyPA,emptyPA)
  else
  match pa with PAData t then
    switch t.0
    case 1 then PAData{t with #label"0" = 2, #label"2" = y}
    case 2 then PAData{t with #label"0" = 3, #label"3" = y}
    case 3 then PAData{t with #label"0" = 4, #label"4" = y}
    case 4 then PAData{t with #label"0" = 5, #label"5" = y}
    case 5 then PAData{t with #label"0" = 6, #label"6" = y}
    case 6 then PAData{t with #label"0" = 7, #label"7" = y}
    case 7 then PAData{t with #label"0" = 8, #label"8" = y}
    case 8 then PAData{t with #label"0" = 9, #label"9" = y}
    case _ then
           if eqi l 0 then PANode(1,10,
             PAData{t with #label"0" = 10, #label"10" = y},
                   emptyPA,emptyPA,emptyPA,emptyPA,emptyPA,
                   emptyPA,emptyPA,emptyPA,emptyPA)
           else
            PANext(PAData{t with #label"0" = 10, #label"10" = y})
    end
  else
  match pa with PANode(i,l2,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    let e = switch i
            case 0 then x0 case 1 then x1 case 2 then x2
            case 3 then x3 case 4 then x4 case 5 then x5
            case 6 then x6 case 7 then x7 case 8 then x8 case _ then x9 end in
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
              emptyPA,emptyPA,emptyPA,emptyPA,emptyPA,emptyPA,
              emptyPA,emptyPA,emptyPA)
          else PANext (setNode e3 i 10)
      else setNode e3 i (addi i 1)
    else setNode e2 i i
  else error "Cannot happen"
end



-- `addPA pa y` adds an element `y` to the end of the
-- pure array `pa` and returns a new pure array
-- Either you should keep track of the number of elements of your pure array
-- in another  variable, or use `lengthPA` to get the current number
-- of elements.
let addPA = lam pa. lam y.
  workAddPA pa y 0


-- `getPA pa n` returns the element at position `n` from `pa`.
-- The complexity of the function is O(log n) with a low constant factor
recursive
let getPA = lam pa. lam n.
  match pa with PANode(_,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    let n2 = modi n l in
    let i = divi n l in
    (switch i case 0 then getPA x0 n2 case 1 then getPA x1 n2
              case 2 then getPA x2 n2 case 3 then getPA x3 n2
              case 4 then getPA x4 n2 case 5 then getPA x5 n2
              case 6 then getPA x6 n2 case 7 then getPA x7 n2
              case 8 then getPA x8 n2 case _ then getPA x9 n2 end)
     else
  match pa with PAData(_,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    (switch n case 0 then x0 case 1 then x1 case 2 then x2
              case 3 then x3 case 4 then x4 case 5 then x5
              case 6 then x6 case 7 then x7 case 8 then x8 case _ then x9 end)
  else error "Should not happen"
end

-- `setPA pa n y` sets value (random access) `y` at index `n` using `pa`. Note that
-- the input `pa` is not affected. The updated pure array is the result value.
-- The complexity of the function is O(log n) with a low constant factor
recursive
let setPA = lam pa. lam n. lam y.
  match pa with PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    let n2 = modi n l in
    let i2 = divi n l in
    (switch i2
     case 0 then PANode(i,l,setPA x0 n2 y,x1,x2,x3,x4,x5,x6,x7,x8,x9)
     case 1 then PANode(i,l,x0,setPA x1 n2 y,x2,x3,x4,x5,x6,x7,x8,x9)
     case 2 then PANode(i,l,x0,x1,setPA x2 n2 y,x3,x4,x5,x6,x7,x8,x9)
     case 3 then PANode(i,l,x0,x1,x2,setPA x3 n2 y,x4,x5,x6,x7,x8,x9)
     case 4 then PANode(i,l,x0,x1,x2,x3,setPA x4 n2 y,x5,x6,x7,x8,x9)
     case 5 then PANode(i,l,x0,x1,x2,x3,x4,setPA x5 n2 y,x6,x7,x8,x9)
     case 6 then PANode(i,l,x0,x1,x2,x3,x4,x5,setPA x6 n2 y,x7,x8,x9)
     case 7 then PANode(i,l,x0,x1,x2,x3,x4,x5,x6,setPA x7 n2 y,x8,x9)
     case 8 then PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,setPA x8 n2 y,x9)
     case _ then PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,setPA x9 n2 y) end)
     else
  match pa with PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    (switch n
     case 0 then PAData(k,y,x1,x2,x3,x4,x5,x6,x7,x8,x9)
     case 1 then PAData(k,x0,y,x2,x3,x4,x5,x6,x7,x8,x9)
     case 2 then PAData(k,x0,x1,y,x3,x4,x5,x6,x7,x8,x9)
     case 3 then PAData(k,x0,x1,x2,y,x4,x5,x6,x7,x8,x9)
     case 4 then PAData(k,x0,x1,x2,x3,y,x5,x6,x7,x8,x9)
     case 5 then PAData(k,x0,x1,x2,x3,x4,y,x6,x7,x8,x9)
     case 6 then PAData(k,x0,x1,x2,x3,x4,x5,y,x7,x8,x9)
     case 7 then PAData(k,x0,x1,x2,x3,x4,x5,x6,y,x8,x9)
     case 8 then PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,y,x9)
     case _ then PAData(k,x0,x1,x2,x3,x4,x5,x6,x7,x8,y) end)
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
  workMakePA 0 n f emptyPA

-- `lengthPA pa` returns an integer giving the length of the pure array `pa`.
recursive
let lengthPA = lam pa.
  match pa with PANode(i,l,x0,x1,x2,x3,x4,x5,x6,x7,x8,x9) then
    addi (muli i l)
      (switch i
        case 0 then lengthPA x0 case 1 then lengthPA x1 case 2 then lengthPA x2
        case 3 then lengthPA x3 case 4 then lengthPA x4 case 5 then lengthPA x5
        case 6 then lengthPA x6 case 7 then lengthPA x7 case 8 then lengthPA x8
        case _ then lengthPA x9
      end)
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

-- `seq2pa seq` converts a sequence to a pure array.
let seq2pa = lam seq.
  foldl (lam a. lam x. addPA a x) emptyPA seq


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

utest pa2seq (seq2pa [1,4,3,10]) with [1,4,3,10]

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

-- Another large test, iterates over all lengths, tests all operations
utest
  let steps = 1500 in
  let incv = 1000 in
  recursive
  let getset = lam i. lam l. lam pa.
    if eqi i l then pa
    else
      let v2 = addi (getPA pa i) incv in
      let pa2 = setPA pa i v2 in
      getset (addi i 1) l pa2
  let verify = lam i. lam l. lam pa2.
    if eqi i l then true
    else
    if eqi (getPA pa2 i) (addi i incv) then
      verify (addi i 1) l pa2
    else false
  let maintest = lam l.
    if eqi (addi steps 1) l then true
    else
      let pa = makePA l (lam x.x) in
      let pa2 = getset 0 l pa in
      let pa3 = seq2pa (pa2seq pa2) in
      if eqi (lengthPA pa3) l then
        if verify 0 l pa3 then maintest (addi l 1) else false
      else false
  in
  maintest 0
with true

