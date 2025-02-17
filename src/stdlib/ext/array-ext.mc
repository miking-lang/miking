/-
  This file contains a minimal interface to mutable arrays.
-/

type Array a
type CArray1 a


external arrayCreateFloat : Int -> Array Float

-- Creates a float array of size `n` with uninitialized values.
let arrayCreateFloat : Int -> Array Float = lam n. arrayCreateFloat n

utest arrayCreateFloat 3; () with ()


external arrayLength : all a. Array a -> Int

-- The length of the array `a`.
let arrayLength : all a. Array a -> Int = lam a. arrayLength a

utest arrayLength (arrayCreateFloat 3) with 3


external arrayGet : all a. Array a -> Int -> a

-- Get the `i`th element from the array `a`.
let arrayGet : all a. Array a -> Int -> a = lam a. lam i. arrayGet a i


external arraySet ! : all a. Array a -> Int -> a -> ()

-- Set, inplace, the `i`th element in the array `a` to the value `v`.
let arraySet : all a. Array a -> Int -> a -> () = lam a. lam i. lam v. arraySet a i v


utest
  let a  = arrayCreateFloat 3 in
  utest arraySet a 0 0. with () in
  utest arraySet a 1 1. with () in
  utest arraySet a 2 2. with () in
  utest arrayGet a 0 with 0. in
  utest arrayGet a 1 with 1. in
  utest arrayGet a 2 with 2. in
  ()
  with ()


external cArray1CreateFloat : Int -> CArray1 Float

-- Creates a float array of size `n` with uninitialized values. This array can
-- share data with external c-code.
let cArray1CreateFloat : Int -> CArray1 Float = lam n. cArray1CreateFloat n

utest cArray1CreateFloat 3; () with ()


external cArray1Dim : all a. CArray1 a -> Int

-- The length of the cArray1 `a`.
let cArray1Dim : all a. CArray1 a -> Int = lam a. cArray1Dim a

utest cArray1Dim (cArray1CreateFloat 3) with 3


external cArray1Get : all a. CArray1 a -> Int -> a

-- Get the `i`th element from the cArray1 `a`.
let cArray1Get : all a. CArray1 a -> Int -> a = lam a. lam i. cArray1Get a i


external cArray1Set ! : all a. CArray1 a -> Int -> a -> ()

-- Set, inplace, the `i`th element in the cArray1 `a` to the value `v`.
let cArray1Set : all a. CArray1 a -> Int -> a -> () = lam a. lam i. lam v. cArray1Set a i v


utest
  let a  = cArray1CreateFloat 3 in
  utest cArray1Set a 0 0. with () in
  utest cArray1Set a 1 1. with () in
  utest cArray1Set a 2 2. with () in
  utest cArray1Get a 0 with 0. in
  utest cArray1Get a 1 with 1. in
  utest cArray1Get a 2 with 2. in
  ()
  with ()
