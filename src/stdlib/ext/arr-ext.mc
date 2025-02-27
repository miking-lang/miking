--------------------------------------------------------------------------------
-- This file contains a minimal interface to mutable arrays, both internal to
-- MCore and shareable with external code.
--------------------------------------------------------------------------------

include "common.mc"

--==============================================================================
-- Mutable arrays with storage internal to MCore.
--------------------------------------------------------------------------------
-- The data of these arrays are not shareable with external code (e.g. due to
-- garbage collection).
--==============================================================================

type Arr a

--------------------------------------------------------------------------------
-- External declarations
--------------------------------------------------------------------------------

external externalArrMake : all a. Int -> a -> Arr a
external externalArrMakeUninitFloat : Int -> Arr Float
external externalArrLength : all a. Arr a -> Int
external externalArrGet : all a. Arr a -> Int -> a
external externalArrSet ! : all a. Arr a -> Int -> a -> ()
external externalArrSub : all a. Arr a -> Int -> Int -> Arr a

--------------------------------------------------------------------------------
-- Array interface
--------------------------------------------------------------------------------

-- Creates an array of length `n` with all elements set to.
let arrMake : all a. Int -> a -> Arr a
  = lam n. lam v. externalArrMake n v

utest arrMake 3 0; () with ()


-- Creates a float array of length `n` with uninitialized values.
let arrMakeUninitFloat : Int -> Arr Float
  = lam n. externalArrMakeUninitFloat n

utest arrMakeUninitFloat 3; () with ()


-- The length of the array.
let arrLength : all a. Arr a -> Int
  = lam a. externalArrLength a

utest arrLength (arrMakeUninitFloat 3) with 3


-- Gets the `i`th element from the array.
let arrGetExn : all a. Arr a -> Int -> a
  = lam a. lam i. externalArrGet a i

utest arrGetExn (arrMake 3 1) 0 with 1
utest arrGetExn (arrMake 3 1) 1 with 1
utest arrGetExn (arrMake 3 1) 2 with 1


-- Sets the `i`th element in the array to the value `v` inplace.
let arrSetExn : all a. Arr a -> Int -> a -> ()
  = lam a. lam i. lam v. externalArrSet a i v

utest
  let a  = arrMakeUninitFloat 3 in
  utest arrSetExn a 0 0. with () in
  utest arrSetExn a 1 1. with () in
  utest arrSetExn a 2 2. with () in
  utest arrGetExn a 0 with 0. in
  utest arrGetExn a 1 with 1. in
  utest arrGetExn a 2 with 2. in

  let a  = arrMake 3 0 in
  utest arrSetExn a 0 0 with () in
  utest arrSetExn a 1 1 with () in
  utest arrSetExn a 2 2 with () in
  utest arrGetExn a 0 with 0 in
  utest arrGetExn a 1 with 1 in
  utest arrGetExn a 2 with 2 in

  ()
  with ()


-- Creates a copy of a subset of the array, starting from `start` with length
-- `len`.
let arrSub : all a. Arr a -> Int -> Int -> Arr a
  = lam a. lam start. lam len. externalArrSub a start len


-- Creates an array of length `n`, where the element at index `i` is result of
-- the application `f i`. Produces an empty array if `n` not greater than zero.
let arrCreate : all a. Int -> (Int -> a) -> Arr a
  = lam n. lam f.
      if gti n 0 then
        let a0 = f 0 in
        let a = arrMake n a0 in
        repeati
          (lam i. let i = addi i 1 in arrSetExn a i (f i))
          (subi n 1);
        a
      else
        -- NOTE(oerikss, 2025-01-25): The array is empty so we don't care what
        -- the value is.
        unsafeCoerce arrMake 0 0

utest arrLength (arrCreate 0 (lam i. error "impossible")) with 0
utest arrLength (arrCreate 3 (lam i. i)) with 3
utest
  let a  = arrCreate 3 (lam i. i) in
  utest arrGetExn a 0 with 0 in
  utest arrGetExn a 1 with 1 in
  utest arrGetExn a 2 with 2 in
  ()
  with ()


--==============================================================================
-- Mutable arrays shareable with external code.
--==============================================================================

type ExtArrKind a
type ExtArr a

--------------------------------------------------------------------------------
-- External declarations
--------------------------------------------------------------------------------

external externalExtArrMakeUninit : all a. ExtArrKind a -> Int -> ExtArr a
external externalExtArrKind : all a. ExtArr a -> ExtArrKind a
external externalExtArrLength : all a. ExtArr a -> Int
external externalExtArrGet : all a. ExtArr a -> Int -> a
external externalExtArrSet ! : all a. ExtArr a -> Int -> a -> ()
external externalExtArrCopy : all a. ExtArr a -> ExtArr a
external externalExtArrFill : all a. ExtArr a -> a -> ()

--------------------------------------------------------------------------------
-- ExtArr interface
--------------------------------------------------------------------------------

-- Single precision float kind.
external extArrKindFloat32 : ExtArrKind Float

-- Double precision float kind.
external extArrKindFloat64 : ExtArrKind Float


-- Creates an external array of size `n` with uninitialized values.
let extArrMakeUninit : all a. ExtArrKind a -> Int -> ExtArr a
  = lam kind. lam n. externalExtArrMakeUninit kind n

utest extArrMakeUninit extArrKindFloat64 3; () with ()


-- Returns the array kind.
let extArrKind : all a. ExtArr a -> ExtArrKind a
  = lam a. externalExtArrKind a

utest
  extArrMakeUninit (extArrKind (extArrMakeUninit extArrKindFloat32 1)) 3; ()
  with ()
utest
  extArrMakeUninit (extArrKind (extArrMakeUninit extArrKindFloat64 1)) 3; ()
with ()


-- The length of the array.
let extArrLength : all a. ExtArr a -> Int
  = lam a. externalExtArrLength a

utest extArrLength (extArrMakeUninit extArrKindFloat64 3) with 3


-- Gets the `i`th element from the array.
let extArrGetExn : all a. ExtArr a -> Int -> a
  = lam a. lam i. externalExtArrGet a i

-- Sets the `i`th element of the array to the value `v` inplace.
let extArrSetExn : all a. ExtArr a -> Int -> a -> ()
  = lam a. lam i. lam v. externalExtArrSet a i v

utest
  let a  = extArrMakeUninit extArrKindFloat64 3 in
  utest extArrSetExn a 0 0. with () in
  utest extArrSetExn a 1 1. with () in
  utest extArrSetExn a 2 2. with () in
  utest extArrGetExn a 0 with 0. in
  utest extArrGetExn a 1 with 1. in
  utest extArrGetExn a 2 with 2. in
  ()
  with ()


-- Creates an external array from a sequence.
let extArrOfSeq : all a. ExtArrKind a -> [a] -> ExtArr a
  = lam kind. lam seq.
    let a = externalExtArrMakeUninit kind (length seq) in
    iteri (externalExtArrSet a) seq;
    a

-- Creates a sequence from an external array.
let extArrToSeq : all a. ExtArr a -> [a]
  = lam a. create (externalExtArrLength a) (externalExtArrGet a)

utest extArrToSeq (extArrOfSeq extArrKindFloat64 [1., 2., 3.]) with [1., 2., 3.]


-- Copies external array.
let extArrCopy : all a. ExtArr a -> ExtArr a
  = lam a. externalExtArrCopy a

utest extArrToSeq (extArrCopy (extArrOfSeq extArrKindFloat64 [1., 2., 3.]))
  with [1., 2., 3.]


-- Fills external array.
let extArrFill : all a . ExtArr a -> a -> ()
  = lam a. lam v. externalExtArrFill a v

utest
  let a  = extArrMakeUninit extArrKindFloat64 3 in
  utest extArrFill a 1. with () in
  utest extArrGetExn a 0 with 1. in
  utest extArrGetExn a 1 with 1. in
  utest extArrGetExn a 2 with 1. in
  ()
  with ()


-- Creates an external array.
let extArrMake : all a . ExtArrKind a -> Int -> a -> ExtArr a
  = lam kind. lam n. lam v.
    let a = externalExtArrMakeUninit kind n in
    externalExtArrFill a v;
    a

utest
  let a  = extArrMake extArrKindFloat64 3 1. in
  utest extArrGetExn a 0 with 1. in
  utest extArrGetExn a 1 with 1. in
  utest extArrGetExn a 2 with 1. in
  ()
  with ()
