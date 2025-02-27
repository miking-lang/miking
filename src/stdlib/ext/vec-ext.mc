/-

  High-level vector library.

-/

include "common.mc"
include "either.mc"
include "arr-ext.mc"
include "cblas-ext.mc"

-- Enumerates vector operation errors.
type VecError
con LengthMismatch : () -> VecError

-- String representation of a matrix error.
let vecErrorToString : VecError -> String
  = lam err.
    switch err
    case LengthMismatch _ then "Length mismatch"
    end

--------------------------------------------------------------------------------
-- External array based vector
--------------------------------------------------------------------------------

type Vec a = ExtArr a

-- Vectors has same length.
let vecHasSameLength : all a. all b. Vec a -> Vec b -> Bool
  = lam a. lam b.
    eqi (extArrLength a) (extArrLength b)

--------------------------------------------------------------------------------
-- Vector space operations for Vec specialized to floats.
--------------------------------------------------------------------------------

-- Adds two vectors. Returns a fresh vector.
let vecAdd : Vec Float -> Vec Float -> Either VecError (Vec Float)
  = lam a. lam b.
    if vecHasSameLength a b then
      let n = extArrLength a in
      let c = extArrMakeUninit (externalExtArrKind b) n in
      externalCblasCopy n b 1 c 1;
      externalCblasAxpy n 1. a 1 c 1;
      Right c
    else Left (LengthMismatch ())

let vecAddExn : Vec Float -> Vec Float -> Vec Float
  = lam a. lam b.
    eitherEither (lam err. error (vecErrorToString err)) (lam x. x) (vecAdd a b)

-- Scales vector. Returns a fresh vector.
let vecScale : Float -> Vec Float -> Vec Float
  = lam s. lam a.
    let n = extArrLength a in
    let b = extArrMakeUninit (externalExtArrKind a) n in
    externalCblasCopy n a 1 b 1;
    externalCblasScal n s b 1;
    b

utest
  let test = lam kind.
    let toSeq = extArrToSeq in
    let randVec = lam n.
      extArrOfSeq kind (create n (lam. int2float (randIntU 0 10)))
    in
    utest vecAdd (randVec 1) (randVec 2) with Left (LengthMismatch ()) in
    let zeroVec = lam n. extArrMake kind n 0. in
    -- Assert the vector space axioms
    -- (https://en.wikipedia.org/wiki/Vector_space).
    repeat (lam.
      let n = randIntU 0 100 in
      let a = int2float (randIntU 0 10) in
      let b = int2float (randIntU 0 10) in
      let u = randVec n in
      let v = randVec n in
      let w = randVec n in
      -- Associativity of vector addition.
      utest toSeq (vecAddExn u (vecAddExn v w))
        with toSeq (vecAddExn (vecAddExn u v) w)
      in
      -- Commutativity of vector addition.
      utest toSeq (vecAddExn u v) with toSeq (vecAddExn v u) in
      -- Identity element of vector addition.
      utest toSeq (vecAddExn (zeroVec n) v) with toSeq v in
      -- Inverse elements of vector addition.
      utest toSeq (vecAddExn v (vecScale -1. v)) with toSeq (zeroVec n) in
      -- Compatibility of scalar multiplication with field multiplication.
      utest toSeq (vecScale a (vecScale b v))
        with toSeq (vecScale (mulf a b) v)
      in
      -- Identity element of scalar multiplication.
      utest toSeq (vecScale 1. v) with toSeq v in
      -- Distributivity of scalar multiplication with respect to vector addition.
      utest toSeq (vecScale a (vecAddExn u v))
        with toSeq (vecAddExn (vecScale a u) (vecScale a v))
      in
      -- Distributivity of scalar multiplication with respect to field addition.
      utest toSeq (vecScale (addf a b) v)
        with toSeq (vecAddExn (vecScale a v) (vecScale b v))
      in
      ())
      100
  in
  test extArrKindFloat32;
  test extArrKindFloat64;
  () with ()

--------------------------------------------------------------------------------
-- Additional vector operations.
--------------------------------------------------------------------------------

-- TODO(oerikss, 2025-02-27): Add the dot product etc. For each operation first
-- see if it is part BLAS. If so, implement that in clbas-ext.mc and then
-- implement it here using that.
