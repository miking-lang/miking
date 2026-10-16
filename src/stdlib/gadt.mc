-- MCore currently does not have support for generalized algebraic
-- data types, but sometimes they're convenient anyway. This file
-- implements some helper to work with GADTs anyway.
--
-- For an example, see the `Val` type and `unVal` functions in the
-- tests.
--
-- Assumptions:
-- * The backend used for compilation has some form of universal
--   representation, i.e., the runtime semantics of `unsafeCoerce` is
--   truly the identity function.
--
-- The implementations in this file are almost exclusively implemented
-- using `unsafeCoerce`. Soundness depends on the types being sensible
-- (which is manually checked), and that the `TyEq` type is only
-- directly manipulated by functions from this file which precludes,
-- e.g., adding new constructors to it.

type TyEq a b

let tyEq : all a. TyEq a a = unsafeCoerce ()
let tyEqFlip : all a. all b. TyEq a b -> TyEq b a = unsafeCoerce
let tyEqL : all a1. all a2. all b1. all b2. TyEq (a1, a2) (b1, b2) -> TyEq a1 b1 = unsafeCoerce
let tyEqR : all a1. all a2. all b1. all b2. TyEq (a1, a2) (b1, b2) -> TyEq a2 b2 = unsafeCoerce

let coerce : all a. all b. TyEq a b -> a -> b = lam. unsafeCoerce

mexpr

utest coerce tyEq 1 with 1 in

let eqInt : TyEq Int Int = tyEq in
utest coerce eqInt 2 with 2 in
utest coerce (tyEqFlip eqInt) 3 with 3 in

let eqPair : TyEq (Int, Char) (Int, Char) = tyEq in
utest coerce (tyEqL eqPair) 4 with 4 in
utest coerce (tyEqR eqPair) 'c' with 'c' in

type Val a in
con VInt : all a. (TyEq a Int, Int) -> Val a in
con VBool : all a. (TyEq a Bool, Bool) -> Val a in

let unVal : all a. Val a -> a = lam v.
  switch v
  case VInt (w, i) then coerce (tyEqFlip w) i
  case VBool (w, b) then coerce (tyEqFlip w) b
  end in

utest unVal (VInt (tyEq, 5)) with 5 in
utest unVal (VBool (tyEq, true)) with true in

-- The following should not type-check, but we cannot place negative tests here:
--
-- let bad : TyEq Int Float = tyEq in
-- let bad : Float = coerce eqInt 1 in
-- let bad = coerce eqInt 'c' in
-- let bad : TyEq Char Char = tyEqL eqPair in
-- let bad = tyEqL eqInt in
-- let bad : Val Bool = VInt (tyEq, 1) in

()
