-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Constructor tag intrinsic

mexpr

type Value in
con VInt : () -> Value in
con VFloat : () -> Value in
con VPair : (Value, Value) -> Value in

let v1 = VPair (VInt (), VFloat ()) in
let v2 = VPair (v1, VInt ()) in

-- Terms which are applications of the same constructor have the same
-- constructor tag.
utest constructorTag (VInt ()) with constructorTag (VInt ()) in
utest constructorTag (VFloat ()) with constructorTag (VFloat ()) in
utest constructorTag v1 with constructorTag v2 in

-- Terms in the same type, but with applications of different constructors,
-- have different constructor tags.
utest constructorTag (VInt ()) with constructorTag (VFloat ()) using neqi in
utest constructorTag (VInt ()) with constructorTag v1 using neqi in
utest constructorTag (VFloat ()) with constructorTag v2 using neqi in

()
