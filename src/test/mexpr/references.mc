-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Reference intrinstics

include "seq.mc"

mexpr

let r1 = ref 1 in
let r2 = ref 2. in
let r3 = r1 in
let r4 = ref (lam x. lam y. join ["Hello ", x, y]) in

utest deref r1 with 1 in
utest deref r2 with 2. using eqf in
utest deref r3 with 1 in
utest (deref r4) "there" "!" with "Hello there!" in

modref r3 4;
utest deref r1 with 4 in
utest deref r3 with 4 in

()
