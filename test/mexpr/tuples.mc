-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test tuples

mexpr

-- Tuples
utest (1,3,10) with (1,3,10) in
utest () with () in
utest (2,8).1 with 8 in
utest (2,8,9).2 with 9 in
utest ('a',8,"the").2 with "the" in
utest ('a',8,"the").2 with "the" in

utest ("foo",5) with {#label"0" = "foo", #label"1" = 5} in

-- Singleton tuples
utest ("foo",) with ("foo",) in

()
