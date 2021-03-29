-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Boolean intrinstics

include "bool.mc"

mexpr

-- Boolean values
utest true with true in
utest false with false in

-- Boolean not
utest true with not false in

-- Boolean and
utest true with and true true in
utest false with and false true in
utest false with and true false in
utest false with and false false in

-- Boolean or
utest true with or true true in
utest true with or false true in
utest true with or true false in
utest false with or false false in

()
