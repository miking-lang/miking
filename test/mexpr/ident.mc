-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test general handling of integers

mexpr

-- Testing variables
let foo = 5 in
let #var"Foo" = 7 in
let #var"*9^/\nhi" = 8 in

utest #var"foo" with foo in
utest #var"Foo" with 7 in
utest #var"*9^/\nhi" with #var"*9^/\nhi" in
utest #var"*9^/\nhi" with 8 in

type Bar in
con F : (Int,Int) -> Bar in
con #con"f" : (Int,String) -> Bar in

utest match F(5,2) with F(x,y) then (y,x) else (0,0) with (2,5) in
utest match #con"f"(3,"a") with #con"f"(x,y) then (y,x) else ("b",0) with ("a",3) in
utest match #con"f"(3,"a") with F(x,y) then (y,x) else (0,0) with (0,0) in

()
