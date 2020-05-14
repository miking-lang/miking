-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test general handling of integers

mexpr

-- Testing variables
let foo = 5 in
let Foo = 7 in
let #ident"*9^/\nhi" = 8 in

utest #ident"foo" with foo in
utest #ident"Foo" with Foo in
utest #ident"Foo" with 7 in
utest #ident"Foo" with Foo in
utest #ident"*9^/\nhi" with #ident"*9^/\nhi" in
utest #ident"*9^/\nhi" with 8 in

type Bar in
con f : (Int,Int) -> Bar in
con F : (Int,String) -> Bar in

utest match f(5,2) with f(x,y) then (y,x) else (0,0) with (2,5) in
utest match F(3,"a") with F(x,y) then (y,x) else ("b",0) with ("a",3) in
utest match F(3,"a") with f(x,y) then (y,x) else (0,0) with (0,0) in

()
