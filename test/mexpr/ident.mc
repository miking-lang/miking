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


()
