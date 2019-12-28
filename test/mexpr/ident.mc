// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test general handling of integers

mexpr


let foo = 5 in
let Foo = 5 in
let #var"*9^/\nhi" = 8 in
utest #var"foo" with foo in
utest #type"Foo" with Foo in
utest #con"Foo" with Foo in
utest #var"*9^/\nhi" with #var"*9^/\nhi" in


()
