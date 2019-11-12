// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test errors

mexpr

// Errors (cannot execute the actual error in the test suite)
utest if false then error "message" else 0 with 0 in

// Test print (cannot execute actual printing)
utest if false then print "message\n" else 0 with 0 in

// Test debug print (cannot execute actual printing)
utest if false then dprint "message\n" else 0 with 0 in

// Test argv
utest slice argv 1 2 with ["test","mexpr"] in

// Test to read and to write to a file
let str1 = "A unicode string.\n島" in
let file = "_testfile" in
let _ = writeFile file str1 in
let str2 = readFile file in
utest str1 with str2 in
utest fileExists file with true in
let _ = deleteFile file in
utest fileExists file with false in

()
