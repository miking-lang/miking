// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test errors

// Errors (cannot execute the actual error in the test suite)
utest if false then error "message" else 0 with 0 in

// Test print (cannot execute actual printing)
utest if false then print "message\n" else 0 with 0 in

// Test debug print (cannot execute actual printing)
utest if false then dprint "message\n" else 0 with 0 in

// Test argv
utest slice argv 1 2 with ["test","mexpr"] in

()
