-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test different instrinsics with side effects

mexpr


-- 'print s' prints out a string to the stdout.
-- String -> ()
utest if false then print "message\n" else 0 with 0 in


-- Test debug print (cannot execute actual printing)
-- Debug print can be applied to any term
utest if false then dprint ["message\n","hi"] else 0 with 0 in


-- 'writeFile fname s' writes a string 's' to a file named 'fname'.
-- String -> String -> ()
let str1 = "A unicode string.\n島" in
let file = "_testfile" in
let _ = writeFile file str1 in


-- 'readFile fname' reads a text file with filename 'fname' and returns a string
-- There is currently no error handling
let str2 = readFile file in
utest str1 with str2 in


-- 'fileExists fname' returns true if a file with name 'fname' exists, else false.
utest fileExists file with true in


-- 'deleteFile fname' deletes a file with name 'fname'
let _ = deleteFile file in
utest fileExists file with false in


-- 'errors s' prints out an error and terminates the program.
-- String -> ()
utest if false then error "message" else 0 with 0 in


// 'argv' contains the program arguments
utest slice argv 1 2 with [] in

// 'exit c' exits the program with error code 'c'
utest if true then () else exit 1 with () in

()
