// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test string and char primitives

mexpr

// Unicode characters
utest 'a' with 'a' in
utest char2int 'A' with 65 in
utest char2int 'ä' with 228 in
utest char2int '島' with 23798 in
utest int2char 97 with 'a' in
utest int2char 252 with 'ü' in
utest int2char 28246 with '湖' in

//string construction
utest "word" with "word" in
utest "" with [] in
utest "大衛·布羅曼" with "大衛·布羅曼" in

// string operarations
utest concat "This " "is" with "This is" in
utest get "Hello" 1 with 'e' in
utest slice "This is all" 3 6 with "s is a" in
utest slice "This is all" 3 6 with ['s',' ','i','s',' ','a'] in

// Nop
utest () with () in

()
