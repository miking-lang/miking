-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Test string and char primitives

mexpr

let emptyStr : String = "" in

-- String and char construction (unicode characters)
utest 'a' with 'a' in
utest '島'with '島' in
utest "word" with "word" in
utest emptyStr with [] in
utest "大衛·布羅曼" with "大衛·布羅曼" in


-- Conversion, Unicode interger numer of a character
utest char2int 'A' with 65 in         -- Char -> Int
utest char2int 'ä' with 228 in
utest char2int '島' with 23798 in
utest char2int '\n' with 10 in
utest char2int '\r' with 13 in
utest int2char 97 with 'a' in         -- Int -> Char
utest int2char 252 with 'ü' in
utest int2char 28246 with '湖' in
utest int2char 10 with '\n' in
utest int2char 13 with '\r' in


-- String operations
-- See seq.mc as well. Strings are sequences.
utest concat "This " "is" with "This is" in
utest get "Hello" 1 with 'e' in
utest subsequence "This is all" 3 6 with "s is a" in
utest subsequence "This is all" 3 6 with ['s',' ','i','s',' ','a'] in

-- Nop
utest () with () in

()
