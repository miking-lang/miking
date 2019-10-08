// Miking is licensed under the MIT license.
// Copyright (C) David Broman. See file LICENSE.txt
//
// Test string and char primitives


// Unicode characters
utest 'a' with 'a' in
utest char2int 'A' with 65 in
utest char2int 'ä' with 228 in
utest char2int '島' with 23798 in
utest int2char 97 with 'a' in
utest int2char 252 with 'ü' in
utest int2char 28246 with '湖' in

nop
