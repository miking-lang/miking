-- This program gives a parse error since an external is defined multiple times.

mexpr
external addi : Int -> Int -> Int in
external addi : Int -> Int -> Int in
()
