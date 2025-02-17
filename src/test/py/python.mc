mexpr

let builtins = pyimport "builtins" in

let x = [5, 4, 3, 2, 1] in
let sum_x = pycall builtins "sum" (x,) in
utest pyconvert sum_x with 15 in
let sum_0 = pycall builtins "sum" ([],) in
utest pyconvert sum_0 with 0 in
let sorted_x = pycall builtins "sorted" (x,) in
utest pyconvert sorted_x with [1, 2, 3, 4, 5] in
let len_x = pycall builtins "len" (x,) in
utest pyconvert len_x with 5 in

let y = negi 1337 in
let abs_y = pycall builtins "abs" (y,) in
utest pyconvert abs_y with 1337 in
let f = pycall builtins "float" ("+1.23",) in
utest pyconvert f with 1.23 in

let a = [true, false, true] in
let all_a = pycall builtins "all" (a,) in
utest pyconvert all_a with false in
let any_a = pycall builtins "any" (a,) in
utest pyconvert any_a with true in

let keys = ["one", "two", "three"] in
let vals = [1, 2, 3] in
let dict = pycall builtins "dict" (pycall builtins "zip" (keys,vals),) in
utest pyconvert dict with {one=1, two=2, three=3} in

let str = pycall builtins "str" ({one=1, two=2, three=3},) in
utest pyconvert str with "{'one': 1, 'two': 2, 'three': 3}" in

let t = pycall builtins "tuple" ((1,2),) in
utest pyconvert t with (1,2) in

utest pyconvert (pycall builtins "str" ((),)) with "None" in
let none = pycall builtins "print" ("",) in
utest pyconvert (pycall builtins "str" (none,)) with "None" in
utest pyconvert none with () in

let e = pycallkw builtins "enumerate" ([1,2,3],) {start = 1} in
utest pyconvert (pycall builtins "list" (e,)) with [(1,1), (2,2), (3,3)] in

()
