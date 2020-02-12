mexpr

let a = sArrCreate 3 in
let _ = sArrSet a 0 0. in
let _ = sArrSet a 1 1. in
let _ = sArrSet a 2 2. in

utest sArrGet a 0 with 0. in
utest sArrGet a 1 with 1. in
utest sArrGet a 2 with 2. in
()
