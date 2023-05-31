mexpr
let v = 1 in
match v with 3 then 1
else match v with 2 then 2
else match v with 4 then 3
else match v with 5 then 4
else 42
