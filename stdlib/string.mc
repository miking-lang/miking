include "seq.mc"
include "char.mc"

let eqstr = fix (lam eqstr. lam s1. lam s2.
    if neqi (length s1) (length s2)
    then false
    else if null s1
         then true
         else if eqchar (head s1) (head s2)
         then eqstr (tail s1) (tail s2)
         else false
)

let string2int = fix (lam string2int. lam s.
  let len = length s in
  let last = subi len 1 in
  if eqi len 0
  then 0
  else
    let lsd = subi (char2int (nth s last)) (char2int '0') in
    let rest = muli 10 (string2int (slice s 0 last)) in
    addi rest lsd
)

let int2string = fix (lam int2string. lam n.
  if lti n 10
  then [int2char (addi n (char2int '0'))]
  else
    let d = [int2char (addi (modi n 10) (char2int '0'))] in
    concat (int2string (divi n 10)) d
)

main
utest string2int "5" with 5 in
utest string2int "25" with 25 in
utest string2int "314159" with 314159 in

utest int2string 5 with "5" in
utest int2string 25 with "25" in
utest int2string 314159 with "314159" in
()