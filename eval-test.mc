mexpr

-- let fib = lam n.
--   if lti n 1 then 0
--   else
--     if eqi n 1 then 1
--     else
--       recursive let recur = lam n1. lam n2. lam i.
--         let n3 = addi n1 n2 in
--         if eqi i n then n3
--         else recur n2 n3 (addi i 1)
--       in
--       recur 0 1 2
-- in

recursive let fib = lam n.
  if lti n 1 then 0
  else
    if eqi n 1 then 1
    else
      addi (fib (subi n 2)) (fib (subi n 1))
in

if eqi (fib 0) 0 then
  if eqi (fib 1) 1 then
    if eqi (fib 10) 55 then
      if eqi (fib 19) 4181 then
        fib 31
      else exit 1
    else exit 1
  else exit 1
else exit 1
