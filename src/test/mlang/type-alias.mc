-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Type-aliases defined within language fragments.

lang Base
  syn T1 =

  syn T2 =
end

lang L1 = Base
  syn T1 =

  type A1 = {a1 : T1, a2 : T2}
  type A2 = {b1 : A1, b2 : Int}

  syn T2 =
  | X ()
end

lang L2 = Base
  syn T2 =
  | Y ()

  type A3 = Int
end

lang L3 = L1 + L2
  syn T1 =
  | Z ()
  | W ()

  type A4 = [(A3, T1)]

  syn T2 =
  | K A4
end

lang L4 = L3
  type A5 = (A3, T3)

  syn T3 =
  | A A6
  | B A5

  type A6 = Float
end

mexpr

use L4 in

-- NOTE(larshum, 2022-01-25): This function could be defined as a semantic
-- function in one of the above language fragments. However, this is translated
-- to code that uses a dprint, which cannot be type-checked at the time of
-- writing. This is needed to ensure that the type aliases in language
-- fragments have been translated correctly.
let f : A1 -> A2 -> Int = lam fst. lam snd.
  match fst with {a1 = a1, a2 = a2} in
  match snd with {b1 = b1, b2 = b2} in
  match a1 with Z _ then
    match a2 with X _ then
      4
    else match b1 with {a1 = x, a2 = y} in
    match x with W _ then
      2
    else match y with Y _ then
      3
    else b2
  else b2
in

let t11 = {a1 = Z (), a2 = Y ()} in
let t12 = {a1 = Z (), a2 = X ()} in
let t21 = {b1 = {a1 = W (), a2 = X ()}, b2 = 6} in
let t22 = {b1 = t11, b2 = 7} in
let t23 = {b1 = t12, b2 = 8} in
utest f t11 t21 with 2 in
utest f t12 t21 with 4 in
utest f t11 t22 with 3 in
utest f t11 t23 with 8 in

let t : A4 = create 3 (lam i. (i, Z ())) in
utest t with [(0, Z ()), (1, Z ()), (2, Z ())] in

let t13 = {a1 = W (), a2 = K t} in
utest f t13 t22 with 7 in

recursive let sum_a5 : A5 -> Int = lam t : A5.
  match t with (n, A f) then
    addi n (floorfi f)
  else match t with (n, B next) then
    addi n (sum_a5 next)
  else never
in

let t : A5 = (3, B (4, B (9, A 2.0))) in
utest sum_a5 t with 18 in

()
