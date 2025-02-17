lang Nat
  syn Nat =
  | Z ()
  | S Nat

  sem is_zero =
  | Z _ -> true
  | S _ -> false

  sem pred =
  | Z _ -> Z ()
  | S n -> n

  sem plus (n2 : Nat) =
  | Z _ -> n2
  | S n1 -> S (plus n1 n2)
end

mexpr

use Nat in
let z = Z () in
utest is_zero z with true in
utest is_zero (S z) with false in
utest pred z with z in
utest pred (S z) with z in
utest plus (S (S z)) (S z) with S (S (S z)) in
()
