lang Nat
  syn Nat =
  | Z ()
  | S Dyn

  sem is_zero =
  | Z _ -> true
  | n -> false

  sem pred =
  | Z _ -> Z ()
  | S n -> n

  sem plus (n2 : Dyn) =
  | Z _ -> n2
  | S n1 -> S (plus n1 n2)
end

mexpr

use Nat in
let Z = Z () in
utest is_zero Z with true in
utest is_zero (S Z) with false in
utest pred Z with Z in
utest pred (S Z) with Z in
utest plus (S (S Z)) (S Z) with S (S (S Z)) in
()
