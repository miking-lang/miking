lang Empty
end

lang Small
  syn Bool =
  | True
  | False

  sem my_not =
  | True -> False
  | False -> True
end

lang Recursive
  syn Bool =
  | True
  | False

  sem my_not (n : Dyn) =
  | True -> if eqi n 0 then False else my_not (subi n 1) True
  | False -> if eqi n 0 then True else my_not (subi n 1) False
end

lang Mutual
  syn Bool =
  | True
  | False

  sem my_not (n : Dyn) =
  | True -> if eqi n 0 then False else my_not2 (subi n 1) True
  | False -> if eqi n 0 then True else my_not2 (subi n 1) False

  sem my_not2 (n : Dyn) =
  | True -> if eqi n 0 then False else my_not (subi n 1) True
  | False -> if eqi n 0 then True else my_not (subi n 1) False
end

let _ =
  use Empty in
  ()
in
let _ =
  use Small in
  utest my_not True with False in
  ()
in
let _ =
  use Recursive in
  utest my_not 5 True with False in
  ()
in
let _ =
  use Mutual in
  utest my_not 10 True with False in
  utest my_not2 5 True with False in
  utest my_not 42 False with True in
  utest my_not2 1 False with True in
  ()
in
()