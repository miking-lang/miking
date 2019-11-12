lang Empty
end

lang Bool
  syn Bool =
  | True
  | False

  sem my_not =
  | True -> False
  | False -> True
end

lang AlsoBool = Bool
end

lang AlsoAlsoBool = AlsoBool
  sem to_bool =
  | True -> true
  | False -> false
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

lang And = Bool
  sem my_and (b1 : Dyn) =
  | True -> b1
  | False -> False
end

mexpr

let _ =
  use Empty in
  ()
in
let _ =
  use Bool in
  utest my_not True with False in
  ()
in
let _ =
  use AlsoBool in
  utest my_not True with False in
  ()
in
let _ =
  use AlsoAlsoBool in
  utest to_bool(my_not True) with false in
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
let _ =
  use And in
  utest my_and True True with True in
  utest my_and True False with False in
  utest my_and False True with False in
  utest my_and False False with False in
  ()
in
()
