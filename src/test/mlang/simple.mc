lang Empty
end

lang MyBool
  syn MyBool =
  | True ()
  | False ()

  sem my_not =
  | True _ -> False ()
  | False _ -> True ()
end

lang AlsoBool = MyBool
end

lang AlsoAlsoBool = AlsoBool
  sem to_bool =
  | True _ -> true
  | False _ -> false
end

lang Recursive
  syn MyBool =
  | True ()
  | False ()

  sem my_not (n : Int) =
  | True _ -> if eqi n 0 then False () else my_not (subi n 1) (True ())
  | False _ -> if eqi n 0 then True () else my_not (subi n 1) (False ())
end

lang Mutual
  syn MyBool =
  | True ()
  | False ()

  sem my_not (n : Int) =
  | True _ -> if eqi n 0 then False () else my_not2 (subi n 1) (True ())
  | False _ -> if eqi n 0 then True () else my_not2 (subi n 1) (False ())

  sem my_not2 (n : Int) =
  | True _ -> if eqi n 0 then False () else my_not (subi n 1) (True ())
  | False _ -> if eqi n 0 then True () else my_not (subi n 1) (False ())
end

lang And = MyBool
  sem my_and (b1 : MyBool) =
  | True _ -> b1
  | False _ -> False ()
end

mexpr

use Empty in
  ();

use MyBool in
  utest my_not (True ()) with False () in
  ();

use AlsoBool in
  utest my_not (True ()) with (False ()) in
  ();

use AlsoAlsoBool in
  utest to_bool(my_not (True ())) with false in
  ();

use Recursive in
  utest my_not 5 (True ()) with False () in
  ();

use Mutual in
  utest my_not 10 (True ()) with (False ()) in
  utest my_not2 5 (True ()) with (False ()) in
  utest my_not 42 (False ()) with (True ()) in
  utest my_not2 1 (False ()) with (True ()) in
  ();

use And in
  utest my_and (True ()) (True ()) with (True ()) in
  utest my_and (True ()) (False ()) with (False ()) in
  utest my_and (False ()) (True ()) with (False ()) in
  utest my_and (False ()) (False ()) with (False ()) in
  ()
