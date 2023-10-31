-- MExpr implementation of a cons list using explicit constructors.

include "option.mc"

type List a
con Cons : all a. (a, List a) -> List a
con Nil : all a. () -> List a

let listEmpty : all a. List a = Nil ()

let listNil : all a. List a -> Bool = lam li.
  match li with Nil _ then true else false

let listCons : all a. a -> List a -> List a = lam e. lam li. Cons (e, li)

let listFind : all a. (a -> Bool) -> List a -> Option a = lam p. lam li.
  recursive let find = lam li.
    switch li
    case Cons (e, li) then
      if p e then Some e
      else find li
    case Nil _ then None ()
    end
  in find li

let listFindMap : all a. all b. (a -> Option b) -> List a -> Option b = lam p. lam li.
  recursive let find = lam li.
    switch li
    case Cons (e, li) then
      match p e with r & Some _ then r
      else find li
    case Nil _ then None ()
    end
  in find li

let listFindMapWithIndex : all a. all b. (Int -> a -> Option b) -> List a -> Option b = lam p. lam li.
  recursive let find = lam idx. lam li.
    switch li
    case Cons (e, li) then
      match p idx e with r & Some _ then r
      else find (addi idx 1) li
    case Nil _ then None ()
    end
  in find 0 li

let listFromSeq : all a. [a] -> List a = lam l.
  recursive let build = lam acc. lam s.
    match s with mid ++ [last] then
      build (listCons last acc) mid
    else acc
  in
  build listEmpty l

let listFoldl : all a. all b. (b -> a -> b) -> b -> List a -> b = lam f.
  recursive let fold = lam acc. lam li.
    switch li
    case Cons (x, li) then fold (f acc x) li
    case Nil _ then acc
    end
  in fold

let listReverse : all a. List a -> List a = lam l.
  listFoldl (lam acc. lam x. listCons x acc) listEmpty l

let listMap : all a. all b. (a -> b) -> List a -> List b = lam f. lam li.
  recursive let map = lam acc. lam li.
    switch li
    case Cons (x, li) then map (Cons (f x, acc)) li
    case Nil _ then acc
    end
  in
  listReverse (map listEmpty li)

let listToSeq : all a. List a -> [a] = lam l. listFoldl snoc [] l

let listEq : all a. all b. (a -> b -> Bool) -> List a -> List b -> Bool =
  lam eqElem.
  recursive let work = lam l. lam r.
    switch (l, r)
    case (Cons (lh, lt), Cons (rh, rt)) then
      if eqElem lh rh then work lt rt
      else false
    case (Nil _, Nil _) then true
    case _ then false
    end
  in work

let listAll : all a. (a -> Bool) -> List a -> Bool =  lam p. lam li.
  recursive let forAll = lam li.
    switch li
    case Cons (x, li) then
      if p x then forAll li else false
    case Nil _ then true
    end
  in
  forAll li

let listFilter : all a. (a -> Bool) -> List a -> List a = lam p. lam li.
  listReverse
    (listFoldl (lam acc. lam x. if p x then Cons (x, acc) else acc) (Nil ()) li)

let listConcat : all a. List a -> List a -> List a = lam lhs. lam rhs.
  listFoldl (lam acc. lam x. listCons x acc) rhs (listReverse lhs)

mexpr

let l1 = listEmpty in
let l2 = listCons 3 l1 in
let l3 = listCons 4 (listCons 3 l2) in
utest l1 with Nil () using listEq eqi in
utest l2 with Cons (3, Nil ()) in
utest l3 with Cons (4, Cons (3, Cons (3, Nil ()))) in

utest listNil l1 with true in
utest listNil l2 with false in
utest listNil l3 with false in

let l4 = listFromSeq [2, 3, 4] in
utest l4 with Cons (2, Cons (3, Cons (4, Nil ()))) in
utest listToSeq l4 with [2, 3, 4] in

let findInt = lam i. lam x.
  match x with (y, _) in
  eqi i y
in
let l5 = listFromSeq [(2, "2"), (3, "3"), (5, "5")] in
utest listFind (findInt 0) l5 with None () in
utest listFind (findInt 2) l5 with Some (2, "2") in
utest listFind (findInt 3) l5 with Some (3, "3") in
utest listFind (findInt 4) l5 with None () in

utest listReverse l4 with Cons (4, Cons (3, Cons (2, Nil ()))) in

let l6 = listMap (addi 1) l4 in
utest l6 with Cons (3, Cons (4, Cons (5, Nil ()))) in
utest listFoldl addi 0 l4 with 9 in
utest listFoldl addi 0 l6 with 12 in

utest listAll (lti 2) (listFromSeq [4, 4, 5, 3]) with true in
utest listAll (gti 3) (listFromSeq [4, 4, 5, 3]) with false in

utest listFilter (lti 2) (listFromSeq [4, 3, 5, 3])
  with listFromSeq [4, 3, 5, 3]
in
utest listFilter (lti 3) (listFromSeq [4, 3, 5, 3])
  with listFromSeq [4, 5]
in

utest listConcat (listFromSeq [1, 2, 3]) (listFromSeq [4, 5])
  with listFromSeq [1, 2, 3, 4, 5]
in
utest listConcat (listFromSeq []) (listFromSeq [4, 5])
  with listFromSeq [4, 5]
in
utest let l : [Int] = [] in listConcat (listFromSeq l) (listFromSeq l)
  with listFromSeq []
in

()
