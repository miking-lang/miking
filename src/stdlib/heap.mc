include "list.mc"

-- NOTE(vipa, 2023-11-30): The code here is directly translated from
-- code here:
-- https://stackoverflow.com/questions/932721/efficient-heaps-in-purely-functional-languages

recursive let _treefold = lam f. lam zero. lam l.
  recursive let pairfold = lam l.
    match l with [x, y] ++ l
    then cons (f x y) (pairfold l)
    else l in
  switch l
  case [x] then
    x
  case [a, b] ++ l then
    _treefold f zero (cons (f a b) (pairfold l))
  case [] then
    zero
  end
end

type Heap a
con HNil : all a. () -> Heap a
con HNode : all a. (a, [Heap a]) -> Heap a

let heapEmpty : all a. Heap a
  = HNil ()

let heapSingleton : all a. a -> Heap a
  = lam a. HNode (a, [])

let heapMerge : all a. (a -> a -> Int) -> Heap a -> Heap a -> Heap a
  = lam cmp. lam heapA. lam heapB. switch (heapA, heapB)
    case (x, HNil _) | (HNil _, x) then x
    case (HNode (a, as), HNode (b, bs)) then
      if lti (cmp a b) 0
      then HNode (a, (cons heapB as))
      else HNode (b, (cons heapA bs))
    end

let heapMergeMany : all a. (a -> a -> Int) -> [Heap a] -> Heap a
  = lam cmp. lam hs. _treefold (heapMerge cmp) (HNil ()) hs

let heapAddMany : all a. (a -> a -> Int) -> [a] -> Heap a -> Heap a
  = lam cmp. lam toAdd. lam h.
    heapMerge cmp h (heapMergeMany cmp (map heapSingleton toAdd))

let heapPeek : all a. Heap a -> Option a
  = lam h. match h with HNode (a, _) then Some a else None ()

let heapPop : all a. (a -> a -> Int) -> Heap a -> Option (a, Heap a)
  = lam cmp. lam h. switch h
    case HNil _ then None ()
    case HNode (a, hs) then Some (a, heapMergeMany cmp hs)
    end
