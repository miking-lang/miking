-- Miking is licensed under the MIT license.
-- Copyright (C) David Broman. See file LICENSE.txt
--
-- Defines auxiliary functions for the map intrinsics.

include "avl.mc"
include "option.mc"
include "seq.mc"
include "string.mc"

-- NOTE(larshum, 2023-03-05): Below follows the implementation of the (as of
-- writing) intrinsic functions of the map data type, making use of the native
-- AVL tree implementation.
type Map k v = use AVLTreeImpl in {cmp : k -> k -> Int, root : AVL k v}


-- ┌────────────┐
-- │ Empty/Size │
-- └────────────┘

let mapEmpty : all k. all v. (k -> k -> Int) -> Map k v = lam cmp.
  use AVLTreeImpl in
  {cmp = cmp, root = avlEmpty ()}

let mapSize : all k. all v. Map k v -> Int = lam m.
  use AVLTreeImpl in
  avlSize m.root

let mapLength : all k. all v. Map k v -> Int = lam m. mapSize m

let mapIsEmpty : all k. all v. Map k v -> Bool = lam m.
  use AVLTreeImpl in
  avlIsEmpty m.root


-- ┌────────┐
-- │ Remove │
-- └────────┘

let mapRemove : all k. all v. k -> Map k v -> Map k v =
  lam k. lam m.
  use AVLTreeImpl in
  {m with root = avlRemove m.cmp k m.root}


-- ┌─────────────┐
-- │ Find/Lookup │
-- └─────────────┘

let mapFindExn : all k. all v. k -> Map k v -> v =
  lam k. lam m.
  use AVLTreeImpl in
  optionGetOrElse
    (lam. error "mapFindExn: key not found")
    (avlLookup m.cmp k m.root)

let mapFindOrElse : all k. all v. (() -> v) -> k -> Map k v -> v =
  lam f. lam k. lam m.
  use AVLTreeImpl in
  optionGetOrElse f (avlLookup m.cmp k m.root)

let mapFindApplyOrElse : all k. all v1. all v2.
  (v1 -> v2) -> (() -> v2) -> k -> Map k v1 -> v2 =
  lam fnThn. lam fnEls. lam k. lam m.
  use AVLTreeImpl in
  optionMapOrElse fnEls fnThn (avlLookup m.cmp k m.root)

let mapLookup : all k. all v. k -> Map k v -> Option v =
  lam k. lam m.
  use AVLTreeImpl in
  avlLookup m.cmp k m.root

let mapLookupOrElse : all k. all v. (() -> v) -> k -> Map k v -> v =
  lam f. lam k. lam m.
  mapFindOrElse f k m
let mapLookupApplyOrElse : all k. all v1. all v2.
  (v1 -> v2) -> (() -> v2) -> k -> Map k v1 -> v2 =
  lam f1. lam f2. lam k. lam m.
  mapFindApplyOrElse f1 f2 k m

let mapLookupOr : all k. all v. v -> k -> Map k v -> v =
  lam dv. lam k. lam m.
  mapLookupOrElse (lam. dv) k m

-- `mapFindUpper k m` returns the key-value pair (k', v) in the map `m`,
-- where k' is the minimum key in `m` and k≤k'. Returns `None ()` if no such key
-- k' exists in `m`. Time complexity is O(log n).
let mapFindUpper : all k. all v. k -> Map k v -> Option (k, v)
  = lam k. lam m. use AVLTreeImpl in avlFindUpper m.cmp k m.root

-- `mapFindLower k m` returns the key-value pair (k', v) in the map `m`,
-- where k' is the maximum key in `m` and k≥k'. Returns `None ()` if no such key
-- k' exists in `m`. Time complexity is O(log n).
let mapFindLower : all k. all v. k -> Map k v -> Option (k, v)
  = lam k. lam m. use AVLTreeImpl in avlFindLower m.cmp k m.root


-- ┌───────────────┐
-- │ Insert/Update │
-- └───────────────┘

let mapInsert : all k. all v. k -> v -> Map k v -> Map k v =
  lam k. lam v. lam m.
  use AVLTreeImpl in
  {m with root = avlInsert m.cmp k v m.root}

let mapInsertWith : all k. all v. (v -> v -> v) -> k -> v -> Map k v -> Map k v =
  lam f. lam k. lam v. lam m.
    match mapLookup k m with Some prev then
      mapInsert k (f prev v) m
    else mapInsert k v m

-- `mapUpdate k f m` looks up `k` in `m` and applies `f` to the result of this
-- lookup. If the result of this application is `Some v`, the binding `k` in `m`
-- is updated to bind to `v`. Otherwise, if the result is `None _`, the binding
-- `k` is removed from `m`.
-- OPT(oerikss, 2023-04-27): We might be able to reduce this to one map access
-- if we operate directly on the AVLTree.
let mapUpdate : all k. all v. k -> (Option v -> Option v) -> Map k v -> Map k v
  = lam k. lam f. lam m.
    switch f (mapLookup k m)
    case Some v then mapInsert k v m
    case None _ then mapRemove k m
    end


-- ┌───────────┐
-- │ Singleton │
-- └───────────┘

-- `mapSingleton cmp k v` creates a singleton map with key-value `k, v` and
-- comparision function `cmp`.
let mapSingleton : all k. all v. (k -> k -> Int) -> k -> v -> Map k v
  = lam cmp. lam k. lam v. mapInsert k v (mapEmpty cmp)


-- ┌────────┐
-- │ Choose │
-- └────────┘

-- `mapChoose m` chooses one binding from `m`, giving `None ()` if `m` is
-- empty.
let mapChoose : all k. all v. Map k v -> Option (k, v) = lam m.
  use AVLTreeImpl in
  avlChoose m.root

let mapChooseExn : all k. all v. Map k v -> (k, v) = lam m.
  use AVLTreeImpl in
  optionGetOrElse (lam. error "mapChooseExn: empty map") (avlChoose m.root)

let mapChooseOrElse : all k. all v. (() -> (k, v)) -> Map k v -> (k, v) =
  lam f. lam m.
  use AVLTreeImpl in
  optionGetOrElse f (avlChoose m.root)


-- ┌────────┐
-- │ Member │
-- └────────┘

let mapMem : all k. all v. k -> Map k v -> Bool = lam k. lam m.
  use AVLTreeImpl in
  optionIsSome (avlLookup m.cmp k m.root)


-- ┌────────┐
-- │ Eq/Cmp │
-- └────────┘

let mapEq : all k. all v. (v -> v -> Bool) -> Map k v -> Map k v -> Bool =
  lam eqv. lam m1. lam m2.
  use AVLTreeImpl in
  avlEq m1.cmp eqv m1.root m2.root

let mapCmp : all k. all v. (v -> v -> Int) -> Map k v -> Map k v -> Int =
  lam cmpv. lam m1. lam m2.
  use AVLTreeImpl in
  avlCmp m1.cmp cmpv m1.root m2.root

let mapGetCmpFun : all k. all v. Map k v -> (k -> k -> Int) = lam m. m.cmp


-- ┌──────────────────┐
-- │ To/From Sequence │
-- └──────────────────┘

let mapBindings : all k. all v. Map k v -> [(k, v)] = lam m.
  use AVLTreeImpl in
  avlToSeq [] m.root

let mapToSeq : all k. all v. Map k v -> [(k,v)] = lam m.
  mapBindings m

let mapFromSeq : all k. all v. (k -> k -> Int) -> [(k, v)] -> Map k v =
  lam cmp. lam bindings.
  use AVLTreeImpl in
  {cmp = cmp, root = avlFromSeq cmp bindings}


-- ┌──────────┐
-- │ Fold/Map │
-- └──────────┘

let mapFoldWithKey : all k. all v. all a. (a -> k -> v -> a) -> a -> Map k v -> a =
  lam f. lam acc. lam m.
  use AVLTreeImpl in
  avlFold f acc m.root

let mapMapWithKey : all k. all v1. all v2. (k -> v1 -> v2) -> Map k v1 -> Map k v2 =
  lam f. lam m.
  use AVLTreeImpl in
  {cmp = m.cmp, root = avlMap f m.root}

let mapMap : all k. all v1. all v2. (v1 -> v2) -> Map k v1 -> Map k v2 =
  lam f. lam m.
  mapMapWithKey (lam. lam v. f v) m

let mapFoldlOption : all k. all v. all acc.
  (acc -> k -> v -> Option acc) -> acc -> Map k v -> Option acc =
  lam f. lam acc. lam m.
    optionFoldlM (lam acc. lam t : (k, v). f acc t.0 t.1) acc (mapBindings m)

let mapMapAccum : all k. all v1. all v2. all acc.
  (acc -> k -> v1 -> (acc, v2)) -> acc -> Map k v1 -> (acc, Map k v2) =
  lam f. lam acc. lam m.
    mapFoldWithKey
      (lam tacc : (acc, Map k v2). lam k. lam v1.
         let fval : (acc, v2) = f tacc.0 k v1 in
         match fval with (acc, v2) then (acc, mapInsert k v2 tacc.1) else never)
      (acc, mapEmpty (mapGetCmpFun m)) m

-- `mapMapWithKeyK f m k` maps the continuation passing function `f` over the
-- values of `m`, passing the result of the mapping to the continuation `k`.
let mapMapWithKeyK
  : all k. all v1. all v2. all a.
    (k -> v1 -> (v2 -> a) -> a) -> Map k v1 -> (Map k v2 -> a) -> a
  = lam f. lam m. lam k.
  mapFoldWithKey
    (lam k. lam key. lam val.
      (lam m. f key val (lam val. k (mapInsert key val m))))
    k m (mapEmpty (mapGetCmpFun m))

-- `mapMapK f m k` maps the continuation passing function `f` over the values of
-- `m`, passing the result of the mapping to the continuation `k`.
let mapMapK
  : all k. all v1. all v2. all a.
    (v1 -> (v2 -> a) -> a) -> Map k v1 -> (Map k v2 -> a) -> a
  = lam f. mapMapWithKeyK (lam. f)


-- ┌─────────┐
-- │ Any/All │
-- └─────────┘

let mapAny : all k. all v. (k -> v -> Bool) -> Map k v -> Bool =
  lam f. lam m.
  use AVLTreeImpl in
  let anyFn = lam acc. lam k. lam v.
    if acc then acc else f k v
  in
  avlFold anyFn false m.root

let mapAll : all k. all v. (v -> Bool) -> Map k v -> Bool = lam f. lam m.
  mapFoldWithKey (lam acc. lam. lam v. and acc (f v)) true m

let mapAllWithKey : all k. all v. (k -> v -> Bool) -> Map k v -> Bool =
  lam f. lam m.
  mapFoldWithKey (lam acc. lam k. lam v. and acc (f k v)) true m


-- ┌─────────┐
-- │ Min/Max │
-- └─────────┘

-- `mapGetMin m` returns the smallest key-value pair of `m`, or None ()
-- if the map is empty.
let mapGetMin : all k. all v. Map k v -> Option (k, v) =
  lam m.
    if mapIsEmpty m then None ()
    else
      use AVLTreeImpl in
      match avlSplitFirst m.root with (k, v, _) in
      Some (k, v)


-- ┌─────────────┐
-- │ Keys/Values │
-- └─────────────┘

let mapKeys : all k. all v. Map k v -> [k] = lam m.
  mapFoldWithKey (lam ks. lam k. lam. snoc ks k) [] m

let mapValues : all k. all v. Map k v -> [v] = lam m.
  mapFoldWithKey (lam vs. lam. lam v. snoc vs v) [] m


-- ┌─────────────┐
-- │ Merge/Union │
-- └─────────────┘

-- Generalized merging of two maps. This can be used to express union,
-- difference, intersection, etc.; any combination of two maps where
-- we do some form of combination and filtering at each key.
let mapMerge : all k. all a. all b. all c.
  (Option a -> Option b -> Option c) -> Map k a -> Map k b -> Map k c =
  lam f. lam l. lam r.
  use AVLTreeImpl in
  {cmp = l.cmp, root = avlMerge l.cmp f l.root r.root}

-- This is `mapMerge`, except the combination function has access to
-- the key being merged.
let mapMergeWithKey : all k. all a. all b. all c.
  (k -> Option a -> Option b -> Option c) -> Map k a -> Map k b -> Map k c =
  lam f. lam l. lam r.
  use AVLTreeImpl in
  {cmp = l.cmp, root = avlMergeWithKey l.cmp f l.root r.root}

let mapUnion : all k. all v. Map k v -> Map k v -> Map k v = lam l. lam r.
  use AVLTreeImpl in
  {l with root = avlUnionWith l.cmp (lam. lam rv. rv) l.root r.root}

let mapUnionWith : all k. all v. (v -> v -> v) -> Map k v -> Map k v -> Map k v = lam f. lam l. lam r.
  use AVLTreeImpl in
  {l with root = avlUnionWith l.cmp f l.root r.root}


-- ┌──────────────────────┐
-- │ Intersect/Difference │
-- └──────────────────────┘

let mapIntersectWith : all k. all a. all b. all c. (a -> b -> c) -> Map k a -> Map k b -> Map k c =
  lam f. lam l. lam r.
  use AVLTreeImpl in
  {cmp = l.cmp, root = avlIntersectWith l.cmp f l.root r.root}

let mapDifference : all k. all v. all v2. Map k v -> Map k v2 -> Map k v =
  lam l. lam r.
  use AVLTreeImpl in
  {l with root = avlDifference l.cmp l.root r.root}


-- ┌────────┐
-- │ Filter │
-- └────────┘

-- Perform a mapping and filtering at the same time, with access to
-- the key.
let mapMapOptionWithKey : all k. all a. all b. (k -> a -> Option b) -> Map k a -> Map k b
  = lam f. lam m.
  use AVLTreeImpl in
  {root = avlMapOption f m.root, cmp = m.cmp}

-- Like `mapMapOptionWithKey` but without access to the key.
let mapMapOption : all k. all a. all b. (a -> Option b) -> Map k a -> Map k b
  = lam f. lam m.
  use AVLTreeImpl in
  {root = avlMapOption (lam. f) m.root, cmp = m.cmp}

-- `mapFilterWithKey p m` filters the map `m` with the predicate `p`.
let mapFilterWithKey : all k. all v. (k -> v -> Bool) -> Map k v -> Map k v
  = lam p. lam m.
  use AVLTreeImpl in
  {root = avlFilter p m.root, cmp = m.cmp}

-- `mapFilter p m` filters the map `m` with the predicate `p`.
let mapFilter : all k. all v. (v -> Bool) -> Map k v -> Map k v
  = lam p. lam m.
  use AVLTreeImpl in
  {root = avlFilter (lam. p) m.root, cmp = m.cmp}

mexpr

let m = mapEmpty subi in

utest mapChoose m with None () in
utest mapGetMin m with None () in

utest mapLookupOrElse (lam. 2) 1 m with 2 in
utest mapLookupApplyOrElse (lam. 2) (lam. 3) 1 m with 3 in
utest mapLength m with 0 in
utest mapIsEmpty m with true in

utest mapLookup 1 m with None () using optionEq eqi in

let m = mapEmpty subi in

let m = mapInsert 1 "1" m in
let m = mapInsert 2 "2" m in
let m = mapInsert 3 "3" m in

utest mapLength m with 3 in
utest mapIsEmpty m with false in

utest mapLookup 1 m with Some "1" using optionEq eqString in
utest mapLookup 2 m with Some "2" using optionEq eqString in
utest mapLookup 3 m with Some "3" using optionEq eqString in
utest mapLookup 4 m with None () using optionEq eqString in

utest
  match mapChoose m with Some _ then true else false
with true in

let m2 = mapInsert 2 "22" m in
let m2 = mapInsert 4 "44" m2 in
let m2 = mapInsert (negi 1) "-1" m2 in

let merged = mapUnion m m2 in
utest mapLookup 1 merged with Some "1" using optionEq eqString in
utest mapLookup 2 merged with Some "22" using optionEq eqString in
utest mapLookup 3 merged with Some "3" using optionEq eqString in
utest mapLookup 4 merged with Some "44" using optionEq eqString in
utest mapLookup (negi 1) merged with Some "-1" using optionEq eqString in
utest mapLookup 5 merged with None () using optionEq eqString in

let m3 = mapFromSeq subi [(1, "m1"), (4, "m4"), (negi 1, "-1")] in
let mergedWith = mapUnionWith concat m m3 in
utest mapLookup 1 mergedWith with Some "1m1" using optionEq eqString in
utest mapLookup 2 mergedWith with Some "2" using optionEq eqString in
utest mapLookup 3 mergedWith with Some "3" using optionEq eqString in
utest mapLookup 4 mergedWith with Some "m4" using optionEq eqString in
utest mapLookup (negi 1) mergedWith with Some "-1" using optionEq eqString in
utest mapLookup 5 mergedWith with None () using optionEq eqString in

utest mapFoldlOption (lam acc. lam k. lam v. Some v) "0" m
with Some "3" using optionEq eqString in
utest mapFoldlOption
  (lam acc. lam k. lam v. if eqi k acc then None () else Some acc) 3 m
with None () using optionEq eqi in

let m = mapFromSeq subi
  [ (1, "1")
  , (2, "2")
  ] in
utest mapLookup 1 m with Some "1" using optionEq eqString in
utest mapLookup 2 m with Some "2" using optionEq eqString in
utest mapLookup 3 m with None () using optionEq eqString in

let m2 = mapInsertWith concat 1 "blub" m in
utest mapLookup 1 m2 with Some "1blub" using optionEq eqString in
utest mapLookup 2 m2 with mapLookup 2 m using optionEq eqString in
utest mapLookup 3 m2 with mapLookup 3 m using optionEq eqString in

utest mapKeys m2 with [1,2] in
utest mapValues m2 with ["1blub","2"] in
utest mapToSeq m2 with [(1,"1blub"), (2,"2")] in

utest
  match mapMapAccum (lam acc. lam k. lam v. ((addi k acc), concat "x" v)) 0 merged
  with (acc, m)
  then (acc, mapBindings m)
  else never
with (9,[(negi 1,("x-1")),(1,("x1")),(2,("x22")),(3,("x3")),(4,("x44"))]) in

let m = mapFromSeq subi
  [ (1, "1")
  , (2, "2")
  , (123, "123")
  ] in
utest mapAllWithKey (lam i. lam. geqi i 1) m with true in
utest mapAllWithKey (lam i. lam. leqi i 123) m with true in
utest mapAllWithKey (lam i. lam. lti i 123) m with false in
utest mapAll (lam str. geqi (length str) 1) m with true in
utest mapAll (lam str. leqi (length str) 3) m with true in
utest mapAll (lam str. lti (length str) 2) m with false in

let m = mapFromSeq subi
  [ (1, "1")
  , (2, "2")
  , (3, "3")
  ] in
utest
  (mapMapWithKeyK (lam key. lam val. lam k. k (key, val)) m (lam m. mapBindings m))
  with [(1, (1, "1")), (2, (2, "2")), (3, (3, "3"))]
in
utest
  (mapMapK (lam val. lam k. k (join [val, val])) m (lam m. mapBindings m))
  with [(1, "11"), (2, "22"), (3, "33")]
in

let m = mapFromSeq subi [
  (1, "1"),
  (2, "2"),
  (3, "3")
] in
utest mapBindings (mapUpdate 1 (lam. Some "2") m)
  with [(1, "2"), (2, "2"), (3, "3")]
in
utest mapBindings (mapUpdate 4 (lam. Some "4") m)
  with [(1, "1"), (2, "2"), (3, "3"), (4, "4")]
in
utest mapBindings (mapUpdate 1 (lam. None ()) m)
  with [(2, "2"), (3, "3")]
in
utest mapBindings (mapUpdate 4 (lam. None ()) m)
  with [(1, "1"), (2, "2"), (3, "3")]
in
utest
  mapBindings
    (mapUpdate 2
       (lam v. match v with Some v then Some (join [v,v]) else None ())
       m)
  with [(1, "1"), (2, "22"), (3, "3")]
in

utest mapGetMin m with Some (1, "1") in

let m = mapFromSeq subi [
  (1, "1"),
  (2, "2"),
  (3, "3")
] in
utest
  mapBindings (mapFilterWithKey (lam k. lam v. and (gti k 1) (eqString v "3")) m)
  with [(3, "3")]
in

let m = mapFromSeq subi [
  (1, "1"),
  (2, "2"),
  (3, "3")
] in
utest
  mapBindings (mapFilter (lam v. or (eqString v "1") (eqString v "3")) m)
  with [(1, "1"), (3, "3")]
in

let m = mapFromSeq subi [
  (1, "1"),
  (2, "2"),
  (3, "3")
] in
utest
  mapBindings (mapMapOptionWithKey (lam k. lam v. if or (eqString v "1") (eqString v "3") then Some (concat (int2string k) (cons 'x' v)) else None ()) m)
  with [(1, "1x1"), (3, "3x3")]
in

let m = mapFromSeq subi [
  (1, "1"),
  (2, "2"),
  (3, "3")
] in
utest
  mapBindings (mapMapOption (lam v. if or (eqString v "1") (eqString v "3") then Some (cons 'x' v) else None ()) m)
  with [(1, "x1"), (3, "x3")]
in

let cmp = lam a. lam b. if ltf a b then -1 else if gtf a b then 1 else 0 in
let m = mapFromSeq cmp [(0., 0), (1., 1), (2., 2), (3., 3), (4., 4)] in
utest mapFindUpper 4.5 m with None () in
utest mapFindUpper 4. m with Some (4., 4) in
utest mapFindUpper 3.5 m with Some (4., 4) in
utest mapFindUpper 3. m with Some (3., 3) in
utest mapFindUpper 2.5 m with Some (3., 3) in
utest mapFindUpper 2. m with Some (2., 2) in
utest mapFindUpper 1.5 m with Some (2., 2) in
utest mapFindUpper 1. m with Some (1., 1) in
utest mapFindUpper 0.5 m with Some (1., 1) in
utest mapFindUpper 0. m with Some (0., 0) in
utest mapFindLower 4.5 m with Some (4., 4) in
utest mapFindLower 4. m with Some (4., 4) in
utest mapFindLower 3.5 m with Some (3., 3) in
utest mapFindLower 3. m with Some (3., 3) in
utest mapFindLower 2.5 m with Some (2., 2) in
utest mapFindLower 2. m with Some (2., 2) in
utest mapFindLower 1.5 m with Some (1., 1) in
utest mapFindLower 1. m with Some (1., 1) in
utest mapFindLower 0.5 m with Some (0., 0) in
utest mapFindLower 0. m with Some (0., 0) in
utest mapFindLower -1. m with None () in

let m = mapSingleton subi 1 1 in
utest mapSize m with 1 in
utest mapLookup 1 m with Some 1 in

()
