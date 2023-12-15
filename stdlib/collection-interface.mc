include "basic-types.mc"

-- TODO(vipa, 2023-12-06): There are a number of temporary changes
-- made to this file, all with the same date as this comment. These
-- should be undone when reprs are properly supported in the main
-- compiler.

-- This file gives a general interface for collection types.

type UColl p x

type Repr x -- TODO(vipa, 2023-12-06): Remove when reprs are added for real
type Coll p x = Repr (UColl p x)

-- The first thing to note is that `Coll` is a `Repr`-type, meaning
-- that the compiler will choose a concrete representation for each
-- `Coll`-value in the program automatically.
--
-- Collections `Coll p x` have two type parameters: the collection
-- properties `p`, and the element type `x`.  The properties `p`
-- consist of two components, and determine the semantics of
-- operations working over a given collection.  For instance, we may
-- define
-- `type Seq a = Coll (KeepAll, SeqOrder) a`
-- `type Set a = Coll (KeepLast, SortedOrder) a`,
-- for which we expect the following behavior:
--
-- >> append (append (append empty 2) 1) 1 : Seq Int
--    ==> [2, 1, 1]
--
-- >> append (append (append empty 2) 1) 1 : Set Int
--    ==> [1, 2]
--
-- The two components of a collection's properties represent a
-- selection and a permutation, respectively.  Informally, these
-- components relate the elements of a collection to the sequence of
-- values inserted into it.  For the example of sets, whenever a
-- duplicate value is inserted into a set, the old value is discarded,
-- corresponding to the selection `KeepLast` that only keeps the last
-- unique element in the sequence of inserted values.  Similarly, the
-- set keeps its elements in sorted order, corresponding to the
-- permutation `SortedOrder` that sorts the sequence of inserted
-- elements.  We can think of the two components as a pair of
-- functions `f` and `g` on sequences; then intuitively the elements
-- of a collection `c` with these properties will be `g (f xs)`, where
-- `xs` is the sequence of elements inserted into `c`.
--
-- In what follows, whenever the documentation makes statements along
-- the lines of "the elements of `c1` are the elements of `c2`
-- followed by the elements of `c3`", it should be implicitly
-- understood that `c1` may discard or reorder some of these elements
-- depending on the properties it has.

---------------------------
-- Collection properties --
---------------------------

-- Selection properties.

-- KeepAll indicates to keep all values in the insertion history.
-- Seen as a filtering function, this is the identity.
type KeepAll

-- KeepLast indicates to only keep the last occurrence of duplicate
-- values.
type KeepLast

-- KeepLastKey applies to collections of key-value pairs `(k, v)`, and
-- indicates to only keep the last occurrence whenever two pairs have
-- the same keys.
type KeepLastKey

-- Orderings.

-- SeqOrder arranges the values in the order they were originally
-- inserted. Seen as a permutation, this is the identity.
type SeqOrder

-- SortedOrder arranges the values in sorted order.
type SortedOrder

-- SortedKeyOrder applies to collections of key-value pairs `(k, v)`,
-- and arranges them in order sortedy by the keys.
type SortedKeyOrder

-- These first three operations define the semantics of the properties
-- through execution; there should be exactly one implementation of
-- the appropriate `...Sem` operation for each property.

type Phantom a
con Phantom : all a. () -> Phantom a

let orderSem : all o. all a. Phantom o -> [a] -> [Int] = never
let selectSem : all s. all a. Phantom s -> [a] -> a -> [a] -> Bool = never

-----------------------------
-- Collection type aliases --
-----------------------------

type Seq a = Coll (KeepAll, SeqOrder) a

-- type Set a = Coll (KeepLast, _) a  -- TODO(vipa, 2023-12-06): Uncomment when reprs are supported
type OrderedSet a = Coll (KeepLast, SortedOrder) a

-- type Map k v = Coll (KeepLastKey, _) (k, v)  -- TODO(vipa, 2023-12-06): Uncomment when reprs are supported
type OrderedMap k v = Coll (KeepLastKey, SortedKeyOrder) (k, v)

----------------------------
-- Fundamental operations --
----------------------------

-- These should be used to give default implementations for all other operations.

-- `empty` denotes an empty collection with any properties.
let empty : all p. all a. Coll p a
  = never

-- `append_op c a` appends `a` to the elements of `c`.
let append_op
  : all p1. all p2. all a
  .  Coll p1 a
  -> a
  -> Coll p2 a
  = never

let append : all p. all a. Coll p a -> a -> Coll p a = append_op

-- `prepend_op a c` prepends `a` to the elements of `c`.
let prepend_op
  : all p1. all p2. all a
  .  a
  -> Coll p1 a
  -> Coll p2 a
  = never

let prepend : all p. all a. a -> Coll p a -> Coll p a = prepend_op

-- `foldl f acc c` gives `f (... (f (f acc x0) x1) ...) xn`, where
-- `x0, x1, ..., xn` are the elements of `c`.
let foldl
  : all p. all a. all acc
  . (acc -> a -> acc)
  -> acc
  -> Coll p a
  -> acc
  = never

-- `foldr f acc c` gives `f x0 (... (f xn-1 (f xn acc)) ...)`, where
-- `x0, x1, ..., xn` are the elements of `c`.
let foldr
  : all p. all a. all acc
  . (a -> acc -> acc)
  -> acc
  -> Coll p a
  -> acc
  = never

--------------------------
-- Composite operations --
--------------------------

-- Interacting with the built-in sequences

let collFromSeq
  : all p. all a
  . [a]
  -> Coll p a
  = never

-- This function should *only* be called on small literals. It's
-- equivalent with `collFromSeq`, but the cost annotation assumes n=5,
-- which gives it a much lower cost

let q
  : all p. all a
  . [a]
  -> Coll p a
  = never

let seqFromColl
  : all p. all a
  . Coll p a
  -> [a]
  = never

-- Property manipulation

-- `view c` creates a new collection from the elements of `c`, with
-- any properties.  If `p1 = p2`, then we should have `view c = c`.
let view
  : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  = never

-- Monoid

-- `singleton a` is a singleton collection with element `a`, with any properties.
let singleton : all p. all a. a -> Coll p a = never

-- `concat_op c1 c2` creates a new collection whose elements are are
-- the elements of `c1` followed by the elements of `c2`.
let concat_op
  : all p1. all p2. all p3. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Coll p3 a
  = never

let concat
  : all p. all a
  .  Coll p a
  -> Coll p a
  -> Coll p a
  = concat_op

let into
  : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Coll p1 a
  = concat_op

-- Foldable

-- `foldl1 f c` behaves as `foldl f (first c) (tail c)`.
-- WARNING: Errors on empty input.
let foldl1
  : all p. all a
  . (a -> a -> a)
  -> Coll p a
  -> a
  = never

-- `foldr1 f c` behaves as `foldr f (last c) (init c)`.
-- WARNING: Errors on empty input.
let foldr1
  : all p. all a
  . (a -> a -> a)
  -> Coll p a
  -> a
  = never

-- `unfoldl f a0` gives a collection with elements `xn, x(n-1), ..., x0`, where
-- `f ai = Some (xi, a(i+1))` for all `i`.
let unfoldl : all p. all a. all b
  . (a -> Option (b, a))
  -> a
  -> Coll p b
  = never

-- `unfoldr f a0` gives a collection with elements `x0, x1, ..., xn`, where
-- `f ai = Some (xi, a(i+1))` for all `i`.
let unfoldr : all p. all a. all b
  . (a -> Option (b, a))
  -> a
  -> Coll p b
  = never

-- `foldl2_op f acc c1 c2` left folds `f` over the first `k` elements in `c1` and
-- `c2`, accumulating on `acc`, where `k` is the minimum of the two collections'
-- sizes.
let foldl2_op
  : all p1. all p2. all a. all b. all c
  . (a -> b -> c -> a)
  -> a
  -> Coll p1 b
  -> Coll p2 c
  -> a
  = never


let foldl2
  : all p. all a. all b. all c
  . (a -> b -> c -> a)
  -> a
  -> Coll p b
  -> Coll p c
  -> a
  = foldl2_op

-- Functor / applicative

-- `map_op f c` creates a new collection with elements
-- `f x0, f x1, ..., f xn`, where `x0, x1, ..., xn` are the elements
-- of `c`.
let map_op
  : all p1. all p2. all a. all b
  . (a -> b)
  -> Coll p1 a
  -> Coll p2 b
  = never

let map
  : all p. all a. all b
  . (a -> b)
  -> Coll p a
  -> Coll p b
  = map_op

-- `map2_op f c1 c2` gives a new collection with elements
-- `f x0 y0, f x1 y1, ..., f xk yk`, where k = min(m, n),
-- `x0, x1, ..., xn` are the elements of `c1`, and `y0, y1, ... ym`
-- are the elements of `c2`.
let map2_op
  : all p1. all p2. all p3. all a. all b. all c
  . (a -> b -> c)
  -> Coll p1 a
  -> Coll p2 b
  -> Coll p3 c
  = never

let map2
  : all p. all a. all b. all c
  . (a -> b -> c)
  -> Coll p a
  -> Coll p b
  -> Coll p c
  = map2_op

-- TODO(vipa, 2023-10-14): naming, it's actually a deterministic
-- function, but it's amongst other things useful to simulate
-- non-determinism (all possible combinations)

-- `map2_nondet_op f c1 c2` gives a new collection with elements `f xi yj` for
-- all j <= m, i <= n, where `x0, x1, ..., xn` are the elements of `c1`, and
-- `y0, y1, ... ym` are the elements of `c2`.
let map2_nondet_op
  : all p1. all p2. all p3. all a. all b. all c
  . (a -> b -> c)
  -> Coll p1 a
  -> Coll p2 b
  -> Coll p3 c
  = never

let map2_nondet
  : all p. all a. all b. all c
  . (a -> b -> c)
  -> Coll p a
  -> Coll p b
  -> Coll p c
  = map2_nondet_op

-- Monad

-- `concatMap_op f c` constructs a new collection from the
-- concatenation of the collections obtained by mapping `f` over `c`.
let concatMap_op
  : all p1. all p2. all p3. all a. all b
  . (a -> Coll p2 b)
  -> Coll p1 a
  -> Coll p3 b
  = never

let concatMap
  : all p. all a. all b
  . (a -> Coll p b)
  -> Coll p a
  -> Coll p b
  = concatMap_op

-- `join_op c` constructs a new collection from the concatenation of
-- the collections contained in `c`.
let join_op
  : all p1. all p2. all p3. all a
  .  Coll p1 (Coll p2 a)
  -> Coll p3 a
  = never

let join
  : all p. all a
  .  Coll p (Coll p a)
  -> Coll p a
  = join_op

let mapM_op
  : all p1. all p2. all p3. all p4. all a. all b
  . (a -> Coll p1 b)
  -> Coll p2 a
  -> Coll p3 (Coll p4 b)
  = never

let mapM
  : all p. all a. all b
  . (a -> Coll p b)
  -> Coll p a
  -> Coll p (Coll p b)
  = mapM_op

-- Traversable

-- `mapAccumL_op f acc0 c` maps a stateful function over a collection,
-- returning the updated collection and the final state.  In other
-- words, letting `x0, x1, ..., xn` be the elements of `c`, the result
-- is a tuple `(accn, c')`, where `c'` has elements `y0, y1, ..., yn`
-- such that `(acc(i+1), yi) = f acci xi` for all `i`.
let mapAccumL_op
  : all p1. all p2. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p1 b
  -> (a, Coll p2 c)
  = never

let mapAccumL
  : all p. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p b
  -> (a, Coll p c)
  = mapAccumL_op

-- `mapAccumR_op` is analogous to `mapAccumL_op`, but performs a right fold.
let mapAccumR_op
  : all p1. all p2. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p1 b
  -> (a, Coll p2 c)
  = never

let mapAccumR
  : all p. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p b
  -> (a, Coll p c)
  = mapAccumR_op

-- `iter f c` calls `f` on each element of `c`, returning unit.
let iter
  : all p. all a
  . (a -> ())
  -> Coll p a
  -> ()
  = never

-- `iter2 f c1 c2` calls `f xi yi` on each pair of elements `xi` in `c1` and
-- `yi` in `c2`, for all `i` less than the minimum of `c1` and `c2`'s sizes.
let iter2
  : all p1. all p2. all a. all b
  . (a -> b -> ())
  -> Coll p1 a
  -> Coll p2 b
  -> ()
  = never

-- Filtering and predicates

-- `filterMap_op f c` constructs a new collection by mapping `f` over
-- the elements of `c` and discarding `None ()`-values.
let filterMap_op
  : all p1. all p2. all a. all b
  . (a -> Option b)
  -> Coll p1 a
  -> Coll p2 b
  = never

let filterMap
  : all p. all a. all b
  . (a -> Option b)
  -> Coll p a
  -> Coll p b
  = filterMap_op

-- `filter_op f c` constructs a new collection containing those
-- elements of `c` for which `f` returns `true`.
let filter_op
  : all p1. all p2. all a
  . (a -> Bool)
  -> Coll p1 a
  -> Coll p2 a
  = never

let filter
  : all p. all a
  . (a -> Bool)
  -> Coll p a
  -> Coll p a
  = filter_op

-- `any f c` returns `true` if `f` returns `true` for some element of `c`.
let any
  : all p. all a
  . (a -> Bool)
  -> Coll p a
  -> Bool
  = never

-- `every f c` returns `true` if `f` returns `true` for every element of `c`.
let every
  : all p. all a
  . (a -> Bool)
  -> Coll p a
  -> Bool
  = never

-- `findMap f c` returns `Some y` for the first element `x` of `c` such that
-- `f x = Some y`, or returns `None ()` if there is no such `x`.
let findMap
  : all p. all a. all b
  . (a -> Option b)
  -> Coll p a
  -> Option b
  = never

-- `find f c` returns `Some x` for the first element `x` of `c` such that
-- `f x = true`, or returns `None ()` if there is no such `x`.
let find
  : all p. all a
  . (a -> Bool)
  -> Coll p a
  -> Option a
  = never

-- `member x c` returns `true` iff `x` is an element of `c`.
let member
  : all p. all a
  .  a
  -> Coll p a
  -> Bool
  = never

-- `isSubset c1 c2` returns `true` iff every element of `c1` is an element of
-- `c2`.
let isSubset
  : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Bool
  = never

-- `partition_op f c` returns a tuple equivalent to
-- `(filter f c, filter (compose not f) c)`.
let partition_op : all p1. all p2. all p3. all a
  . (a -> Bool)
  -> Coll p1 a
  -> (Coll p2 a, Coll p3 a)
  = never

let partition : all p. all a
  . (a -> Bool)
  -> Coll p a
  -> (Coll p a, Coll p a)
  = partition_op

-- `distinct_op c` removes duplicates of `c`, with preserved ordering.  Keeps
-- first occurrence of an element.
let distinct_op
  : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  = never

let distinct
  : all p. all a
  .  Coll p a
  -> Coll p a
  = distinct_op

-- Size

-- `size c` returns the number of elements of `c`.
let size : all p. all a. Coll p a -> Int
  = never

-- `null c` returns `true` iff `size c` returns 0.
let null : all p. all a. Coll p a -> Bool
  = never

-- Equality and comparison

-- `eqColl c1 c2` returns true iff `xi == yi` and `m == n`, where
-- `x0, x1, ..., xn` and `y0, y1, ..., yn` are the elements of `c1` and `c2`,
-- respectively.
let eqColl
  : all p1. all p2. all a. all b
  .  Coll p1 a
  -> Coll p2 b
  -> Bool
  = never

-- `cmpColl c1 c2` compares collections `c1` and `c2` by lexical ordering.
let cmpColl : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Int
  = never

-- Indexing and order

-- `reverse_op c` creates a collection from `c`'s elements in reverse order.
let reverse_op : all p1. all p2. all a. Coll p1 a -> Coll p2 a
  = never

let reverse : all p. all a. Coll p a -> Coll p a
  = reverse_op

-- `splitAt_op c i` returns a tuple `(c1, c2)`, where `c1` has elements
-- `x0, ..., x(i-1)` and `c2` has elements `xi, ..., xn`, if
-- `x0, x1, ..., xn` are the elements of `c`.
-- WARNING: Errors on `i` less than 0 or greater than n.
let splitAt_op
  : all p1. all p2. all p3. all a
  .  Coll p1 a
  -> Int
  -> (Coll p2 a, Coll p3 a)
  = never

let splitAt
  : all p. all a
  .  Coll p a
  -> Int
  -> (Coll p a, Coll p a)
  = splitAt_op

-- `getAt_op c i` returns `xi`, if `x0, x1, ..., xn` are the elements of `c`.
-- WARNING: Errors on `i` less than 0 or greater than n.
let getAt
  : all p. all a
  .  Coll p a
  -> Int
  -> a
  = never

-- `setAt_op c i a` constructs a collection from `c`, with `xi` replaced by
-- `a`, if `x0, x1, ..., xn` are the elements of `c`.
-- WARNING: Errors on `i` less than 0 or greater than n-1.
let setAt_op
  : all p1. all p2. all a
  .  Coll p1 a
  -> Int
  -> a
  -> Coll p2 a
  = never

let setAt
  : all p. all a
  .  Coll p a
  -> Int
  -> a
  -> Coll p a
  = setAt_op

let splitFirst_op
  : all p1. all p2. all a
  . Coll p1 a
  -> Option (a, Coll p2 a)
  = never

let splitFirst
  : all p. all a
  . Coll p a
  -> Option (a, Coll p a)
  = splitFirst_op

let splitLast_op
  : all p1. all p2. all a
  . Coll p1 a
  -> Option (Coll p2 a, a)
  = never

let splitLast
  : all p. all a
  . Coll p a
  -> Option (Coll p a, a)
  = splitLast_op

-- `first c` is equivalent to `getAt c 0`.
-- WARNING: Errors on empty input.
let first : all p. all a. Coll p a -> a
  = never

-- `last c` is equivalent to `getAt c (subi n 1)`, if `size c = n`.
-- WARNING: Errors on empty input.
let last : all p. all a. Coll p a -> a
  = never

-- `tail_op c` is equivalent to the second component of `splitAt_op c 1`.
-- WARNING: Errors on empty input.
let tail_op : all p1. all p2. all a. Coll p1 a -> Coll p2 a
  = never

let tail : all p. all a. Coll p a -> Coll p a
  = tail_op

-- `init_op c` is equivalent to the first component of
-- `splitAt_op c (subi n 1)`, if `size c = n`.
-- WARNING: Errors on empty input.
let init_op : all p1. all p2. all a. Coll p1 a -> Coll p2 a
  = never

let init : all p. all a. Coll p a -> Coll p a
  = init_op

-- `mapi_op f c` creates a new collection with elements
-- `f 0 x0, f 1 x1, ..., f n xn`, where `x0, x1, ..., xn` are the elements
-- of `c`.
let mapi_op
  : all p1. all p2. all a. all b
  . (Int -> a -> b)
  -> Coll p1 a
  -> Coll p2 b
  = never

let mapi
  : all p. all a. all b
  . (Int -> a -> b)
  -> Coll p a
  -> Coll p b
  = mapi_op

let iteri_op
  : all p1. all p2. all a
  . (Int -> a -> ())
  -> Coll p1 a
  -> ()
  = never

-- `iteri f c` calls `f` on each element of `c` along with its index, returning unit.
let iteri
  : all p. all a
  . (Int -> a -> ())
  -> Coll p a
  -> ()
  = never

-- `create n f` creates a new collection with elements `f 0, f 1, ..., f (n - 1)`.
let create : all p. all a
  .  Int
  -> (Int -> a)
  -> Coll p a
  = never

-- `getRange_op c i j` creates a new collection with elements
-- `xi, x(i+1), ..., x(j-1)` if i < j, else returning an empty collection.
let getRange_op : all p1. all p2. all a
  .  Coll p1 a
  -> Int
  -> Int
  -> Coll p2 a
  = never

let getRange : all p. all a
  .  Coll p a
  -> Int
  -> Int
  -> Coll p a
  = getRange_op

-- `removeFirst_op a c` removes the first occurrence of `a` in `c`.
let removeFirst_op : all p1. all p2. all a
  .  a
  -> Coll p1 a
  -> Coll p2 a
  = never

let removeFirst : all p. all a
  .  a
  -> Coll p a
  -> Coll p a
  = removeFirst_op

-- `isPrefix c1 c2` returns true iff the elements of `c1` are a prefix of
-- those of `c2`.
let isPrefix
  : all p1. all p2. all a. all b
  .  Coll p1 a
  -> Coll p2 b
  -> Bool
  = never

-- `isSuffix c1 c2` returns true iff the elements of `c1` are a suffix of
-- those of `c2`.
let isSuffix
  : all p1. all p2. all a. all b
  .  Coll p1 a
  -> Coll p2 b
  -> Bool
  = never

-- `sort_op c` returns a new collection whose elements are those of `c`,
-- ordered in ascending order.
let sort_op
  : all p1. all p2. all a
  .  Coll p1 a
  -> Coll p2 a
  = never

let sort
  : all p. all a
  .  Coll p a
  -> Coll p a
  = sort_op

-- Key-value operations

-- `lookup k c` returns `Some v` for the first element `(k', v)` in `c` s.t.
-- `k` = `k'`, or `None ()` if no such element exists.
let lookup
  : all p. all k. all v
  .  k
  -> Coll p (k, v)
  -> Option v
  = never

-- `removeKey_op k c` removes the first element `(k', v)` in `c` such that
-- `k` = `k'`, acting like the identity if no such element exists.
let removeKey_op
  : all p1. all p2. all k. all v
  .  k
  -> Coll p1 (k, v)
  -> Coll p2 (k, v)
  = never

let removeKey
  : all p. all k. all v
  .  k
  -> Coll p (k, v)
  -> Coll p (k, v)
  = removeKey_op

-- `hasKey k c` returns true iff there is an element `(k', v)` in `c` such that
-- `k` = `k'`.
let hasKey
  : all p. all k. all v
  .  k
  -> Coll p (k, v)
  -> Bool
  = never

-- `getKeys c` is equivalent to `map_op (lam x. x.0) c`.
let getKeys
  : all p1. all p2. all k. all v
  .  Coll p1 (k, v)
  -> Coll p2 k
  = never

-- `getValues c` is equivalent to `map_op (lam x. x.1) c`.
let getValues
  : all p1. all p2. all k. all v
  .  Coll p1 (k, v)
  -> Coll p2 v
  = never

-- `intersectKeysWith_op f c1 c2` produces a new collection whose keys are the
-- intersection of `c1`'s and `c2`'s.  The value associated with each key will
-- be obtained by combining the corresponding values in `c1` and `c2` using `f`.
-- If `c1` contains duplicates of a key, all will be used; on the other hand,
-- if `c2` contains duplicates, only the first occurrence is considered.  For
-- example, with sequences we expect the following semantics.
--
-- >> intersectKeysWithOp_op addi [(0, 1), (0, 2)] [(0, 10), (0, 20), (1, 30)]
--   ==> [(0, 11), (0, 12)]
let intersectKeysWith_op
  : all p1. all p2. all p3. all k. all a. all b. all c
  . (a -> b -> c)
  -> Coll p1 (k, a)
  -> Coll p2 (k, b)
  -> Coll p3 (k, c)
  = never

let intersectKeysWith
  : all p. all k. all a. all b. all c
  . (a -> b -> c)
  -> Coll p (k, a)
  -> Coll p (k, b)
  -> Coll p (k, c)
  = intersectKeysWith_op

let intersectKeys
  : all p. all k. all a. all b
  .  Coll p (k, a)
  -> Coll p (k, b)
  -> Coll p (k, a)
  = lam c1. lam c2.
  intersectKeysWith (lam a. lam. a) c1 c2

-- `unionKeysWith_op f c1 c2` produces a new collection whose keys are the
-- union of `c1`'s and `c2`'s.  If a key exists in both collections, the value
-- associated with that key will be obtained by combining the corresponding
-- values in `c1` and `c2` using `f`. If `c1` contains duplicates of a key, all
-- will be used; on the other hand, if `c2` contains duplicates, only the first
-- occurrence is considered.  For example, with sequences we expect the
-- following semantics.
--
-- >> unionKeysWith_op addi [(0, 1), (0, 2)] [(0, 10), (0, 20), (1, 30)]
--   ==> [(0, 11), (0, 12), (1, 30)]
let unionKeysWith_op
  : all p1. all p2. all p3. all k. all a. all b. all c
  . (a -> a -> a)
  -> Coll p1 (k, a)
  -> Coll p2 (k, a)
  -> Coll p3 (k, a)
  = never

let unionKeysWith
  : all p. all k. all a. all b. all c
  . (a -> a -> a)
  -> Coll p (k, a)
  -> Coll p (k, a)
  -> Coll p (k, a)
  = unionKeysWith_op

let unionKeys
  : all p. all k. all a. all b
  .  Coll p (k, a)
  -> Coll p (k, a)
  -> Coll p (k, a)
  = lam c1. lam c2.
  unionKeysWith (lam. lam a. a) c1 c2

-- `differenceKeys_op c1 c2` produces a new collection whose keys are those of
-- `c1` which do not occur in `c2`.  If `c1` contains duplicates of a key, both
-- will be preserved.
let differenceKeys_op
  : all p1. all p2. all p3. all k. all a. all b
  .  Coll p1 (k, a)
  -> Coll p2 (k, b)
  -> Coll p3 (k, a)
  = never

let differenceKeys
  : all p. all k. all a. all b
  .  Coll p (k, a)
  -> Coll p (k, b)
  -> Coll p (k, a)
  = differenceKeys_op

-- `mergeKeys_op f c1 c2` produces a new collection similarly to `unionKeys` and
-- `intersectKeys`, but calls `f` for every key in `c1`, passing it
-- `f k (This v1)`, `f k (That v2)`, or `f k (These (v1, v2))` depending on
-- whether the key is present in `c1`, `c2`, or both.  If `c1` contains
-- duplicates of a key, all will be used; on the other hand, if `c2` contains
-- duplicates, only the first occurrence is considered.
let mergeKeys_op
  : all p1. all p2. all p3. all k. all a. all b. all c
  . (k -> These a b -> Option c)
  -> Coll p1 (k, a)
  -> Coll p2 (k, b)
  -> Coll p3 (k, a)
  = never

let mergeKeys
  : all p. all k. all a. all b. all c
  . (k -> These a b -> Option c)
  -> Coll p (k, a)
  -> Coll p (k, b)
  -> Coll p (k, a)
  = mergeKeys_op

-- `mapWithKey_op f c` creates a new collection with elements
-- `f k0 v0, f k1 v1, ..., f kn vn`, where `(k0, v0), (k1, v1), ..., (kn, vn)`
-- are the elements of `c`.
let mapWithKey_op
  : all p1. all p2. all k. all a. all b
  . (k -> a -> b)
  -> Coll p1 (k, a)
  -> Coll p2 (k, b)
  = never

let mapWithKey
  : all p. all k. all a. all b
  . (k -> a -> b)
  -> Coll p (k, a)
  -> Coll p (k, b)
  = mapWithKey_op

-- `mapValues_op f c` is equivalent to `mapWithKey_op (lam. f) c`.
let mapValues_op
  : all p1. all p2. all k. all a. all b
  . (a -> b)
  -> Coll p1 (k, a)
  -> Coll p2 (k, b)
  = never

let mapValues
  : all p. all k. all a. all b
  . (a -> b)
  -> Coll p (k, a)
  -> Coll p (k, b)
  = mapValues_op

-- `mapAccumLWithKey_op f acc0 c` maps a stateful function over a key-value
-- collection, returning the updated collection and the final state.  In other
-- words, letting `(k0, v0), (k1, v1), ..., (kn, vn)` be the elements of `c`,
-- the result is a tuple `(accn, c')`, where `c'` has elements
-- `(k0, u0), (k1, u1), ..., (kn, un)` such that `(acc(i+1), ui) = f acci ki vi`
-- for all `i`.
let mapAccumLWithKey_op
  : all p1. all p2. all k. all a. all b. all c
  . (a -> k -> b -> (a, c))
  -> a
  -> Coll p1 (k, b)
  -> (a, Coll p2 (k, c))
  = never

let mapAccumLWithKey
  : all p. all k. all a. all b. all c
  . (a -> k -> b -> (a, c))
  -> a
  -> Coll p (k, b)
  -> (a, Coll p (k, c))
  = mapAccumLWithKey_op

-- `mapAccumLValues_op f acc c` is equivalent to
-- `mapAccumLWithKey_op (lam a. lam. lam b. f a b) acc c`.
let mapAccumLValues_op
  : all p1. all p2. all k. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p1 (k, b)
  -> (a, Coll p2 (k, c))
  = never

let mapAccumLValues
  : all p. all k. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p (k, b)
  -> (a, Coll p (k, c))
  = mapAccumLValues_op

-- `mapAccumRWithKey_op` is analogous to `mapAccumLWithKey_op`, but performs a
-- right fold.
let mapAccumRWithKey_op
  : all p1. all p2. all k. all a. all b. all c
  . (a -> k -> b -> (a, c))
  -> a
  -> Coll p1 (k, b)
  -> (a, Coll p2 (k, c))
  = never

let mapAccumRWithKey
  : all p. all k. all a. all b. all c
  . (a -> k -> b -> (a, c))
  -> a
  -> Coll p (k, b)
  -> (a, Coll p (k, c))
  = mapAccumRWithKey_op

-- `mapAccumRValues_op` is analogous to `mapAccumRValues_op`, but performs a
-- right fold.
let mapAccumRValues_op
  : all p1. all p2. all k. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p1 (k, b)
  -> (a, Coll p2 (k, c))
  = never

let mapAccumRValues
  : all p. all k. all a. all b. all c
  . (a -> b -> (a, c))
  -> a
  -> Coll p (k, b)
  -> (a, Coll p (k, c))
  = mapAccumRValues_op

-- `filterMapValues_op f c` constructs a new collection of key-value pairs by
-- mapping `f` over the values of `c` and discarding `None ()`-results.
let filterMapValues_op
  : all p1. all p2. all k. all a. all b
  . (a -> Option b)
  -> Coll p1 (k, a)
  -> Coll p2 (k, b)
  = never

let filterMapValues
  : all p. all k. all a. all b
  . (a -> Option b)
  -> Coll p (k, a)
  -> Coll p (k, b)
  = filterMapValues_op

-- `filterValues_op f c` constructs a new collection of key-value pairs
-- containing only those elements of `c` for which `f` returns `true` when
-- applied to the value component.
let filterValues_op
  : all p1. all p2. all k. all a. all b
  . (a -> Bool)
  -> Coll p1 (k, a)
  -> Coll p2 (k, a)
  = never

let filterValues
  : all p. all k. all a. all b
  . (a -> Bool)
  -> Coll p (k, a)
  -> Coll p (k, a)
  = never

-- Set operations

let remove
  : all p. all a
  .  a
  -> Coll p a
  -> Coll p a
  = removeFirst

let add
  : all p. all a
  .  Coll p a
  -> a
  -> Coll p a
  = append

-- `difference_op c1 c2` constructs a new collection containing only those
-- elements of `c1` which do not occur in `c2`.
let difference_op
  : all p1. all p2. all p3. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Coll p3 a
  = never

let difference
  : all p. all a
  .  Coll p a
  -> Coll p a
  -> Coll p a
  = difference_op

-- `intersection_op c1 c2` constructs a new collection containing only those
-- elements of `c1` which also occur in `c2`.
let intersection_op
  : all p1. all p2. all p3. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Coll p3 a
  = never

let intersection
  : all p. all a
  .  Coll p a
  -> Coll p a
  -> Coll p a
  = intersection_op

-- `union_op c1 c2` constructs a new collection containing the elements of `c1`
-- along with any elements of `c2` not in `c1`.  Duplicates of elements in `c2`
-- are discarded.
let union_op
  : all p1. all p2. all p3. all a
  .  Coll p1 a
  -> Coll p2 a
  -> Coll p3 a
  = never

let union
  : all p. all a
  .  Coll p a
  -> Coll p a
  -> Coll p a
  = union_op
