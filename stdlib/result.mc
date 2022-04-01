include "map.mc"
include "either.mc"
include "common.mc"

/-

A `Result w e a` is morally an `Option a` that knows what warnings and
errors arose from producing it. Note the plurality on warnings and
errors: the combinators in this module compute and propagate as many
errors as possible, rather than just bail on the first one.

A value of type `Result w e a` thus contains either:
- One result `a` and zero or more warnings `w`.
- One or more errors `e` and zero or more warnings `w`.

All combinators in this module preserve errors and warnings as far as
possible. However, it's still possible to write expressions that drop
errors. For example, these two functions are identical if both inputs
are ok, but the latter might not report as many errors:

```mcore
let add1
  : all w. all e. Result w e Int -> Result w e Int -> Result w e Int
  = lam a. lam b. result.map2 addi a b

let add2
  : all w. all e. Result w e Int -> Result w e Int -> Result w e Int
  = lam a. lam b. result.bind a (lam a. result.bind b (lam b. result.ok (addi a b)))
```

This is because `bind` cannot run its action if the incoming value is
an error, thus any errors from `b` will not be propagated.

As such, it is recommended to use `bind` as little as possible, and as
late as possible, preferring the various `map` combinators instead
when possible. As a rule of thumb, only use `bind input action` when
errors and warnings produced by `action` are entirely irrelevant if
`input` is an error (e.g., if the action doesn't make sense to do if
the input has an error).

Finally, each result has at most one copy of each warning and
error. To achieve this the `err` and `warn` functions are not
referentially transparent; each separate invocation produces a
distinct error/warning. For example:

```mcore
let a = result.err 1
let b = result.err 1
utest result.consume (result.lift2 addi a a) with ([], Left [1])
utest result.consume (result.lift2 addi a b) with ([], Left [1, 1])
```

-/

type Result w e a
-- NOTE(vipa, 2022-01-21): These constructors are not intended to be
-- public, there are invariants that the outside world is unlikely to
-- preserve.
con ResultOk : { warnings : Map Symbol w, value : a } -> Result w e a
con ResultErr : { warnings : Map Symbol w, errors : Map Symbol e } -> Result w e a

let _emptyMap
  : all x. Map Symbol x
  -- TODO(vipa, 2022-01-21): This assumes that sym2hash is a perfect
  -- hash, i.e., that there are no collisions, which is presently true
  -- but might not be in the future.
  = mapEmpty (lam l. lam r. subi (sym2hash l) (sym2hash r))

-- Produce a value to pattern match on from a result, for when we want
-- to report errors and warnings instead of perform additional
-- computations.
let _consume
  : all w. all e. all a. Result w e a -> ([w], Either [e] a)
  = lam val.
    switch val
    case ResultOk r then (mapValues r.warnings, Right r.value)
    case ResultErr r then (mapValues r.warnings, Left (mapValues r.errors))
    end

-- The order of warnings and errors is not significant, thus we call
-- this function on a result to be compared in a utest to get a stable
-- ordering.
let _prepTest
  : all a. Result Char Int a -> ([Char], Either [Int] a)
  = lam x.
    match _consume x with (w, r) in
    (sort cmpChar w, eitherBiMap (sort subi) identity r)

-- Produce a single value without any warnings or errors. Also known
-- as `pure` or `return`.
let _ok
  : all w. all e. all a. a -> Result w e a
  = lam value. ResultOk { warnings = _emptyMap, value = value }

utest _prepTest (_ok 1) with ([], Right 1)

-- Produce a single error. Note that this function is not
-- referentially transparent, different invocations produce distinct
-- errors.
let _err
  : all w. all e. all a. e -> Result w e a
  = lam err.
    let id = gensym () in
    ResultErr { warnings = _emptyMap, errors = mapInsert id err _emptyMap }

utest _prepTest (_err 1) with ([], Left [1])

-- Produce a single warning. Note that this function is not
-- referentially transparent, different invocations produce distinct
-- warnings.
let _warn
  : all w. all e. w -> Result w e ()
  = lam warn.
    let id = gensym () in
    ResultOk { warnings = mapInsert id warn _emptyMap, value = () }

utest _prepTest (_warn 'a') with (['a'], Right ())

-- Internal. Attach multiple warnings at once to a result.
let _warns
  : all w. all e. all a. Map Symbol w -> Result w e a -> Result w e a
  = lam warns. lam val.
    switch val
    case ResultOk r then ResultOk {r with warnings = mapUnion r.warnings warns}
    case ResultErr r then ResultErr {r with warnings = mapUnion r.warnings warns}
    end

-- Internal. Takes a result, pretends that it's a `ResultErr`, and returns the
-- contained record. Note that the `errors` field can be empty, even
-- though that's not possible for `ResultErr` normally.
let _asError
  : all w. all e. all a. Result w e a -> { warnings : Map Symbol w, errors : Map Symbol e }
  = lam start.
    switch start
    case ResultOk r then { warnings = r.warnings, errors = _emptyMap }
    case ResultErr r then r
    end

-- Internal. Merge the contents of multiple errors together.
let _mergeErrors
  : all w. all e.
  { warnings : Map Symbol w, errors : Map Symbol e } ->
  { warnings : Map Symbol w, errors : Map Symbol e } ->
  { warnings : Map Symbol w, errors : Map Symbol e }
  = lam a. lam b.
    { warnings = mapUnion a.warnings b.warnings, errors = mapUnion a.errors b.errors }

-- Update the value, if any, inside the `Result`. Preserves all errors
-- and warnings.
let _map
  : all w. all e. all a. all b. (a -> b) -> Result w e a -> Result w e b
  = lam f. lam start.
    switch start
    case ResultOk r then ResultOk {r with value = f r.value}
    case ResultErr _ then start
    end

utest _prepTest (_map (addi 1) (_ok 3)) with ([], Right 4)
utest _prepTest (_map (addi 1) (_err 3)) with ([], Left [3])
utest _prepTest (_map (addi 1) (_map (lam. 3) (_warn 'a'))) with (['a'], Right 4)

-- Apply a function in a `Result` to a value in another
-- `Result`. Preserves all errors and warnings.
let _apply
  : all w. all e. all a. all b. Result w e (a -> b) -> Result w e a -> Result w e b
  = lam f. lam a.
    match (f, a) with (ResultOk f, ResultOk a) then
      ResultOk { warnings = mapUnion f.warnings a.warnings, value = f.value a.value }
    else
      ResultErr (_mergeErrors (_asError f) (_asError a))

utest _prepTest (_apply (_ok (addi 1)) (_ok 2)) with ([], Right 3)
utest _prepTest (_apply (_map (lam. lam x. x) (_warn 'a')) (_warn 'b')) with (['a', 'b'], Right ())
utest _prepTest (_apply (_map (lam. addi 1) (_warn 'b')) (_ok 2)) with (['b'], Right 3)
utest _prepTest (_apply (_err 7) (_ok 8)) with ([], Left [7])
utest _prepTest (_apply (_err 7) (_warn 'c')) with (['c'], Left [7])
utest _prepTest (_apply (_ok (addi 1)) (_err 8)) with ([], Left [8])
utest _prepTest (_apply (_err 7) (_err 8)) with ([], Left [7, 8])

-- Perform a computation on the values present in two `Results` if
-- neither is an error. Preserves the errors and warnings of both
-- inputs.
-- Semantically equivalent with:
-- let map2 = lam f. lam a. lam b. apply (map f a) b
let _map2
  : all w. all e. all a1. all a2. all b. (a1 -> a2 -> b) -> Result w e a1 -> Result w e a2 -> Result w e b
  = lam f. lam a. lam b.
    match (a, b) with (ResultOk a, ResultOk b) then
      ResultOk { warnings = mapUnion a.warnings b.warnings, value = f a.value b.value }
    else
      ResultErr (_mergeErrors (_asError a) (_asError b))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam f. lam a. lam b. _apply (_map f a) b in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. (a, b) in
  let eqPair : (Int, Int) -> (Int, Int) -> Bool = lam a. lam b. and (eqi a.0 b.0) (eqi a.1 b.1) in
  let eq : Result Char Int (Int, Int) -> Result Char Int (Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. utest _map2 f a b with semantics f a b using eq in ()))

-- Take all warnings and errors from both inputs, but only the value
-- in the second input (if neither input has an error).
let _withAnnotations
  : all w. all e. all a. all b. Result w e a -> Result w e b -> Result w e b
  = _map2 (lam. lam b. b)

-- Perform a computation on the values present in three `Results` if
-- none is an error. Preserves the errors and warnings of all inputs.
-- Semantically equivalent with:
-- let map3 = lam f. lam a. lam b. lam c. apply (apply (map f a) b) c
let _map3
  : all w. all e. all a1. all a2. all a3. all b. (a1 -> a2 -> a3 -> b) -> Result w e a1 -> Result w e a2 -> Result w e a3 -> Result w e b
  = lam f. lam a. lam b. lam c.
    match (a, b, c) with (ResultOk a, ResultOk b, ResultOk c) then
      ResultOk { warnings = mapUnion (mapUnion a.warnings b.warnings) c.warnings, value = f a.value b.value c.value }
    else
      ResultErr (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam f. lam a. lam b. lam c. _apply (_apply (_map f a) b) c in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. (a, b, c) in
  let eqPair : (Int, Int, Int) -> (Int, Int, Int) -> Bool = lam a. lam b. and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2) in
  let eq : Result Char Int (Int, Int, Int) -> Result Char Int (Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. utest _map3 f a b c with semantics f a b c using eq in ())))

-- Perform a computation on the values present in three `Results` if
-- none is an error. Preserves the errors and warnings of all inputs.
-- Semantically equivalent with:
-- let map4 = lam f. lam a. lam b. lam c. lam d. apply (apply (apply (map f a) b) c) d
let _map4
  : all w. all e. all a1. all a2. all a3. all a4. all b. (a1 -> a2 -> a3 -> a4 -> b) -> Result w e a1 -> Result w e a2 -> Result w e a3 -> Result w e a4 -> Result w e b
  = lam f. lam a. lam b. lam c. lam d.
    match (a, b, c, d) with (ResultOk a, ResultOk b, ResultOk c, ResultOk d) then
      ResultOk { warnings = mapUnion (mapUnion (mapUnion a.warnings b.warnings) c.warnings) d.warnings, value = f a.value b.value c.value d.value }
    else
      ResultErr (_mergeErrors (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c)) (_asError d))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam f. lam a. lam b. lam c. lam d. _apply (_apply (_apply (_map f a) b) c) d in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. lam d. (a, b, c, d) in
  let eqPair : (Int, Int, Int, Int) -> (Int, Int, Int, Int) -> Bool = lam a. lam b. and (and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2)) (eqi a.3 b.3) in
  let eq : Result Char Int (Int, Int, Int, Int) -> Result Char Int (Int, Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. for_ (cons (_ok 4) errs)
          (lam d. utest _map4 f a b c d with semantics f a b c d using eq in ()))))

-- Perform a computation on the values of a list. Produces a non-error
-- only if all individual computations produce a non-error. Preserves
-- all errors and warnings.
let _mapM
  : all w. all e. all a. all b. (a -> Result w e b) -> [a] -> Result w e [b]
  = lam f.
    recursive
      let workOk
        : Map Symbol w -> [b] -> [a] -> Result w e [b]
        = lam accWarn. lam acc. lam list.
          match list with [a] ++ list then
            switch f a
            case ResultOk r then workOk (mapUnion accWarn r.warnings) (snoc acc r.value) list
            case ResultErr r then workErr {r with warnings = mapUnion accWarn r.warnings} list
            end
          else
            ResultOk { warnings = accWarn, value = acc }
      let workErr
        : { warnings : Map Symbol w, errors : Map Symbol e } -> [a] -> Result w e [b]
        = lam acc. lam list.
          match list with [a] ++ list then
            workErr (_mergeErrors acc (_asError (f a))) list
          else
            ResultErr acc
    in workOk _emptyMap []

let #var"" =
  -- Multiply by 10, error 0 on negative, warn 'a' on 0.
  let work : Int -> Result Char Int Int = lam x.
    if lti x 0 then _err 0 else
    let res = _ok (muli x 10) in
    if eqi x 0 then _withAnnotations (_warn 'a') res else res in
  utest _prepTest (_mapM work [0, 1, 2]) with (['a'], Right [0, 10, 20]) in
  utest _prepTest (_mapM work [0, 1, 2, 0]) with (['a', 'a'], Right [0, 10, 20, 0]) in
  utest _prepTest (_mapM work [0, negi 1, 2]) with (['a'], Left [0]) in
  utest _prepTest (_mapM work [0, negi 1, negi 2]) with (['a'], Left [0, 0]) in
  ()

-- Perform a computation only if its input is error free. Preserves
-- warnings and errors, but if the input is an error then the action
-- won't run, thus any errors or warnings it would have been produced
-- are not present in the result.
let _bind
  : all w. all e. all a. all b. Result w e a -> (a -> Result w e b) -> Result w e b
  = lam start. lam f.
    switch start
    case ResultOk r then _warns r.warnings (f r.value)
    case ResultErr _ then start
    end

utest _prepTest (_bind (_err 0) (lam. _err 1)) with ([], Left [0])
utest _prepTest (_bind (_ok 0) (lam. _err 1)) with ([], Left [1])
utest _prepTest (_bind (_withAnnotations (_warn 'a') (_ok 0)) (lam. _err 1)) with (['a'], Left [1])
utest _prepTest (_bind (_withAnnotations (_warn 'a') (_ok 0)) (lam x. _ok (addi x 1))) with (['a'], Right 1)
utest _prepTest (_bind (_withAnnotations (_warn 'a') (_ok 0)) (lam x. _withAnnotations (_warn 'b') (_ok (addi x 1)))) with (['a', 'b'], Right 1)

-- Perform a computation only if its inputs are error free. Preserves
-- warnings and errors, but if the inputs have an error then the
-- action won't run, thus any errors or warnings it would have been
-- produced are not present in the result.
-- Semantically equivalent with:
-- let bind2 = lam a. lam b. lam f. bind (map2 (lam a. lam b. (a, b)) a b) (lam x. f x.0 x.1)
let _bind2
  : all w. all e. all a1. all a2. all b. Result w e a1 -> Result w e a2 -> (a1 -> a2 -> Result w e b) -> Result w e b
  = lam a. lam b. lam f.
    match (a, b) with (ResultOk a, ResultOk b) then
      _warns (mapUnion a.warnings b.warnings) (f a.value b.value)
    else
      ResultErr (_mergeErrors (_asError a) (_asError b))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam a. lam b. lam f. _bind (_map2 (lam a. lam b. (a, b)) a b) (lam x: (Int, Int). f x.0 x.1) in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. _withAnnotations (_warn 'a') (_ok (a, b)) in
  let eqPair : (Int, Int) -> (Int, Int) -> Bool = lam a. lam b. and (eqi a.0 b.0) (eqi a.1 b.1) in
  let eq : Result Char Int (Int, Int) -> Result Char Int (Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. utest _bind2 a b f with semantics a b f using eq in ()))

-- Perform a computation only if its inputs are error free. Preserves
-- warnings and errors, but if the inputs have an error then the
-- action won't run, thus any errors or warnings it would have been
-- produced are not present in the result.
-- Semantically equivalent with:
-- let bind3 = lam a. lam b. lam c. lam f. bind (map3 (lam a. lam b. lam c. (a, b, c)) a b c) (lam x. f x.0 x.1 x.2)
let _bind3
  : all w. all e. all a1. all a2. all a3. all b. Result w e a1 -> Result w e a2 -> Result w e a3 -> (a1 -> a2 -> a3 -> Result w e b) -> Result w e b
  = lam a. lam b. lam c. lam f.
    match (a, b, c) with (ResultOk a, ResultOk b, ResultOk c) then
      _warns (mapUnion (mapUnion a.warnings b.warnings) c.warnings) (f a.value b.value c.value)
    else
      ResultErr (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam a. lam b. lam c. lam f. _bind (_map3 (lam a. lam b. lam c. (a, b, c)) a b c) (lam x: (Int, Int, Int). f x.0 x.1 x.2) in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. _withAnnotations (_warn 'a') (_ok (a, b, c)) in
  let eqPair : (Int, Int, Int) -> (Int, Int, Int) -> Bool = lam a. lam b. and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2) in
  let eq : Result Char Int (Int, Int, Int) -> Result Char Int (Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. utest _bind3 a b c f with semantics a b c f using eq in ())))

-- Perform a computation only if its inputs are error free. Preserves
-- warnings and errors, but if the inputs have an error then the
-- action won't run, thus any errors or warnings it would have been
-- produced are not present in the result.
-- Semantically equivalent with:
-- let bind4 = lam a. lam b. lam c. lam d. lam f. bind (map4 (lam a. lam b. lam c. lam d. (a, b, c, d)) a b c d) (lam x. f x.0 x.1 x.2 x.3)
let _bind4
  : all w. all e. all a1. all a2. all a3. all a4. all b. Result w e a1 -> Result w e a2 -> Result w e a3 -> Result w e a4 -> (a1 -> a2 -> a3 -> a4 -> Result w e b) -> Result w e b
  = lam a. lam b. lam c. lam d. lam f.
    match (a, b, c, d) with (ResultOk a, ResultOk b, ResultOk c, ResultOk d) then
      _warns (mapUnion (mapUnion (mapUnion a.warnings b.warnings) c.warnings) d.warnings) (f a.value b.value c.value d.value)
    else
      ResultErr (_mergeErrors (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c)) (_asError d))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
let #var"" =
  let semantics = lam a. lam b. lam c. lam d. lam f. _bind (_map4 (lam a. lam b. lam c. lam d. (a, b, c, d)) a b c d) (lam x: (Int, Int, Int, Int). f x.0 x.1 x.2 x.3) in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. lam d. _withAnnotations (_warn 'a') (_ok (a, b, c, d)) in
  let eqPair : (Int, Int, Int, Int) -> (Int, Int, Int, Int) -> Bool = lam a. lam b. and (and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2)) (eqi a.3 b.3) in
  let eq : Result Char Int (Int, Int, Int, Int) -> Result Char Int (Int, Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. for_ (cons (_ok 4) errs)
          (lam d. utest _bind4 a b c d f with semantics a b c d f using eq in ()))))

let result =
  -- Constructors
  { ok = _ok
  , err = _err
  , warn = _warn
  -- Destructors
  , consume = _consume
  -- Mapping, action produces no new errors or warnings
  , map = _map
  , map2 = _map2
  , map3 = _map3
  , map4 = _map4
  , apply = _apply
  , withAnnotations = _withAnnotations
  -- Mapping, action can produce new errors and/or warnings
  , bind = _bind
  , bind2 = _bind2
  , bind3 = _bind3
  , bind4 = _bind4
  , mapM = _mapM
  }
