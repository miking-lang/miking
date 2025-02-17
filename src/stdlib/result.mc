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
con ResultOk : all w. all e. all a.
  { warnings : Map Symbol w, value : a } -> Result w e a
con ResultErr : all w. all e. all a.
  { warnings : Map Symbol w, errors : Map Symbol e } -> Result w e a

let _emptyMap
  : all x. () -> Map Symbol x
  -- TODO(aathn, 2022-01-21): Relax value restriction
  -- TODO(vipa, 2022-01-21): This assumes that sym2hash is a perfect
  -- hash, i.e., that there are no collisions, which is presently true
  -- but might not be in the future.
  = lam. mapEmpty (lam l. lam r. subi (sym2hash l) (sym2hash r))

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
  = lam value. ResultOk { warnings = _emptyMap (), value = value }

utest _prepTest (_ok 1) with ([], Right 1)

-- Produce a single error. Note that this function is not
-- referentially transparent, different invocations produce distinct
-- errors.
let _err
  : all w. all e. all a. e -> Result w e a
  = lam err.
    let id = gensym () in
    ResultErr { warnings = _emptyMap (), errors = mapInsert id err (_emptyMap ()) }

utest match _prepTest (_err 1) with ([], Left [1]) then true else false
with true

-- Produce a single warning. Note that this function is not
-- referentially transparent, different invocations produce distinct
-- warnings.
let _warn
  : all w. all e. w -> Result w e ()
  = lam warn.
    let id = gensym () in
    ResultOk { warnings = mapInsert id warn (_emptyMap ()), value = () }

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
    case ResultOk r then { warnings = r.warnings, errors = (_emptyMap ()) }
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
    case ResultOk {warnings = w, value = v} then ResultOk {warnings = w, value = f v}
    case ResultErr r then ResultErr r
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
utest match _prepTest (_apply (_err 7) (_ok 8)) with ([], Left [7]) then true else false
with true
utest match _prepTest (_apply (_err 7) (_warn 'c')) with (['c'], Left [7]) then true else false
with true
utest _prepTest (_apply (_ok (addi 1)) (_err 8)) with ([], Left [8])
utest match _prepTest (_apply (_err 7) (_err 8)) with ([], Left [7, 8]) then true else false
with true

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
utest
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
with ()

-- Take all warnings and errors from both inputs, but only the value
-- in the second input (if neither input has an error).
let _withAnnotations
  : all w. all e. all a. all b. Result w e a -> Result w e b -> Result w e b
  = lam r1. lam r2. _map2 (lam. lam b. b) r1 r2

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
utest
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
with ()

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
utest
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
with ()

-- Perform a computation on the values present in three `Results` if
-- none is an error. Preserves the errors and warnings of all inputs.
-- Semantically equivalent with:
-- let map5 = lam f. lam a. lam b. lam c. lam d. lam e. apply (apply (apply (apply (map f a) b) c) d) e
let _map5
  : all w. all e. all a1. all a2. all a3. all a4. all a5. all b. (a1 -> a2 -> a3 -> a4 -> a5 -> b) -> Result w e a1 -> Result w e a2 -> Result w e a3 -> Result w e a4 -> Result w e a5 -> Result w e b
  = lam f. lam a. lam b. lam c. lam d. lam e.
    match (a, b, c, d, e) with (ResultOk a, ResultOk b, ResultOk c, ResultOk d, ResultOk e) then
      ResultOk { warnings = mapUnion (mapUnion (mapUnion (mapUnion a.warnings b.warnings) c.warnings) d.warnings) e.warnings, value = f a.value b.value c.value d.value e.value }
    else
      ResultErr (_mergeErrors (_mergeErrors (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c)) (_asError d)) (_asError e))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
utest
  let semantics = lam f. lam a. lam b. lam c. lam d. lam e. _apply (_apply (_apply (_apply (_map f a) b) c) d) e in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. lam d. lam e. (a, b, c, d, e) in
  let eqPair : (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) -> Bool = lam a. lam b. and (and (and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2)) (eqi a.3 b.3)) (eqi a.4 b.4) in
  let eq : Result Char Int (Int, Int, Int, Int, Int) -> Result Char Int (Int, Int, Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. for_ (cons (_ok 4) errs)
          (lam d. for_ (cons (_ok 5) errs)
            (lam e. utest _map5 f a b c d e with semantics f a b c d e using eq in ())))))
with ()

-- Perform a computation on the values of a sequence. Produces a non-error only
-- if all individual computations produce a non-error. Preserves all errors and
-- warnings.
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
    in workOk (_emptyMap ()) []

utest
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
with ()

let _foldlM : all w. all e. all a. all b.
  (a -> b -> (Result w e a)) -> a -> [b] -> Result w e a
  = lam f. lam acc.
    recursive
      let workOK : Map Symbol w -> a -> [b] -> Result w e a
        = lam accWarn. lam acc. lam seq.
          match seq with [hd] ++ tl then
            switch f acc hd
            case ResultOk c then
              workOK (mapUnion accWarn c.warnings) (c.value) tl
            case ResultErr c then
              ResultErr {c with warnings = mapUnion accWarn c.warnings }
            end
          else
            ResultOk { warnings = accWarn, value = acc }
    in workOK (_emptyMap ()) acc

-- Perform a computation on the values of a sequence while simultaneously
-- folding an accumulator over the sequence from the left. Produces a non-error
-- only if all individual computations produce a non-error. All errors and
-- warnings are preserved.
let _mapAccumLM : all w. all e. all a. all b. all c.
  (a -> b -> (a, Result w e c)) -> a -> [b] -> (a, Result w e [c])
  = lam f. lam acc.
    recursive
      let workOK : Map Symbol w -> (a, [c]) -> [b] -> (a, Result w e [c])
        = lam accWarn. lam acc. lam seq.
          match acc with (a, cs) in
          match seq with [b] ++ seq then
            switch f a b
            case (a, ResultOk c) then
              workOK (mapUnion accWarn c.warnings) (a, snoc cs c.value) seq
            case (a, ResultErr c) then
              workErr { c with warnings = mapUnion accWarn c.warnings } a seq
            end
          else
            (a, ResultOk { warnings = accWarn, value = cs })
      let workErr
        : { warnings : Map Symbol w, errors : Map Symbol e }
          -> a
            -> [b]
              -> (a, Result w e [c])
        = lam accErr. lam a. lam seq.
          match seq with [b] ++ seq then
            match f a b with (a, c) in
            workErr (_mergeErrors accErr (_asError c)) a seq
          else
            (a, ResultErr accErr)
    in workOK (_emptyMap ()) (acc, [])

utest
  -- Multiply by 10 and reverse the sequence. Produces error 0 on negative and
  -- warn 'a' on 0.
  let work : [Int] -> Int -> ([Int], Result Char Int Int)
    = lam acc. lam x.
      let acc = cons x acc in
      let x = if lti x 0 then _err 0 else
        let res = _ok (muli x 10) in
        if eqi x 0 then _withAnnotations (_warn 'a') res else res in
      (acc, x) in
  let _prepTest = lam p. (p.0, _prepTest p.1) in
  utest _prepTest (_mapAccumLM work [] [0, 1, 2]) with
    ([2, 1, 0], (['a'], Right [0, 10, 20])) in
  utest _prepTest (_mapAccumLM work [] [0, negi 1, 2, 0]) with
    ([0, 2, negi 1 ,0], (['a', 'a'], Left [0])) in
  utest _prepTest (_mapAccumLM work [] [0, negi 1, negi 2]) with
    ([negi 2, negi 1 ,0], (['a'], Left [0, 0])) in
  utest _prepTest (_mapAccumLM work [] [0, 0, negi 2]) with
    ([negi 2, 0 ,0], (['a', 'a'], Left [0])) in
  ()
with ()

-- Convert a Result to an Option, discarding any information present
-- about warnings or a potential error.
let _toOption
  : all w. all e. all a. Result w e a -> Option a
  = lam r.
    match r with ResultOk x then Some x.value else None ()

-- Perform a computation only if its input is error free. Preserves
-- warnings and errors, but if the input is an error then the action
-- won't run, thus any errors or warnings it would have been produced
-- are not present in the result.
let _bind
  : all w. all e. all a. all b. Result w e a -> (a -> Result w e b) -> Result w e b
  = lam start. lam f.
    switch start
    case ResultOk r then _warns r.warnings (f r.value)
    case ResultErr r then ResultErr r
    end

utest match _prepTest (_bind (_err 0) (lam. _err 1)) with ([], Left [0]) then true else false
with true
utest match _prepTest (_bind (_ok 0) (lam. _err 1)) with ([], Left [1]) then true else false
with true
utest match _prepTest (_bind (_withAnnotations (_warn 'a') (_ok 0)) (lam. _err 1)) with (['a'], Left [1]) then true else false
with true
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
utest
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
with ()

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
utest
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
with ()

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
utest
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
with ()

-- Perform a computation only if its inputs are error free. Preserves
-- warnings and errors, but if the inputs have an error then the
-- action won't run, thus any errors or warnings it would have been
-- produced are not present in the result.
-- Semantically equivalent with:
-- let bind5 = lam a. lam b. lam c. lam d. lam e. lam f. bind (map5 (lam a. lam b. lam c. lam d. lam e. (a, b, c, d, e)) a b c d e) (lam x. f x.0 x.1 x.2 x.3 x.4)
let _bind5
  : all w. all e. all a1. all a2. all a3. all a4. all a5. all b. Result w e a1 -> Result w e a2 -> Result w e a3 -> Result w e a4 -> Result w e a5 -> (a1 -> a2 -> a3 -> a4 -> a5 -> Result w e b) -> Result w e b
  = lam a. lam b. lam c. lam d. lam e. lam f.
    match (a, b, c, d, e) with (ResultOk a, ResultOk b, ResultOk c, ResultOk d, ResultOk e) then
      _warns (mapUnion (mapUnion (mapUnion (mapUnion a.warnings b.warnings) c.warnings) d.warnings) e.warnings) (f a.value b.value c.value d.value e.value)
    else
      ResultErr (_mergeErrors (_mergeErrors (_mergeErrors (_mergeErrors (_asError a) (_asError b)) (_asError c)) (_asError d)) (_asError e))

-- NOTE(vipa, 2022-01-21): Poor man's property based testing, or
-- rather exhaustive testing for small number of posibilities
utest
  let semantics = lam a. lam b. lam c. lam d. lam e. lam f. _bind (_map5 (lam a. lam b. lam c. lam d. lam e. (a, b, c, d, e)) a b c d e) (lam x: (Int, Int, Int, Int, Int). f x.0 x.1 x.2 x.3 x.4) in
  let errs = [_err 1, _err 2, _err 3] in
  let f = lam a. lam b. lam c. lam d. lam e. _withAnnotations (_warn 'a') (_ok (a, b, c, d, e)) in
  let eqPair : (Int, Int, Int, Int, Int) -> (Int, Int, Int, Int, Int) -> Bool = lam a. lam b. and (and (and (and (eqi a.0 b.0) (eqi a.1 b.1)) (eqi a.2 b.2)) (eqi a.3 b.3)) (eqi a.4 b.4) in
  let eq : Result Char Int (Int, Int, Int, Int, Int) -> Result Char Int (Int, Int, Int, Int, Int) -> Bool = lam l. lam r.
    let l = _prepTest l in
    let r = _prepTest r in
    and (eqSeq eqChar l.0 r.0) (eitherEq (eqSeq eqi) eqPair l.1 r.1) in
  for_ (cons (_ok 1) errs)
    (lam a. for_ (cons (_ok 2) errs)
      (lam b. for_ (cons (_ok 3) errs)
        (lam c. for_ (cons (_ok 4) errs)
          (lam d. for_ (cons (_ok 5) errs)
            (lam e. utest _bind5 a b c d e f with semantics a b c d e f using eq in ())))))
with ()


-- Perform a computation only if both elements in the input are error
-- free. Preserves warnings and errors, element-wise, but if the input have an
-- error then the action won't run, thus any errors or warnings it would have
-- been produced are not present in the result.
let _bindParallel2
  : all w1. all e1. all w2. all e2. all a1. all a2. all b1. all b2.
    (Result w1 e1 a1, Result w2 e2 a2)
      -> (a1 -> a2 -> (Result w1 e1 b1, Result w2 e2 b2))
         -> (Result w1 e1 b1, Result w2 e2 b2)
  = lam p. lam f.
    switch p
    case (ResultOk a1, ResultOk a2) then
      match f a1.value a2.value with (b1, b2) in
      (_warns a1.warnings b1, _warns a2.warnings b2)
    case (a1, a2) then
      (ResultErr (_asError a1), ResultErr (_asError a2))
    end

utest
  let flip = lam x. lam y. (_ok y, _ok x) in
  let _prepTest = lam p. (_prepTest p.0, _prepTest p.1) in

  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_bindParallel2 (r1, r2) flip) with
    ((['a'], Right 2), (['b'], Right 1))
  in

  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_bindParallel2 (r1, r2) flip) with
    ((['a'], Left []), (['b'], Left [2]))
  in

  let r1 = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_bindParallel2 (r1, r2) flip) with
    ((['a'], Left [1]), (['b'], Left []))
  in

  let r1 : Result Char Int Int = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_bindParallel2 (r1, r2) flip) with
    ((['a'], Left [1]), (['b'], Left [2]))
  in
  ()
  with ()

-- Selects `r` if it is error free, otherwise selects `f` applied to `()`.
let _orElse : all w. all e. all a. (() -> Result w e a) -> Result w e a -> Result w e a
  = lam f. lam r.
    match r with ResultOk _ then r else f ()

utest
  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_orElse (lam. r2) r1) with (['a'], Right 1) in

  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_orElse (lam. r2) r1) with (['a'], Right 1) in

  let r1 = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_orElse (lam. r2) r1) with (['b'], Right 2) in

  let r1 : Result Char Int Int = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_orElse (lam. r2) r1) with (['b'], Left [2]) in
  ()
with ()

-- Selects `r1` if it is error free, selects `r2` if it is error free and `r1`
-- contains errors. If both `r1` and `r2` contains errors, these are merged. In
-- all cases, warnings are propagated between `r1` and `r2`.
-- NOTE(oerikss, 2023-05-10): We might not want to keep the semantics of the last
-- sentence. On the other-hand, you can use orElse of you do not want share data
-- between `r1` and `r2`.
let _or : all w. all e. all a. Result w e a -> Result w e a -> Result w e a
  = lam r1. lam r2.
    switch (r1, r2)
    case (ResultOk _, ResultOk r2) then _warns r2.warnings r1
    case (ResultOk _, ResultErr r2) then _warns r2.warnings r1
    case (ResultErr r1, ResultOk _) then _warns r1.warnings r2
    case (ResultErr r1, ResultErr r2) then ResultErr (_mergeErrors r1 r2)
    end

utest
  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_or r1 r2) with (['a', 'b'], Right 1) in

  let r1 = _withAnnotations (_warn 'a') (_ok 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_or r1 r2) with (['a', 'b'], Right 1) in

  let r1 = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_ok 2) in
  utest _prepTest (_or r1 r2) with (['a', 'b'], Right 2) in

  let r1 : Result Char Int Int = _withAnnotations (_warn 'a') (_err 1) in
  let r2 = _withAnnotations (_warn 'b') (_err 2) in
  utest _prepTest (_or r1 r2) with (['a', 'b'], Left [1, 2]) in
  ()
with ()

let result =
  -- Constructors
  { ok = _ok
  , err = _err
  , warn = _warn
  -- Destructors
  , consume = _consume
  , toOption = _toOption
  -- Mapping, action produces no new errors or warnings
  , map = _map
  , map2 = _map2
  , map3 = _map3
  , map4 = _map4
  , map5 = _map5
  , apply = _apply
  , withAnnotations = _withAnnotations
  -- Mapping, action can produce new errors and/or warnings
  , bind = _bind
  , bind2 = _bind2
  , bind3 = _bind3
  , bind4 = _bind4
  , bind5 = _bind5
  , bindParallel2 = _bindParallel2
  , mapM = _mapM
  , mapAccumLM = _mapAccumLM
  , foldlM = _foldlM
  -- Conditionals
  , orElse = _orElse
  , or = _or
  }
