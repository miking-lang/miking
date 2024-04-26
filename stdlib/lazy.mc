include "option.mc"

type LazyContainer a
con LazyVal : all a. a -> LazyContainer a
con LazyFunc : all a. (() -> a) -> LazyContainer a

type Lazy a = Ref (LazyContainer a)

let lazy : all a. (() -> a) -> Lazy a
  = lam f. ref (LazyFunc f)

let lazyForce : all a. Lazy a -> a
  = lam l.
    switch deref l
    case LazyVal a then a
    case LazyFunc f then
      let res = f () in
      modref l (LazyVal res);
      res
    end

let lazyMap : all a. all b. (a -> b) -> Lazy a -> Lazy b
  = lam f. lam l.
    lazy (lam. f (lazyForce l))

type StreamNode a
con SNil : all a. () -> StreamNode a
con SCons : all a. (a, Lazy (StreamNode a)) -> StreamNode a
type LStream a = Lazy (StreamNode a)

let lazyStreamEmpty : all a. () -> LStream a
  = lam. ref (LazyVal (SNil ()))

let lazyStreamSingleton : all a. a -> LStream a
  = lam a. ref (LazyVal (SCons (a, lazyStreamEmpty ())))

let lazyStream : all acc. all a. (acc -> Option (acc, a)) -> acc -> LStream a
  = lam f. lam acc.
    recursive let goNext = lam acc.
      match f acc with Some (acc, a) then
        SCons (a, lazy (lam. goNext acc))
      else SNil () in
    lazy (lam. goNext acc)

let lazyStreamLaziest : all acc. all a. (acc -> Option (() -> acc, a)) -> (() -> acc) -> LStream a
  = lam f. lam acc.
    recursive let goNext = lam acc.
      match f acc with Some (acc, a) then
        SCons (a, lazy (lam. goNext (acc ())))
      else SNil () in
    lazy (lam. goNext (acc ()))

let lazyStreamWithInit : all acc. all a. (() -> acc) -> (acc -> Option (acc, a)) -> LStream a
  = lam init. lam f.
    recursive let goNext = lam acc.
      match f acc with Some (acc, a) then
        SCons (a, lazy (lam. goNext acc))
      else SNil () in
    lazy (lam. goNext (init ()))

let lazyStreamUncons : all a. LStream a -> Option (a, LStream a)
  = lam s.
    switch lazyForce s
    case SCons (h, t) then Some (h, t)
    case SNil _ then None ()
    end

let lazyStreamMap : all a. all b. (a -> b) -> LStream a -> LStream b
  = lam f. lam s.
    recursive let work = lam s.
      let body = lam.
        match lazyStreamUncons s with Some (a, as)
        then SCons (f a, work as)
        else SNil () in
      lazy body
    in work s

let lazyStreamMapOption : all a. all b. (a -> Option b) -> LStream a -> LStream b
  = lam f. lam s.
    recursive let work = lam s.
      switch s
      case SCons (h, ss) then
        match f h with Some h
        then SCons (h, lazyMap work ss)
        else work (lazyForce ss)
      case SNil _ then
        SNil ()
      end
    in lazyMap work s

-- OPT(vipa, 2023-11-30): This could probably be more efficient with
-- some extra initialization, maybe putting all the things in a Heap
let lazyStreamMergeMin : all a. (a -> a -> Int) -> [LStream a] -> LStream a
  = lam cmp. lam streams.
    let step = lam streams.
      let f = lam acc : (Option {here : a, tail : LStream a, full : LStream a}, [LStream a]). lam stream.
        match lazyStreamUncons stream with Some (here, tail) then
          match acc.0 with Some prev then
            if lti (cmp here prev.here) 0 then
              (Some {here = here, tail = tail, full = stream}, snoc acc.1 prev.full)
            else (acc.0, snoc acc.1 stream)
          else (Some {here = here, tail = tail, full = stream}, acc.1)
        else acc in
      match foldl f (None (), []) streams with (Some min, streams) then
        Some (snoc streams min.tail, min.here)
      else None ()
    in lazyStream step streams

let lazyStreamStatefulFilterMap : all a. all b. all acc. (acc -> a -> (acc, Option b)) -> acc -> LStream a -> LStream b
  = lam f. lam acc. lam s.
    recursive let step = lam acc : {stream : LStream a, acc : acc}.
      match lazyStreamUncons acc.stream with Some (a, as) then
        switch f acc.acc a
        case (acc, Some b) then
          Some ({acc = acc, stream = as}, b)
        case (acc, None _) then
          step {acc = acc, stream = as}
        end
      else None ()
    in lazyStream step {acc = acc, stream = s}

let lazyStreamStatefulFilter : all a. all acc. (acc -> a -> (acc, Bool)) -> acc -> LStream a -> LStream a
  = lam f. lam acc. lam s.
    lazyStreamStatefulFilterMap (lam acc. lam a. match f acc a with (acc, keep) in (acc, if keep then Some a else None ())) acc s

let lazyStreamForceAll : all a. LStream a -> [a]
  = lam s.
    recursive let work = lam acc. lam s.
      match lazyStreamUncons s with Some (x, s)
      then work (snoc acc x) s
      else acc
    in work [] s

type IterNode a
type Iter a = () -> IterNode a
con INNil : all a. () -> IterNode a
con INCons : all a. (a, Iter a) -> IterNode a

let iterEmpty : all a. Iter a = lam. INNil ()
let iterCons : all a. a -> Iter a -> Iter a = lam a. lam it. lam. INCons (a, it)
let iterSingle : all a. a -> Iter a = lam a. iterCons a iterEmpty

recursive let iterConcat : all a. Iter a -> Iter a -> Iter a
  = lam a. lam b. lam. switch a ()
    case INNil _ then b ()
    case INCons (a, aNext) then INCons (a, iterConcat aNext b)
    end
end

recursive let iterMap : all a. all b. (a -> b) -> Iter a -> Iter b
  = lam f. lam xs. lam. switch xs ()
    case INNil _ then INNil ()
    case INCons (x, xs) then INCons (f x, iterMap f xs)
    end
end

recursive let iterConcatMap : all a. all b. (a -> Iter b) -> Iter a -> Iter b
  = lam f. lam xs. lam. switch xs ()
    case INNil _ then INNil ()
    case INCons (x, xs) then iterConcat (f x) (iterConcatMap f xs) ()
    end
end

let iterUncons : all a. Iter a -> Option (a, Iter a)
  = lam it. switch it ()
    case INNil _ then None ()
    case INCons (x, xs) then Some (x, xs)
    end

recursive let iterTake : all a. Int -> Iter a -> Iter a
  = lam limit. lam it. lam.
    if leqi limit 0 then INNil () else
    switch it ()
    case INNil _ then INNil ()
    case INCons (x, xs) then INCons (x, iterTake (subi limit 1) xs)
    end
end

let iterMin : all a. (a -> a -> Int) -> Iter a -> Option a
  = lam cmp. lam it.
    recursive let work = lam acc. lam it. switch it ()
      case INNil _ then acc
      case INCons (x, xs) then
        work (if lti (cmp acc x) 0 then acc else x) xs
      end in
    switch it ()
    case INNil _ then None ()
    case INCons (x, xs) then Some (work x xs)
    end
