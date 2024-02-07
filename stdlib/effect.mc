include "option.mc"
include "either.mc"

lang Effect
  -- NOTE(aathn, 2024-02-06): If we had GADTs, we could remove the
  -- Response type in favor of having a parameterized Query type where
  -- the parameter indicates the return type.
  syn Query =
  syn Response =

  syn Eff a =
  | Pure a
  | Impure (Query, Response -> Eff a)

  sem return : all a. a -> Eff a
  sem return =
  | a -> Pure a

  sem bind : all a. all b. Eff a -> (a -> Eff b) -> Eff b
  sem bind e = | f -> effJoinMap f e

  sem effJoinMap : all a. all b. (a -> Eff b) -> Eff a -> Eff b
  sem effJoinMap f =
  | Pure x -> f x
  | Impure (q, k) ->
    Impure (q, lam x. effJoinMap f (k x))

  sem effMap : all a. all b. (a -> b) -> Eff a -> Eff b
  sem effMap f = | e -> effJoinMap (lam x. return (f x)) e

  sem effMap2 : all a. all b. all c. (a -> b -> c) -> Eff a -> Eff b -> Eff c
  sem effMap2 f e1 = | e2 ->
    effJoinMap (lam g. effMap g e2) (effMap f e1)

  sem effMapM : all a. all b. (a -> Eff b) -> [a] -> Eff [b]
  sem effMapM f = | l ->
    foldl (lam acc. lam x. effMap2 snoc acc (f x)) (return []) l

  sem perform : all a. Query -> (Response -> a) -> Eff a
  sem perform q =
  | k ->
    Impure (q, lam r. return (k r))

  sem handleEff
    : all a. all b. (a -> Eff b)
    -> ((Response -> Eff b) -> Query -> Option (Eff b))
    -> Eff a
    -> Eff b
  sem handleEff ret h =
  | Pure x -> ret x
  | Impure (q, k) ->
    let continue = lam r. handleEff ret h (k r) in
    optionGetOr (Impure (q, continue)) (h continue q)

  sem runEff : all a. Eff a -> a
  sem runEff =
  | Pure x -> x
end

lang Reader = Effect
  syn Ctx =

  syn Query =
  | ReaderAskQ ()

  syn Response =
  | ReaderAskR Ctx

  sem ask : all a. (Ctx -> a) -> Eff a
  sem ask =
  | proj -> perform (ReaderAskQ ()) (lam x. match x with ReaderAskR c in proj c)

  sem local : all a. all b. (b -> Ctx -> Ctx) -> b -> Eff a -> Eff a
  sem local update b =
  | Pure x -> Pure x
  | Impure (q, k1) ->
    let k2 = lam r. local update b (k1 r) in
    match q with ReaderAskQ _ then
      Impure (q, lam r. match r with ReaderAskR c in k2 (ReaderAskR (update b c)))
    else Impure (q, k2)

  sem handleReader : all a. Ctx -> Eff a -> Eff a
  sem handleReader ctx =
  | e ->
    let handler = lam continue. lam q.
      match q with ReaderAskQ () then
        Some (continue (ReaderAskR ctx))
      else None ()
    in
    handleEff return handler e
end

lang Writer = Effect
  syn Log =

  syn Query =
  | WriterTellQ Log

  syn Response =
  | WriterTellR ()

  sem tell : all a. Log -> Eff ()
  sem tell =
  | l -> perform (WriterTellQ l) (lam. ())

  sem handleWriter : all a. all b. (Log -> b) -> Eff a -> Eff (a, [b])
  sem handleWriter proj =
  | e ->
    let handler = lam continue. lam q.
      match q with WriterTellQ l then
        Some (effMap (lam al. (al.0, cons (proj l) al.1)) (continue (WriterTellR ())))
      else None ()
    in
    handleEff (lam x. return (x, [])) handler e
end

lang State = Effect
  syn State =

  syn Query =
  | StateGetQ ()
  | StatePutQ (State -> State)

  syn Response =
  | StateGetR State
  | StatePutR ()

  sem get : all a. (State -> a) -> Eff a
  sem get =
  | proj -> perform (StateGetQ ()) (lam x. match x with StateGetR s in proj s)

  sem put : all a. (a -> State -> State) -> a -> Eff ()
  sem put update =
  | a -> perform (StatePutQ (update a)) (lam. ())

  sem handleState : all a. all b. (State -> b) -> State -> Eff a -> Eff (a, b)
  sem handleState proj s =
  | Pure x -> return (x, proj s)
  | Impure (q, k) ->
    let continue = lam s. lam r. handleState proj s (k r) in
    switch q
    case StateGetQ () then
      continue s (StateGetR s)
    case StatePutQ f then
      continue (f s) (StatePutR ())
    case _ then
      Impure (q, continue s)
    end
end

lang NonDet = Effect
  syn NDItem =

  -- NOTE(aathn, 2024-02-07): If we had GADTs, we wouldn't need this
  -- NDItem type, we could simply have
  -- NDChooseQ : all a. [a] -> Query a.
  syn Query =
  | NDChooseQ [NDItem]

  syn Response =
  | NDChooseR NDItem

  sem choose : all a. [a] -> Eff a
  sem choose =
  | is ->
    -- NOTE(aathn, 2024-02-07): We cheat by defining a local
    -- constructor which will escape its scope -- this is safe since
    -- it will always be handled by the corresponding continuation,
    -- but it would be rejected by the new typechecker, and it would
    -- be unnecessary if we had GADTs as stated above.
    con Item : a -> NDItem in
    perform
      (NDChooseQ (map (lam i. Item i) is))
      (lam x. match x with NDChooseR (Item i) in i)

  sem handleND : all a. Eff a -> Eff [a]
  sem handleND =
  | e ->
    let handler = lam continue. lam q.
      match q with NDChooseQ is then
        let f = lam acc. lam i. effMap2 concat acc (continue (NDChooseR i)) in
        Some (foldl f (return []) is)
      else None ()
    in
    handleEff (lam x. return [x]) handler e
end

lang Failure = Effect
  syn Failure =

  syn Query =
  | FailQ Failure

  syn Response =

  sem fail : all a. Failure -> Eff a
  sem fail =
  | a ->
    perform (FailQ a) (lam. error "failed branch was executed!")

  sem handleFail : all a. all b. (Failure -> b) -> Eff a -> Eff (Either b a)
  sem handleFail proj =
  | e ->
    let handler = lam. lam q.
      match q with FailQ f then
        Some (return (Left (proj f)))
      else None ()
    in
    handleEff (lam x. return (Right x)) handler e
end

lang TestLang = Reader + NonDet
  sem getInt : Ctx -> Int
  sem addInt : Int -> Ctx -> Ctx

  sem effProg : () -> Eff Int
  sem effProg = | () ->
    local addInt 3
      (bind (choose [0,1]) (lam i.
      bind (choose [2,3]) (lam j.
      bind (ask getInt) (lam k.
      return (addi (addi i j) k)))))
end

lang TestLangImpl = TestLang
  syn Ctx = | ICtx Int
  sem getInt = | ICtx i -> i
  sem addInt j = | ICtx i -> ICtx (addi j i)
end

mexpr

use TestLangImpl in

utest runEff (handleND (handleReader (ICtx 7) (effProg ())))
with [12,13,13,14] in

()
