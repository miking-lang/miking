include "option.mc"

lang Effect
  -- NOTE(aathn, 2024-02-06): If we had GADTs, we could remove the
  -- Response type in favor of having a Query type with a type
  -- parameter indicating the return type.
  syn Query =
  syn Response =

  type Iso a b =
    { fwd : a -> b, bwd : b -> a }

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
  | ReaderGetQ ()

  syn Response =
  | ReaderGetR Ctx

  sem ask : all a. Iso a Ctx -> Eff a
  sem ask =
  | i -> perform (ReaderGetQ ()) (lam x. match x with ReaderGetR c in i.bwd c)

  sem handleReader : all b. all a. Iso b Ctx -> b -> Eff a -> Eff a
  sem handleReader i ctx =
  | e ->
    let c = i.fwd ctx in
    let handler = lam continue. lam q.
      match q with ReaderGetQ () then
        Some (continue (ReaderGetR c))
      else None ()
    in
    handleEff return handler e
end

lang Writer = Effect
  syn Log =

  syn Query =
  | WriterPutQ Log

  syn Response =
  | WriterPutR ()

  sem tell : all a. Iso a Log -> a -> Eff ()
  sem tell i =
  | l -> perform (WriterPutQ (i.fwd l)) (lam. ())

  sem handleWriter : all a. all b. Iso b Log -> Eff a -> Eff (a, [b])
  sem handleWriter i =
  | e ->
    let handler = lam continue. lam q.
      match q with WriterPutQ l then
        Some (effMap (lam al. (al.0, cons (i.bwd l) al.1)) (continue (WriterPutR ())))
      else None ()
    in
    handleEff (lam x. return (x, [])) handler e
end

lang State = Effect
  syn State =

  syn Query =
  | StateGetQ ()
  | StatePutQ State

  syn Response =
  | StateGetR State
  | StatePutR ()

  sem get : all a. Iso a State -> Eff a
  sem get =
  | i -> perform (StateGetQ ()) (lam x. match x with StateGetR s in i.bwd s)

  sem put : all a. Iso a State -> a -> Eff ()
  sem put i =
  | s -> perform (StatePutQ (i.fwd s)) (lam. ())

  sem handleState : all a. all b. Iso b State -> b -> Eff a -> Eff (a, b)
  sem handleState i s =
  | Pure x -> return (x, s)
  | Impure (q, k) ->
    let continue = lam s. lam r. handleState i s (k r) in
    switch q
    case StateGetQ () then
      continue s (StateGetR (i.fwd s))
    case StatePutQ s then
      continue (i.bwd s) (StatePutR ())
    case _ then
      Impure (q, continue s)
    end
end

lang NonDet = Effect
  syn NDItem =

  syn Query =
  | NDChooseQ [NDItem]

  syn Response =
  | NDChooseR NDItem

  sem choose : all a. [a] -> Eff a
  sem choose =
  | is ->
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

lang TestLang = Reader + NonDet end

mexpr

use TestLang in

con ICtx : Int -> Ctx in
let intCtx : Iso Int Ctx =
  { fwd = lam i. ICtx i
  , bwd = lam c. match c with ICtx i in i }
in

let effProg : Eff Int =
  bind (choose [0,1]) (lam i.
  bind (choose [2,3]) (lam j.
  bind (ask intCtx) (lam k.
  return (addi (addi i j) k))))
in

utest runEff (handleND (handleReader intCtx 7 effProg)) with [9,10,10,11] in
()
