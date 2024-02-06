include "option.mc"

lang Effect
  syn Query =
  syn Response =

  syn Eff a =
  | Pure a
  | Impure (Query, Response -> Eff a)

  sem return : all a. a -> Eff a
  sem return =
  | a -> Pure a

  sem flatMap : all a. all b. (a -> Eff b) -> Eff a -> Eff b
  sem flatMap f =
  | Pure x -> f x
  | Impure (q, k) ->
    Impure (q, lam x. flatMap f (k x))

  sem bind : all a. all b. Eff a -> (a -> Eff b) -> Eff b
  sem bind e = | f -> flatMap f e

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

  sem ask =
  | () -> perform (ReaderGetQ ()) (lam x. match x with ReaderGetR c in c)

  sem handleReader : all a. Ctx -> Eff a -> Eff a
  sem handleReader ctx =
  | e ->
    let handler = lam continue. lam q.
      match q with ReaderGetQ () then
        Some (continue (ReaderGetR ctx))
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

  sem tell =
  | l -> perform (WriterPutQ l) (lam. ())

  sem handleWriter : all a. Eff a -> Eff (a, [Log])
  sem handleWriter =
  | e ->
    let handler = lam continue. lam q.
      match q with WriterPutQ l then
        Some (bind (continue (WriterPutR ())) (lam al. (al.0, concat l al.1)))
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

  sem ask =
  | () -> perform (StateGetQ ()) (lam x. match x with StateGetQ s in s)

  sem put =
  | s -> perform (StatePutQ s) (lam. ())

  sem handleState : all a. State -> Eff a -> Eff (a, State)
  sem handleState s =
  | Pure x -> return (x, s)
  | Impure (q, k) ->
    let continue = lam s. lam r. handleState s (k r) in
    switch q
    case StateGetQ () then
      continue s (StateGetR s)
    case StatePutQ s then
      continue s (StatePutR ())
    case _ then
      Impure (q, continue s)
    end
end
