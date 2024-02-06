lang Effect
  syn Req a =

  syn Eff a =
  | Pure a
  -- Encoding existentials using forall
  | Impure (all r. (all b. (Req b, b -> Eff a) -> r) -> r)

  sem return : all a. a -> Eff a
  sem return =
  | a -> Pure a

  sem flatMap : all a. all b. (a -> Eff b) -> Eff a -> Eff b
  sem flatMap f =
  | Pure x -> f x
  | Impure content ->
    let newContent : all r. (all c. (Req c, c -> Eff b) -> r) -> r =
      lam k.
        let compute : all d. (Req d, d -> Eff a) -> r = lam input.
          match input with (u, g) in
          k (u, lam x. bind (g x) f)
        in
        content #frozen"compute"
    in
    Impure #frozen"newContent"

  sem bind : all a. all b. Eff a -> (a -> Eff b) -> Eff b
  sem bind e = | f -> flatMap f e

  sem send : all a. Req a -> Eff a
  sem send =
  | req ->
    let content : all r. (all c. (Req c, c -> Eff a) -> r) -> r =
      lam k. k (req, return)
    in
    Impure #frozen"content"

  sem runEffect : all a. all b. (a -> Eff b) -> (all v. (v -> Eff b) -> Req v -> Eff b) -> Eff a -> Eff b
  sem runEffect ret h =
  | Pure x -> ret x
  | Impure content ->
    let compute : all c. (Req c, c -> Eff a) -> b = lam input.
      match input with (u, q) in
      h u (lam x. runEffect ret h (q x))
    in
    content #frozen"compute"
end

lang Reader = Effect
  syn Req a =
  | Get ()

  sem get =
  | () -> Get ()

end
