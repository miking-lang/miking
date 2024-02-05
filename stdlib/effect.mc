lang Effect
  syn Eff a =
  | Return a
  | Bind (Eff a, a -> Eff b)

  sem return : a -> Eff a
  sem return =
  | a -> Return a

  sem bind : Eff a -> (a -> Eff b) -> Eff b
  sem bind e =
  | f -> Bind (e, f)
end

lang Reader = Effect
  syn Eff a =
  | Get ()

  sem get =
  | () -> Get ()

end
