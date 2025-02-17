let foo = lam.
  sleepMs (hole (IntRange {min = 0, max = 100, default = 50}))

mexpr

foo ()
