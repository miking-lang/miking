let foo = lam.
  sleepMs (HoleIntRange {min = 0, max = 100, depth = 0, default = 50})

mexpr

foo ()
