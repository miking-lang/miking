let foo = lam.
  sleepMs (holeIntRange {min = 0, max = 100, depth = 0, default = 50})

mexpr

foo ()
