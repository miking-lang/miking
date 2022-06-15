
mexpr
  let r = ref "5" in
  let to10 = lam setter.
    setter "10" in
  to10 (modref r);
  print (deref r)
