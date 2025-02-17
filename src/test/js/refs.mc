include "common.mc"

mexpr
  let r = ref "5" in
  let to10 = lam r. modref r "10" in
  to10 r;
  printLn (deref r);
  ()
