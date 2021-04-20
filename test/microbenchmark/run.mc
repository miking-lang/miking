
recursive
  let repeat = lam f. lam n.
    if eqi n 0 then
      ()
    else
      f();
      repeat f (subi n 1) 
end
