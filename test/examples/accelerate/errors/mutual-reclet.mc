-- Example using mutually recursive bindings, which cannot be accelerated as
-- Futhark does not support recursion.

recursive
  let even = lam x.
    if eqi x 0 then true
    else odd (subi x 1)
  let odd = lam x.
    if eqi x 0 then false
    else even (subi x 1)
end

mexpr

if even 3 then print "3 is even\n"
else print "3 is not even\n"
