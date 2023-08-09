-- Example using mutually recursive bindings, which cannot be accelerated using
-- Futhark, as it does not support recursion.

recursive
  let even = lam x.
    if eqi x 0 then true
    else odd (subi x 1)
  let odd = lam x.
    if eqi x 0 then false
    else even (subi x 1)
end

mexpr

let b = accelerate (
  loop 1 (lam. ());
  even 3
) in
utest b with false in

()
