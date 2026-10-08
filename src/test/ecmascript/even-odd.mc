mexpr

recursive
    let even = lam x.
        if eqi x 0
        then true
        else odd (subi x 1)
    let odd = lam x.
        if eqi x 1
        then true
        else even (subi x 1)
in

print (if even 4000000 then "even" else "odd")
