-- Mutual tail recursion, four million deep.
--
-- JavaScript eliminates no tail calls at all, so each step would cost a frame
-- if these two compiled to plain calls. Members of a recursive group that
-- tail-call each other share one loop instead, which is what this depth
-- checks.
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

utest even 4000000 with true in
utest odd 4000001 with true in
()
