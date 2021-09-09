

external myExternalExp : Float -> Float

external externalBinomialLogPmf : Float -> Float -> Int -> Float
let binomialLogPmf = lam p:Float. lam n:Int. lam x:Float. externalBinomialLogPmf x p n

mexpr

utest binomialLogPmf 0.6 1 0.5 with 0.0 in
()
