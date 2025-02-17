include "common.mc"
include "tensor.mc"

let printTensor = lam t.
  printLn (strJoin " " (map int2string (tensorToSeqExn t)))

mexpr

-- Tensors a, b, c, and d are all defined as aliases of the larger tensor t.
-- However, the accelerated expression must rediscover t so that it can
-- recreate the aliasing relation of the provided tensors.

let writeTensors = lam a. lam b. lam c. lam d.
  tensorLinearSetExn b 0 5; -- t = 5 0 0 0
  tensorLinearSetExn c 0 7; -- t = 5 0 0 7
  tensorLinearSetExn d 0 2; -- t = 5 0 2 7
  tensorLinearSetExn a 0 4; -- t = 5 4 2 7
  tensorLinearSetExn a 2 3  -- t = 5 4 2 3
in
let t = tensorCreateCArrayInt [4] (lam i. 0) in
let a = tensorSubExn t 1 3 in
let b = tensorSubExn t 0 2 in
let c = tensorSubExn t 3 1 in
let d = tensorSubExn t 2 1 in
accelerate (loop 1 (lam. ()); writeTensors a b c d)

;

-- Repeat the experiment without acceleration
let t2 = tensorCreateCArrayInt [4] (lam i. 0) in
let a = tensorSubExn t2 1 3 in
let b = tensorSubExn t2 0 2 in
let c = tensorSubExn t2 3 1 in
let d = tensorSubExn t2 2 1 in
writeTensors a b c d;

utest t with t2 using tensorEq eqi in
()
