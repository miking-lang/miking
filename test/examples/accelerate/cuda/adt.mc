include "common.mc"

lang NumberLang
  syn Number =
  | Integer Int
  | FP Float

  sem addNumber : Float -> Number -> Float
  sem addNumber (lhs : Float) =
  | Integer a -> addf lhs (int2float a)
  | FP a -> addf lhs a

  sem toFloat : Number -> Float
  sem toFloat =
  | Integer a -> int2float a
  | FP a -> a
end

lang NumberLangExtra = NumberLang
  syn Number =
  | Pair (Int, Float)

  sem randNumber : () -> Number
  sem randNumber =
  | () ->
    let r = randIntU 0 100 in
    let x = randIntU 0 3 in
    let f = divf 1.0 (int2float (addi r 1)) in
    match x with 0 then Integer r
    else match x with 1 then FP f
    else match x with 2 then Pair (r, f)
    else never

  sem addNumber (lhs : Float) =
  | Pair p ->
    match p with (x, y) in
    addf (addf lhs y) (int2float x)

  sem toFloat : Number -> Float
  sem toFloat =
  | Pair p -> addf (int2float p.0) p.1
end

let tensorSetFloat : Tensor[Float] -> [Int] -> Float -> () =
  lam t. lam idx. lam v.
  (let s : Tensor[Float] -> [Int] -> Float -> () = tensorSetExn in s) t idx v

let tensorGetFloat : Tensor[Float] -> [Int] -> Float =
  lam t. lam idx.
  (let g : Tensor[Float] -> [Int] -> Float = tensorGetExn in g) t idx

mexpr

use NumberLangExtra in

let n = 100 in
let s : [Number] = create n (lam. randNumber ()) in
let t : Tensor[Float] = tensorCreateCArrayFloat [1] (lam. 0.0) in

let x : Float = accelerate (
  -- Use a parallelLoop to force copying of data to GPU. Later in the code it
  -- is then used on the CPU, thus forcing the compiler to generate code for
  -- copying it back.
  parallelLoop 1 (lam i : Int.
    let n : Number = (let g : [Number] -> Int -> Number = get in g) s i in
    let y : Float = toFloat n in
    tensorSetFloat t [i] y;
    ());
  let y : Float = tensorGetFloat t [0] in
  addf
    y
    ((let f : (Float -> Number -> Float) -> Float -> [Number] -> Float = foldl in f)
      addNumber 0.0 s)) in
let x_cpu : Float = addf (toFloat (get s 0)) (foldl addNumber 0.0 s) in
printLn (join ["Result = ", float2string x, " ", float2string x_cpu])
