include "common.mc"

lang NumberLang
  syn Number =
  | Integer Int
  | FP Float

  sem addNumber : Float -> Number -> Float
  sem addNumber (lhs : Float) =
  | Integer a -> addf lhs (int2float a)
  | FP a -> addf lhs a
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
end

mexpr

use NumberLangExtra in

let n = 100 in
let s : [Number] = create n (lam. randNumber ()) in

let x : Float = accelerate (
  (let f : (Float -> Number -> Float) -> Float -> [Number] -> Float = foldl in f)
    addNumber 0.0 s) in
printLn (join ["Result = ", float2string x, " ", float2string (foldl addNumber 0.0 s)])
