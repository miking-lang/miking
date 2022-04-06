include "common.mc"
include "string.mc"

type Rec = {a : Tensor[Float], b : Tensor[Int]}

type Data
con Data_A : Tensor[Float] -> Data
con Data_B : Rec -> Data
con Data_C : Int -> Data

mexpr

let s : [Tensor[Float]] =
  create 100
    (lam. tensorCreateCArrayFloat [10] (lam. 0.0))
in

let r = {
  a = tensorCreateCArrayFloat [5] (lam. 0.0),
  b = tensorCreateCArrayInt [3] (lam. 0)
} in

let t : [Data] = [
  Data_A (tensorCreateCArrayFloat [70] (lam. 0.0)),
  Data_B r,
  Data_C 3
] in

let nonsense : [Tensor[Float]] -> Rec -> [Data] -> () =
  lam s. lam r. lam t.
  ()
in

let updateDataA : [Data] -> () = lam t.
  let n = (let l : [Data] -> Int = length in l) t in
  seqLoop n (lam i : Int.
    let d : Data = get t i in
    match d with Data_A tensor then
      tensorSetExn tensor [17] 3.14;
      tensorSetExn tensor [24] 2.4;
      tensorSetExn tensor [9] 1.0
    else ())
in

let updateSomeTensors : [Tensor[Float]] -> Rec -> [Data] -> () =
  lam s. lam r. lam t.
  let temp : Tensor[Float] = get s 3 in
  tensorSetExn temp [2] 4.5;
  tensorSetExn r.b [1] 4;
  updateDataA t;
  ()
in

let checkUpdated : [Tensor[Float]] -> Rec -> [Data] -> Bool =
  lam s. lam r. lam t.
  let temp : Tensor[Float] = get s 3 in
  let f : Float = tensorGetExn temp [2] in
  if neqf f 4.5 then false else

  let temp : Tensor[Int] = r.b in
  let i : Int = tensorGetExn r.b [1] in
  if neqi i 4 then false else

  true
in

let res : Bool = accelerate (
  parallelLoop 1 (lam i : Int.
    updateSomeTensors s r t);
  let b = checkUpdated s r t in
  parallelLoop 1 (lam i : Int.
    nonsense s r t);
  b
) in

let cpu_res : Bool = checkUpdated s r t in
printLn (if res then "true" else "false");
printLn (if cpu_res then "true" else "false")
