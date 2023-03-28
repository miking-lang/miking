let rand_float_gauss_boxmuller_many count =
  let rec helpiter i acc =
    if i == count then acc
    else helpiter (i + 1) (Owl_stats.gaussian_rvs 0.0 1.0 :: acc)
  in
  helpiter 0 []

(* Generates a uniformly random floating point number in the range [0,1) *)
let randFloatUniform _ =
  let upperbound = 1073741823 in
  let x = Random.int upperbound in
  float_of_int x /. float_of_int upperbound

(* Generates a sequence of randomly sampled floats from N(0,1) *)
let randFloatGaussBoxMullerMany count =
  let rec generate acc i =
    if i == count then acc (* even basecase *)
    else
      let u1 = randFloatUniform () in
      let u2 = randFloatUniform () in
      let r = Float.sqrt (-2.0 *. Float.log u1) in
      let theta = 2.0 *. Float.pi *. u2 in
      let z1 = r *. Float.cos theta in
      if i + 1 == count then z1 :: acc (* odd basecase *)
      else
        (* z2 is independent from z1 *)
        let z2 = r *. Float.sin theta in
        generate (z1 :: z2 :: acc) (i + 2)
  in
  generate [] 0

(* Generates/samples a single normally distributed float from N(0,1) *)
let randFloatGaussBoxMuller _ = List.hd (randFloatGaussBoxMullerMany 1)

let _ =
  Benchmarkcommon.repeat (fun () ->
      randFloatGaussBoxMullerMany Rand_sample_n.n )
