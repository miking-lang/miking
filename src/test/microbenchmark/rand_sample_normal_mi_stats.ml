(* Generates a sequence of randomly sampled floats from N(0,1) *)
let rand_float_gauss_boxmuller_many count =
  let rec helpiter i acc =
    if i == count then acc
    else helpiter (i + 1) (Mi_stats.mi_normal_rng_ 0.0 1.0 :: acc)
  in
  helpiter 0 []

let _ =
  Benchmarkcommon.repeat (fun () ->
      rand_float_gauss_boxmuller_many Rand_sample_n.n )