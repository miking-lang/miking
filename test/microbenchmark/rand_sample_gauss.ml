let rand_float_gauss_boxmuller_many count =
  let rec helpiter i acc =
    if i == count then
      acc
    else
      helpiter (i + 1)
               ((Owl_stats.gaussian_rvs 0.0 1.0)::acc)
  in
  helpiter 0 []

let _ = Benchmarkcommon.repeat (fun () -> rand_float_gauss_boxmuller_many Rand_sample_n.n)
