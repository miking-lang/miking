let ida_ss_tolerances rtol atol = Ida.SStolerances (rtol, atol)

let ida_retcode = function
  | Ida.Success ->
      0
  | Ida.StopTimeReached ->
      1
  | Ida.RootsFound ->
      2
