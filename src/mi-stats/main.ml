type mi_rng

external create_rng : int -> mi_rng = "mi_rng_create"
(* external sample : mi_rng -> float = "mi_rng_sample" *)

external mi_normal_lpdf : (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed])
  = "mi_normal_lpdf_wrapped" "mi_normal_lpdf_unwrapped" [@@noalloc]
external mi_normal_rng : (float [@unboxed]) -> (float [@unboxed]) -> mi_rng -> (float [@unboxed])
  = "mi_normal_rng_wrapped" "mi_normal_rng_unwrapped" [@@noalloc]

let () =
  let rng = create_rng 2 in
  let s1 = mi_normal_rng 0.0 1.0 rng in
  let s2 = mi_normal_rng 0.0 1.0 rng in
  print_float s1;
  print_endline "";
  print_float s2;
  print_endline "";
  print_float (mi_normal_lpdf 0.0 0.0 1.0);
  print_endline "";
  Gc.full_major ();
  ()
