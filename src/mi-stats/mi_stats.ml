type mi_rng

external create_rng : int -> mi_rng = "mi_rng_create"

external mi_normal_lpdf : (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed])
  = "mi_normal_lpdf_wrapped" "mi_normal_lpdf_unwrapped" [@@noalloc]
external mi_normal_rng : (float [@unboxed]) -> (float [@unboxed]) -> mi_rng -> (float [@unboxed])
  = "mi_normal_sample_wrapped" "mi_normal_sample_unwrapped" [@@noalloc]
