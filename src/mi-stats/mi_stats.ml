type mi_rng

external create_rng : int -> mi_rng = "mi_rng_create"

let global_rng = ref (create_rng 0)

let mi_set_seed : int -> unit = fun seed -> global_rng := create_rng seed


external mi_normal_lpdf : (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed]) -> (float [@unboxed])
  = "mi_normal_lpdf_wrapped" "mi_normal_lpdf_unwrapped" [@@noalloc]
external mi_normal_rng : (float [@unboxed]) -> (float [@unboxed]) -> mi_rng -> (float [@unboxed])
  = "mi_normal_sample_wrapped" "mi_normal_sample_unwrapped" [@@noalloc]
let mi_normal_rng_ : float -> float -> float = fun a b -> mi_normal_rng a b !global_rng
