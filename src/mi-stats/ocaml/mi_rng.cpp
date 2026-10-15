#ifndef MI_RNG_CPP
#define MI_RNG_CPP

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/custom.h>
#include <caml/fail.h>

#include "../cpp/mi_rng.hpp"

// Get an lvalue for an rng thing from an OCaml value
#define Mi_rng_val(v) (*(mi_rng*)Data_custom_val(v))

static void mi_rng_finalize(value mi_rng_v) {
  // Pairs with the placement new in mi_rng_create; the GC owns the storage itself.
  Mi_rng_val(mi_rng_v).~mi_rng();
}

static struct custom_operations mi_rng_ops {
  "mi_rng_handle",
  mi_rng_finalize,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

extern "C" CAMLprim value mi_rng_create(value seed) {
  CAMLparam1(seed);
  CAMLlocal1(v);
  v = caml_alloc_custom(&mi_rng_ops, sizeof(mi_rng), 0, 1);
  new (Data_custom_val(v)) mi_rng(Long_val(seed));
  CAMLreturn(v);
}

#endif
