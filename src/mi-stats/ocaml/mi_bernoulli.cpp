#ifndef MI_BERNOULLI_CPP
#define MI_BERNOULLI_CPP

#include "../cpp/mi_bernoulli.hpp"
#include "./mi_rng.cpp"

extern "C" CAMLprim double mi_bernoulli_lpmf_unwrapped(value n, double theta) {
  return mi_bernoulli_lpmf(Bool_val(n), theta);
}

extern "C" CAMLprim value mi_bernoulli_lpmf_wrapped(value n, value theta) {
  CAMLparam2(n, theta);
  CAMLreturn(caml_copy_double(mi_bernoulli_lpmf(Bool_val(n), Double_val(theta))));
}

extern "C" CAMLprim value mi_bernoulli_rng_unwrapped(double theta, value mt) {
  return Val_bool(mi_bernoulli_rng(theta, Mi_rng_val(mt)));
}

extern "C" CAMLprim value mi_bernoulli_rng_wrapped(value theta, value mt) {
  CAMLparam2(theta, mt);
  CAMLreturn(Val_bool(mi_bernoulli_rng(Double_val(theta), Mi_rng_val(mt))));
}

#endif
