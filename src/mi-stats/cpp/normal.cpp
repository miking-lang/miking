#include <stan/math/prim/prob/normal_lpdf.hpp>
#include <stan/math/prim/prob/normal_rng.hpp>

#include "./mi_rng.cpp"

#ifdef TEST
#include <caml/fail.h>
#endif

double mi_normal_lpdf(double x, double mu, double sigma) {
  #ifdef TEST
  try {
  #endif
    return stan::math::normal_lpdf(x, mu, sigma);
  #ifdef TEST
  }
  catch (const std::domain_error& str) {
    caml_invalid_argument(str);
  }
  #endif
}

extern "C" CAMLprim double mi_normal_lpdf_unwrapped(double x, double mu, double sigma) {
  return mi_normal_lpdf(x, mu, sigma);
}

extern "C" CAMLprim value mi_normal_lpdf_wrapped(value x, value mu, value sigma) {
  CAMLparam3(x, mu, sigma);
  CAMLreturn(caml_copy_double(mi_normal_lpdf(Double_val(x), Double_val(mu), Double_val(sigma))));
}

double mi_normal_sample(double mu, double sigma, mi_rng &rng) {
  #ifdef TEST
  try {
  #endif
    return stan::math::normal_rng(mu, sigma, rng);
  #ifdef TEST
  }
  catch (const std::domain_error& str) {
    caml_invalid_argument(str);
  }
  #endif
}

extern "C" CAMLprim double mi_normal_sample_unwrapped(double mu, double sigma, value mt) {
  return mi_normal_sample(mu, sigma, Mi_rng_val(mt));
}

extern "C" CAMLprim value mi_normal_sample_wrapped(value mu, value sigma, value mt) {
  CAMLparam3(mu, sigma, mt);
  CAMLreturn(caml_copy_double(mi_normal_sample(Double_val(mu), Double_val(sigma), Mi_rng_val(mt))));
}
