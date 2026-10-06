#ifndef MI_NORMAL_HPP
#define MI_NORMAL_HPP

#include <stan/math/prim/prob/normal_lpdf.hpp>
#include <stan/math/prim/prob/normal_rng.hpp>

#include "./mi_rng.hpp"

inline double mi_normal_lpdf(double x, double mu, double sigma) {
   return stan::math::normal_lpdf(x, mu, sigma);
}

inline double mi_normal_rng(double mu, double sigma, mi_rng &rng) {
  return stan::math::normal_rng(mu, sigma, rng);
}

#endif
