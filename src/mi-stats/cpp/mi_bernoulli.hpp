#ifndef MI_BERNOULLI_HPP
#define MI_BERNOULLI_HPP

#include <stan/math/prim/prob/bernoulli_lpmf.hpp>
#include <stan/math/prim/prob/bernoulli_rng.hpp>

#include "./mi_rng.hpp"

inline double mi_bernoulli_lpmf(int n, double theta) {
  return stan::math::bernoulli_lpmf(n, theta);
}

inline int mi_bernoulli_rng(double theta, mi_rng &rng) {
  return stan::math::bernoulli_rng(theta, rng);
}

#endif
