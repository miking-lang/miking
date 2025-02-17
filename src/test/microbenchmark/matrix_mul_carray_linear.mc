include "matrix_mul_dense_linear.mc"
include "benchmarkcommon.mc"

mexpr

-- Benchmark
benchmark tensorCreateCArrayFloat matMul ();

-- Test
-- test mat_mul;
-- Expect
-- [
-- 	[0., 1., 2.],
-- 	[3., 4., 5.],
-- 	[6., 7., 8.]
-- ][
-- 	[0., 1., 2.],
-- 	[3., 4., 5.],
-- 	[6., 7., 8.]
-- ][
-- 	[15., 18., 21.],
-- 	[42., 54., 66.],
-- 	[69., 90., 111.]
-- ]
()
