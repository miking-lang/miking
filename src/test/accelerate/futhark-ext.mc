-- Tests that the sin and cos externals are supported by the Futhark backend.
include "math.mc"
include "seq.mc"
mexpr
let s1 = map int2float [0, 1, 7, 12, 14, 9] in
let s2f = accelerate (map sin s1) in
let s3f = accelerate (map cos s2f) in
let s2s = map sin s1 in
let s3s = map cos s2s in
utest s3f with s3s using eqSeq eqf in
()
