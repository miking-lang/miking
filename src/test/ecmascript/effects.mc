-- References, symbols and tensors.
--
-- `ref` in the standard library is a rank-0 tensor, so these exercise the same
-- machinery: `tensorCreateDense [] (lam. x)` with get and set at index [].
include "ref.mc"
include "tensor.mc"

mexpr

-- References.
let r = ref 1 in
utest deref r with 1 in
modref r 42;
utest deref r with 42 in

-- A reference captured by a closure is shared, not copied.
let bump = lam. modref r (addi (deref r) 1) in
bump (); bump ();
utest deref r with 44 in

-- Symbols are distinct and compare by identity.
let a = gensym () in
let b = gensym () in
utest eqsym a a with true in
utest eqsym a b with false in

-- Tensors. Indexing is row-major.
let m = tensorCreateDense [2, 3] (lam idx. addi (muli 10 (get idx 0)) (get idx 1)) in
utest tensorRank m with 2 in
utest tensorShape m with [2, 3] in
utest tensorGetExn m [1, 2] with 12 in
tensorSetExn m [0, 0] 7;
utest tensorGetExn m [0, 0] with 7 in

-- A slice shares storage with the tensor it came from.
let row = tensorSliceExn m [1] in
utest tensorRank row with 1 in
utest tensorGetExn row [2] with 12 in
tensorSetExn row [2] 99;
utest tensorGetExn m [1, 2] with 99 in

-- ... and a copy does not.
let c = tensorCopy m in
tensorSetExn c [0, 0] (negi 1);
utest tensorGetExn m [0, 0] with 7 in

-- Reshape keeps the elements in linear order.
let flat = tensorReshapeExn m [6] in
utest map (lam i. tensorGetExn flat [i]) [0, 1, 2, 3, 4, 5] with [7, 1, 2, 10, 11, 99] in

-- Sub narrows the first dimension, still sharing storage.
let s = tensorSubExn m 1 1 in
utest tensorGetExn s [0, 0] with 10 in

-- Transpose has to copy, since the representation has no strides.
let t = tensorTransposeExn m 0 1 in
utest tensorShape t with [3, 2] in
utest tensorGetExn t [2, 1] with 99 in
()
