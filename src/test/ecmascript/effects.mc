-- References, symbols and tensors.
--
-- `ref` in the standard library is a rank-0 tensor, so these exercise the same
-- machinery: `tensorCreateDense [] (lam. x)` with get and set at index [].
include "common.mc"
include "ref.mc"
include "seq.mc"
include "string.mc"
include "tensor.mc"

mexpr

-- References.
let r = ref 1 in
printLn (int2string (deref r));
modref r 42;
printLn (int2string (deref r));

-- A reference captured by a closure is shared, not copied.
let bump = lam. modref r (addi (deref r) 1) in
bump (); bump ();
printLn (int2string (deref r));

-- Symbols are distinct and compare by identity.
let a = gensym () in
let b = gensym () in
printLn (if eqsym a a then "same" else "differ");
printLn (if eqsym a b then "same" else "differ");

-- Tensors. Indexing is row-major.
let m = tensorCreateDense [2, 3] (lam idx. addi (muli 10 (get idx 0)) (get idx 1)) in
printLn (int2string (tensorRank m));
printLn (strJoin "," (map int2string (tensorShape m)));
printLn (int2string (tensorGetExn m [1, 2]));
tensorSetExn m [0, 0] 7;
printLn (int2string (tensorGetExn m [0, 0]));

-- A slice shares storage with the tensor it came from.
let row = tensorSliceExn m [1] in
printLn (int2string (tensorRank row));
printLn (int2string (tensorGetExn row [2]));
tensorSetExn row [2] 99;
printLn (int2string (tensorGetExn m [1, 2]));

-- ... and a copy does not.
let c = tensorCopy m in
tensorSetExn c [0, 0] (negi 1);
printLn (int2string (tensorGetExn m [0, 0]));

-- Reshape keeps the elements in linear order.
let flat = tensorReshapeExn m [6] in
printLn (strJoin "," (map (lam i. int2string (tensorGetExn flat [i])) [0, 1, 2, 3, 4, 5]));

-- Sub narrows the first dimension, still sharing storage.
let s = tensorSubExn m 1 1 in
printLn (int2string (tensorGetExn s [0, 0]));

-- Transpose has to copy, since the representation has no strides.
let t = tensorTransposeExn m 0 1 in
printLn (strJoin "," (map int2string (tensorShape t)));
printLn (int2string (tensorGetExn t [2, 1]))
