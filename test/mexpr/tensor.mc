include "seq.mc"

-- Some helper functions
let tensorRepeat = lam shape. lam v.
  tensorCreate shape (lam. v)

let tensorFill = lam t. lam v.
  let n = foldl muli 1 (tensorShape t) in
  let t1 = tensorReshapeExn t [n] in
  tensorIteri (lam. lam e. tensorSetExn e [] v) t1

-- Run all tests
let testTensors = lam eq. lam fromInt. lam v.
 -- Rank < 2 Tensors
  let mkRank2TestTensor = lam.
    tensorCreate [3, 4] (lam is.
                          let i = get is 0 in
                          let j = get is 1 in
                          fromInt (addi (addi (muli i 4) j) 1)) in

  -- Set and Get
  let t = tensorRepeat [] v.0 in
  tensorSetExn t [] v.1;
  utest tensorGetExn t [] with v.1 using eq in
  utest tensorRank t with 0 in
  utest tensorShape t with [] in

  let t = mkRank2TestTensor () in
  utest tensorRank t with 2 in
  utest tensorShape t with [3, 4] in
  utest tensorGetExn t [0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 3] with v.4 using eq in
  utest tensorGetExn t [1, 0] with v.5 using eq in
  utest tensorGetExn t [1, 1] with v.6 using eq in
  utest tensorGetExn t [1, 2] with v.7 using eq in
  utest tensorGetExn t [1, 3] with v.8 using eq in
  utest tensorGetExn t [2, 0] with v.9 using eq in
  utest tensorGetExn t [2, 1] with v.10 using eq in
  utest tensorGetExn t [2, 2] with v.11 using eq in
  utest tensorGetExn t [2, 3] with v.12 using eq in

  -- Copy
  let t1 = tensorRepeat [3, 4] v.0 in
  let t2 = mkRank2TestTensor () in
  tensorCopyExn t2 t1;
  utest tensorGetExn t1 [0, 0] with v.1 using eq in
  utest tensorGetExn t1 [0, 1] with v.2 using eq in
  utest tensorGetExn t1 [0, 2] with v.3 using eq in
  utest tensorGetExn t1 [0, 3] with v.4 using eq in
  utest tensorGetExn t1 [1, 0] with v.5 using eq in
  utest tensorGetExn t1 [1, 1] with v.6 using eq in
  utest tensorGetExn t1 [1, 2] with v.7 using eq in
  utest tensorGetExn t1 [1, 3] with v.8 using eq in
  utest tensorGetExn t1 [2, 0] with v.9 using eq in
  utest tensorGetExn t1 [2, 1] with v.10 using eq in
  utest tensorGetExn t1 [2, 2] with v.11 using eq in
  utest tensorGetExn t1 [2, 3] with v.12 using eq in

  -- Reshape
  let t = mkRank2TestTensor () in
  let t1 = tensorReshapeExn t [12] in
  utest tensorRank t1 with 1 in
  utest tensorShape t1 with [12] in
  utest tensorGetExn t1 [0] with v.1 using eq in
  utest tensorGetExn t1 [1] with v.2 using eq in
  utest tensorGetExn t1 [2] with v.3 using eq in
  utest tensorGetExn t1 [3] with v.4 using eq in
  utest tensorGetExn t1 [4] with v.5 using eq in
  utest tensorGetExn t1 [5] with v.6 using eq in
  utest tensorGetExn t1 [6] with v.7 using eq in
  utest tensorGetExn t1 [7] with v.8 using eq in
  utest tensorGetExn t1 [8] with v.9 using eq in
  utest tensorGetExn t1 [9] with v.10 using eq in
  utest tensorGetExn t1 [10] with v.11 using eq in
  utest tensorGetExn t1 [11] with v.12 using eq in

  let t = tensorRepeat [] v.0 in
  let t1 = tensorReshapeExn t [1] in
  utest tensorShape t1 with [1] in

  -- Slice
  let t = tensorRepeat [] v.0 in
  let t1 = tensorSliceExn t [] in
  utest tensorShape t1 with [] in
  utest tensorRank t1 with 0 in
  utest tensorGetExn t1 [] with v.0 using eq in

  let t = tensorRepeat [1] v.0 in
  let t1 = tensorSliceExn t [] in
  utest tensorShape t1 with [1] in
  utest tensorRank t1 with 1 in
  utest tensorGetExn t1 [0] with v.0 using eq in

  let t = tensorRepeat [1] v.0 in
  let t1 = tensorSliceExn t [0] in
  utest tensorShape t1 with [] in
  utest tensorRank t1 with 0 in
  utest tensorGetExn t1 [] with v.0 using eq in

  let t = mkRank2TestTensor () in
  let t1 = tensorSliceExn t [0] in
  let t2 = tensorSliceExn t [1] in
  utest tensorShape t1 with [4] in
  utest tensorShape t2 with [4] in
  utest tensorGetExn t1 [0] with v.1 using eq in
  utest tensorGetExn t1 [1] with v.2 using eq in
  utest tensorGetExn t1 [2] with v.3 using eq in
  utest tensorGetExn t1 [3] with v.4 using eq in
  utest tensorGetExn t2 [0] with v.5 using eq in
  utest tensorGetExn t2 [1] with v.6 using eq in
  utest tensorGetExn t2 [2] with v.7 using eq in
  utest tensorGetExn t2 [3] with v.8 using eq in

  let t = mkRank2TestTensor () in
  let t1 = tensorSliceExn t [1] in
  utest tensorShape t2 with [4] in
  let t2 = tensorSliceExn t1 [1] in
  utest tensorShape t2 with [] in
  utest tensorGetExn t2 [] with v.6 using eq in

  let t = mkRank2TestTensor () in
  let t1 = tensorSliceExn t [1,1] in
  utest tensorShape t1 with [] in
  utest tensorGetExn t1 [] with v.6 using eq in

  -- Slice and Fill
  let t = mkRank2TestTensor () in
  let t1 = tensorSliceExn t [0] in
  let t2 = tensorSliceExn t [1] in
  tensorFill t1 v.0;
  utest tensorGetExn t [0, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1] with v.0 using eq in
  utest tensorGetExn t [0, 2] with v.0 using eq in
  utest tensorGetExn t [0, 3] with v.0 using eq in
  utest tensorGetExn t [1, 0] with v.5 using eq in
  utest tensorGetExn t [1, 1] with v.6 using eq in
  utest tensorGetExn t [1, 2] with v.7 using eq in
  utest tensorGetExn t [1, 3] with v.8 using eq in
  utest tensorGetExn t [2, 0] with v.9 using eq in
  utest tensorGetExn t [2, 1] with v.10 using eq in
  utest tensorGetExn t [2, 2] with v.11 using eq in
  utest tensorGetExn t [2, 3] with v.12 using eq in
  tensorFill t2 v.1;
  utest tensorGetExn t [0, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1] with v.0 using eq in
  utest tensorGetExn t [0, 2] with v.0 using eq in
  utest tensorGetExn t [0, 3] with v.0 using eq in
  utest tensorGetExn t [1, 0] with v.1 using eq in
  utest tensorGetExn t [1, 1] with v.1 using eq in
  utest tensorGetExn t [1, 2] with v.1 using eq in
  utest tensorGetExn t [1, 3] with v.1 using eq in
  utest tensorGetExn t [2, 0] with v.9 using eq in
  utest tensorGetExn t [2, 1] with v.10 using eq in
  utest tensorGetExn t [2, 2] with v.11 using eq in
  utest tensorGetExn t [2, 3] with v.12 using eq in

  -- Slice and Copy
  let t = mkRank2TestTensor () in
  let t1 = tensorSliceExn t [0] in
  let t2 = tensorSliceExn t [1] in
  tensorCopyExn t1 t2;
  utest tensorGetExn t [0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 3] with v.4 using eq in
  utest tensorGetExn t [1, 0] with v.1 using eq in
  utest tensorGetExn t [1, 1] with v.2 using eq in
  utest tensorGetExn t [1, 2] with v.3 using eq in
  utest tensorGetExn t [1, 3] with v.4 using eq in
  utest tensorGetExn t [2, 0] with v.9 using eq in
  utest tensorGetExn t [2, 1] with v.10 using eq in
  utest tensorGetExn t [2, 2] with v.11 using eq in
  utest tensorGetExn t [2, 3] with v.12 using eq in

  -- Sub
  let t = mkRank2TestTensor () in

  let t1 = tensorSubExn t 0 1 in
  utest tensorShape t1 with [1, 4] in
  utest tensorGetExn t1 [0, 0] with v.1 using eq in
  utest tensorGetExn t1 [0, 1] with v.2 using eq in
  utest tensorGetExn t1 [0, 2] with v.3 using eq in
  utest tensorGetExn t1 [0, 3] with v.4 using eq in

  let t2 = tensorSubExn t 1 2 in
  utest tensorShape t2 with [2, 4] in
  utest tensorGetExn t2 [0, 0] with v.5 using eq in
  utest tensorGetExn t2 [0, 1] with v.6 using eq in
  utest tensorGetExn t2 [0, 2] with v.7 using eq in
  utest tensorGetExn t2 [0, 3] with v.8 using eq in
  utest tensorGetExn t2 [1, 0] with v.9 using eq in
  utest tensorGetExn t2 [1, 1] with v.10 using eq in
  utest tensorGetExn t2 [1, 2] with v.11 using eq in
  utest tensorGetExn t2 [1, 3] with v.12 using eq in

  let t3 = tensorSubExn t2 1 1 in
  utest tensorGetExn t3 [0, 0] with v.9 using eq in
  utest tensorGetExn t3 [0, 1] with v.10 using eq in
  utest tensorGetExn t3 [0, 2] with v.11 using eq in
  utest tensorGetExn t3 [0, 3] with v.12 using eq in

  -- Sub and Fill
  let t = mkRank2TestTensor () in
  let t1 = tensorSubExn t 0 1 in
  let t2 = tensorSubExn t 1 2 in

  tensorFill t1 v.0;
  utest tensorGetExn t [0, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1] with v.0 using eq in
  utest tensorGetExn t [0, 2] with v.0 using eq in
  utest tensorGetExn t [0, 3] with v.0 using eq in
  utest tensorGetExn t [1, 0] with v.5 using eq in
  utest tensorGetExn t [1, 1] with v.6 using eq in
  utest tensorGetExn t [1, 2] with v.7 using eq in
  utest tensorGetExn t [1, 3] with v.8 using eq in
  utest tensorGetExn t [2, 0] with v.9 using eq in
  utest tensorGetExn t [2, 1] with v.10 using eq in
  utest tensorGetExn t [2, 2] with v.11 using eq in
  utest tensorGetExn t [2, 3] with v.12 using eq in
  tensorFill t2 v.1;
  utest tensorGetExn t [0, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1] with v.0 using eq in
  utest tensorGetExn t [0, 2] with v.0 using eq in
  utest tensorGetExn t [0, 3] with v.0 using eq in
  utest tensorGetExn t [1, 0] with v.1 using eq in
  utest tensorGetExn t [1, 1] with v.1 using eq in
  utest tensorGetExn t [1, 2] with v.1 using eq in
  utest tensorGetExn t [1, 3] with v.1 using eq in
  utest tensorGetExn t [2, 0] with v.1 using eq in
  utest tensorGetExn t [2, 1] with v.1 using eq in
  utest tensorGetExn t [2, 2] with v.1 using eq in
  utest tensorGetExn t [2, 3] with v.1 using eq in

  -- Iteri
  let t = tensorRepeat [2, 2] v.0 in
  tensorIteri (lam i. lam row.
                         tensorIteri (lam j. lam e.
                                        tensorSetExn e
                                                     []
                                                     (fromInt (addi (muli i 2)
                                                                    j)))
                                      row)
                      t;

  utest tensorGetExn t [0, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1] with v.1 using eq in
  utest tensorGetExn t [1, 0] with v.2 using eq in
  utest tensorGetExn t [1, 1] with v.3 using eq in

  -- Rank 3 Tensors
  let mkRank3TestTensor = lam.
    tensorCreate [2, 2, 3] (lam is.
                              let i = get is 0 in
                              let j = get is 1 in
                              let k = get is 2 in
                              let ofs = addi k (muli 3 (addi j (muli 2 i))) in
                              fromInt (addi ofs 1)) in

  -- Get Set
  let t = mkRank3TestTensor () in
  utest tensorRank t with 3 in
  utest tensorShape t with [2, 2, 3] in
  utest tensorGetExn t [0, 0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 1, 0] with v.4 using eq in
  utest tensorGetExn t [0, 1, 1] with v.5 using eq in
  utest tensorGetExn t [0, 1, 2] with v.6 using eq in
  utest tensorGetExn t [1, 0, 0] with v.7 using eq in
  utest tensorGetExn t [1, 0, 1] with v.8 using eq in
  utest tensorGetExn t [1, 0, 2] with v.9 using eq in
  utest tensorGetExn t [1, 1, 0] with v.10 using eq in
  utest tensorGetExn t [1, 1, 1] with v.11 using eq in
  utest tensorGetExn t [1, 1, 2] with v.12 using eq in

  -- Reshape
  let t = mkRank3TestTensor () in
  let t1 = tensorReshapeExn t [12] in
  utest tensorRank t1 with 1 in
  utest tensorShape t1 with [12] in
  utest tensorGetExn t1 [0] with v.1 using eq in
  utest tensorGetExn t1 [1] with v.2 using eq in
  utest tensorGetExn t1 [2] with v.3 using eq in
  utest tensorGetExn t1 [3] with v.4 using eq in
  utest tensorGetExn t1 [4] with v.5 using eq in
  utest tensorGetExn t1 [5] with v.6 using eq in
  utest tensorGetExn t1 [6] with v.7 using eq in
  utest tensorGetExn t1 [7] with v.8 using eq in
  utest tensorGetExn t1 [8] with v.9 using eq in
  utest tensorGetExn t1 [9] with v.10 using eq in
  utest tensorGetExn t1 [10] with v.11 using eq in
  utest tensorGetExn t1 [11] with v.12 using eq in

  -- Slice
  let t = mkRank3TestTensor () in
  let t1 = tensorSliceExn t [0, 1] in
  utest tensorShape t1 with [3] in
  utest tensorGetExn t1 [0] with v.4 using eq in
  utest tensorGetExn t1 [1] with v.5 using eq in
  utest tensorGetExn t1 [2] with v.6 using eq in
  let t2 = tensorSliceExn t [1] in
  utest tensorShape t2 with [2, 3] in
  utest tensorGetExn t2 [0, 0] with v.7 using eq in
  utest tensorGetExn t2 [0, 1] with v.8 using eq in
  utest tensorGetExn t2 [0, 2] with v.9 using eq in
  utest tensorGetExn t2 [1, 0] with v.10 using eq in
  utest tensorGetExn t2 [1, 1] with v.11 using eq in
  utest tensorGetExn t2 [1, 2] with v.12 using eq in

  -- Slice and Fill
  let t = mkRank3TestTensor () in
  let t1 = tensorSliceExn t [0, 1] in
  let t2 = tensorSliceExn t [1] in
  tensorFill t1 v.0;
  tensorFill t2 v.1;
  utest tensorGetExn t [0, 0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 1, 0] with v.0 using eq in
  utest tensorGetExn t [0, 1, 1] with v.0 using eq in
  utest tensorGetExn t [0, 1, 2] with v.0 using eq in
  utest tensorGetExn t [1, 0, 0] with v.1 using eq in
  utest tensorGetExn t [1, 0, 1] with v.1 using eq in
  utest tensorGetExn t [1, 0, 2] with v.1 using eq in
  utest tensorGetExn t [1, 1, 0] with v.1 using eq in
  utest tensorGetExn t [1, 1, 1] with v.1 using eq in
  utest tensorGetExn t [1, 1, 2] with v.1 using eq in

  -- Sub
  let t = mkRank3TestTensor () in
  let t1 = tensorSubExn t 1 1 in
  utest tensorShape t1 with [1, 2, 3] in
  utest tensorGetExn t1 [0, 0, 0] with v.7 using eq in
  utest tensorGetExn t1 [0, 0, 1] with v.8 using eq in
  utest tensorGetExn t1 [0, 0, 2] with v.9 using eq in
  utest tensorGetExn t1 [0, 1, 0] with v.10 using eq in
  utest tensorGetExn t1 [0, 1, 1] with v.11 using eq in
  utest tensorGetExn t1 [0, 1, 2] with v.12 using eq in

  -- Sub and Fill
  let t = mkRank3TestTensor () in
  let t1 = tensorSubExn t 1 1 in
  tensorFill t1 v.0;
  utest tensorGetExn t [0, 0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 1, 0] with v.4 using eq in
  utest tensorGetExn t [0, 1, 1] with v.5 using eq in
  utest tensorGetExn t [0, 1, 2] with v.6 using eq in
  utest tensorGetExn t [1, 0, 0] with v.0 using eq in
  utest tensorGetExn t [1, 0, 1] with v.0 using eq in
  utest tensorGetExn t [1, 0, 2] with v.0 using eq in
  utest tensorGetExn t [1, 1, 0] with v.0 using eq in
  utest tensorGetExn t [1, 1, 1] with v.0 using eq in
  utest tensorGetExn t [1, 1, 2] with v.0 using eq in

  -- Slice Sub and Fill
  let t = mkRank3TestTensor () in
  let t1 = tensorSliceExn t [1] in
  let t2 = tensorSubExn t1 1 1 in
  tensorFill t2 v.0;
  utest tensorGetExn t [0, 0, 0] with v.1 using eq in
  utest tensorGetExn t [0, 0, 1] with v.2 using eq in
  utest tensorGetExn t [0, 0, 2] with v.3 using eq in
  utest tensorGetExn t [0, 1, 0] with v.4 using eq in
  utest tensorGetExn t [0, 1, 1] with v.5 using eq in
  utest tensorGetExn t [0, 1, 2] with v.6 using eq in
  utest tensorGetExn t [1, 0, 0] with v.7 using eq in
  utest tensorGetExn t [1, 0, 1] with v.8 using eq in
  utest tensorGetExn t [1, 0, 2] with v.9 using eq in
  utest tensorGetExn t [1, 1, 0] with v.0 using eq in
  utest tensorGetExn t [1, 1, 1] with v.0 using eq in
  utest tensorGetExn t [1, 1, 2] with v.0 using eq in

  ()

let v = (0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
let _void = testTensors eqi (lam x. x) v

let v = (0., 1., 2., 3., 4., 5., 6., 7., 8., 9., 10., 11., 12.)
let _void = testTensors eqf int2float v

let v = ([0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12])
let _void = testTensors (eqSeq eqi) (lam x. [x]) v
