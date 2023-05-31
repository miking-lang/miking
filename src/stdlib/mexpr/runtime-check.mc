-- Instruments runtime safety checks in an AST. The current version includes
-- bounds checking for sequence intrinsics such as get and set, and checking
-- for division by zero.
--
-- If a defined constraint is violated, the program will exit and print an
-- error message referring to the intrinsic function used in the call - i.e.
-- not to the place where it was fully applied.

include "common.mc"
include "mexpr/ast-builder.mc"
include "mexpr/cmp.mc"
include "mexpr/eq.mc"
include "mexpr/const-arity.mc"
include "mexpr/pprint.mc"

-- NOTE(larshum, 2021-11-29): The error messages and the error conditions are
-- defined here so that they can be reused in the unit tests.
let _divByZeroMsg = "Division by zero"
let _negIndexSeqAccessMsg = "Negative index used to access sequence"
let _outOfBoundsSeqMsg = "Out of bounds access in sequence"
let _headEmptyMsg = "Head on empty sequence"
let _tailEmptyMsg = "Tail on empty sequence"
let _splitAtNegIndexMsg = "Split at using negative index"
let _splitAtBeyondEndOfSeqMsg = "Split at index out of bounds"
let _subseqNegativeIndexMsg = "Subsequence using negative index"
let _subseqNegativeLenMsg = "Subsequence using negative length"
let _tensorDimMismatchMsg = "Wrong number of dimensions used to access tensor"
let _tensorShapeMismatchMsg = "Invalid indices used to access tensor"
let _negIndexTensorAccessMsg = "Negative index used to access tensor"
let _outOfBoundsTensorMsg = "Out of bounds access in tensor"
let _tensorSubNegativeOffsetMsg = "Subtensor using negative offset"
let _tensorSubNegativeLenMsg = "Subtensor using negative length"
let _tensorSubBoundsMsg = "Subtensor out of bounds"

let _nonEmptySequenceCond = lam s. gti_ (length_ s) (int_ 0)
let _nonZeroCond = lam x. neqi_ x (int_ 0)
let _nonNegativeCond = lam x. geqi_ x (int_ 0)
let _lessThanLengthCond = lam x. lam s. lti_ x (length_ s)
let _tensorRankEq = lam t. lam idxs. eqi_ (utensorRank_ t) (length_ idxs)
let _tensorIdxShapeCond = lam t. lam idxs.
  let sh = nameSym "sh" in
  let acc = nameSym "acc" in
  let i1 = nameSym "i" in
  let i2 = nameSym "i" in
  -- Checks that all indices in the sequence of indices are non-negative and
  -- less than the corresponding dimension of the tensor.
  foldl_
    (nulam_ acc (nulam_ i1
      (if_ (nvar_ acc)
        (if_ (geqi_ (get_ idxs (nvar_ i1)) (int_ 0))
          (lti_ (get_ idxs (nvar_ i1)) (get_ (utensorShape_ t) (nvar_ i1)))
          false_)
        false_)))
    true_
    (create_ (length_ idxs) (nulam_ i2 (nvar_ i2)))
let _lessThanTensorSizeCond = lam t. lam linIdx.
  use MExprAst in
  lti_ linIdx (foldl_ (uconst_ (CMuli ())) (int_ 1) (utensorShape_ t))
let _tensorSliceIdxCond = lam t. lam idxs.
  leqi_ (length_ idxs) (utensorRank_ t)
let _tensorSubBoundsCond = lam t. lam ofs. lam len.
  leqi_ (addi_ ofs len) (head_ (utensorShape_ t))

lang MExprRuntimeCheck = MExprAst + MExprArity + MExprCmp + MExprPrettyPrint
  -- This function returns a sequence of conditions that are to be checked at
  -- runtime for a given intrinsic. Each condition consists of a string
  -- message, which is printed if the condition turns out to be false, and an
  -- expression node which defines how the condition is checked. For an
  -- intrinsic with n parameters, the variables 0 up to n-1 represent its
  -- parameters in declaration order.
  sem intrinsicRuntimeConditions : Const -> [(String, Expr)]
  sem intrinsicRuntimeConditions =
  | CDivi _ | CModi _ -> [(_divByZeroMsg, _nonZeroCond (var_ "1"))]
  | CGet _ | CSet _ ->
    [ (_negIndexSeqAccessMsg, _nonNegativeCond (var_ "1"))
    , (_outOfBoundsSeqMsg, _lessThanLengthCond (var_ "1") (var_ "0")) ]
  | CHead _ -> [(_headEmptyMsg, _nonEmptySequenceCond (var_ "0"))]
  | CTail _ -> [(_tailEmptyMsg, _nonEmptySequenceCond (var_ "0"))]
  | CSplitAt _ ->
    [ (_splitAtNegIndexMsg, _nonNegativeCond (var_ "1"))
    , (_splitAtBeyondEndOfSeqMsg, leqi_ (var_ "1") (length_ (var_ "0"))) ]
  | CSubsequence _ ->
    [ (_subseqNegativeIndexMsg, _nonNegativeCond (var_ "1"))
    , (_subseqNegativeLenMsg, _nonNegativeCond (var_ "2")) ]
  | CTensorGetExn _ | CTensorSetExn _ ->
    [ (_tensorDimMismatchMsg, _tensorRankEq (var_ "0") (var_ "1"))
    , (_tensorShapeMismatchMsg, _tensorIdxShapeCond (var_ "0") (var_ "1")) ]
  | CTensorLinearGetExn _ | CTensorLinearSetExn _ ->
    [ (_negIndexTensorAccessMsg, _nonNegativeCond (var_ "1"))
    , (_outOfBoundsTensorMsg, _lessThanTensorSizeCond (var_ "0") (var_ "1")) ]
  | CTensorSliceExn _ ->
    [ (_tensorDimMismatchMsg, _tensorSliceIdxCond (var_ "0") (var_ "1"))
    , (_tensorShapeMismatchMsg, _tensorIdxShapeCond (var_ "0") (var_ "1")) ]
  | CTensorSubExn _ ->
    [ (_tensorSubNegativeOffsetMsg, _nonNegativeCond (var_ "1")),
      (_tensorSubNegativeLenMsg, _nonNegativeCond (var_ "2")),
      (_tensorSubBoundsMsg, _tensorSubBoundsCond (var_ "0") (var_ "1") (var_ "2")) ]
  | _ -> []

  sem collectUsedRuntimeCheckedIntrinsics : Set Const -> Expr -> Set Const
  sem collectUsedRuntimeCheckedIntrinsics used =
  | TmConst t ->
    if null (intrinsicRuntimeConditions t.val) then used
    else setInsert t.val used
  | t -> sfold_Expr_Expr collectUsedRuntimeCheckedIntrinsics used t

  sem defineRuntimeCheckedFunction : Name -> (Const, Name) -> Expr
  sem defineRuntimeCheckedFunction errId =
  | (intrinsic, id) ->
    -- NOTE(larshum, 2021-11-29): We don't store an info field for the
    -- runtime-checked intrinsic functions because they should catch runtime
    -- errors. In such cases, they will print the info of the intrinsic where
    -- the call originated from.
    recursive let generateCheck = lam infoId. lam cond : (String, Expr).
      ulet_ ""
        (if_ cond.1
          unit_
          (app_ (nvar_ errId) (concat_ (var_ infoId) (str_ cond.0)))) in
    recursive let addParam = lam acc : Expr. lam paramId : Name.
      nulam_ paramId acc in
    let conditions = intrinsicRuntimeConditions intrinsic in
    let arity = constArity intrinsic in
    let intrinsicArgs = create arity (lam i. int2string i) in
    let callBody = appSeq_ (uconst_ intrinsic) (map (lam a. var_ a) intrinsicArgs) in
    let infoId = "i" in
    let checks = map (generateCheck infoId) conditions in
    let body = bindall_ (snoc checks callBody) in
    nulet_ id (ulams_ (cons infoId intrinsicArgs) body)

  sem defineRuntimeCheckedFunctions : [Const] -> (Map Const Name, Expr)
  sem defineRuntimeCheckedFunctions =
  | used ->
    let errorFunctionId = nameSym "errfn" in
    let errorFunction =
      nulet_ errorFunctionId (ulam_ "msg"
        (bind_
          (ulet_ "" (printError_ (concat_ (var_ "msg") (str_ "\n"))))
          (exit_ (int_ 1)))) in
    let intrinsicName = lam c : Const.
      nameSym (cons '_' (getConstStringCode 0 c)) in
    let usedWithId = zip used (map intrinsicName used) in
    let intrinsicMap : Map Const Name = mapFromSeq cmpConst usedWithId in
    let runtimeCheckedFunctions =
      map (defineRuntimeCheckedFunction errorFunctionId) usedWithId in
    (intrinsicMap, bindall_ (join [[errorFunction], runtimeCheckedFunctions]))

  sem callRuntimeCheckedFunctions : Map Const Name -> Expr -> Expr
  sem callRuntimeCheckedFunctions intrinsicIds =
  | TmConst t ->
    let charWithInfo = lam info. lam c.
      TmConst {val = CChar {val = c}, ty = TyUnknown {info = info},
               info = info} in
    let strWithInfo = lam info. lam str.
      TmSeq {tms = map (charWithInfo info) str, ty = TyUnknown {info = info},
             info = info} in
    match mapLookup t.val intrinsicIds with Some runtimeFuncId then
      let infoStr = infoErrorString t.info "" in
      TmApp {
        lhs = TmVar {ident = runtimeFuncId, ty = TyUnknown {info = t.info},
                     info = t.info, frozen = false},
        rhs = strWithInfo t.info infoStr,
        ty = TyUnknown {info = t.info}, info = t.info}
    else TmConst t
  | t -> smap_Expr_Expr (callRuntimeCheckedFunctions intrinsicIds) t

  sem injectRuntimeChecks : Expr -> Expr
  sem injectRuntimeChecks =
  | t ->
    let used = collectUsedRuntimeCheckedIntrinsics (setEmpty cmpConst) t in
    if mapIsEmpty used then t
    else
      let used = setToSeq used in
      match defineRuntimeCheckedFunctions used with (intrinsicIds, functions) in
      let t = callRuntimeCheckedFunctions intrinsicIds t in
      bind_ functions t
end

lang TestLang = MExprRuntimeCheck + MExprPrettyPrint + MExprEq
end

mexpr

use TestLang in

let i = Info {filename = "test.txt", row1 = 1, col1 = 5, row2 = 1, col2 = 20} in

let id = lam c : Const. nameSym (cons '_' (getConstStringCode 0 c)) in
let errorFunctionId = nameSym "errfn" in
let err = lam msg. app_ (nvar_ errorFunctionId) (concat_ (var_ "i") (str_ msg)) in

let divId = id (CDivi ()) in
let expectedDivi =
  ulet_ "_divi" (ulam_ "i" (ulam_ "0" (ulam_ "1" (bind_
    (ulet_ ""
      (if_ (_nonZeroCond (var_ "1")) unit_ (err _divByZeroMsg)))
    (divi_ (var_ "0") (var_ "1")))))) in
utest defineRuntimeCheckedFunction errorFunctionId (CDivi (), divId)
with expectedDivi using eqExpr in

let headId = id (CHead ()) in
let expectedHead =
  ulet_ "_head" (ulam_ "i" (ulam_ "0" (bind_
    (ulet_ ""
      (if_ (_nonEmptySequenceCond (var_ "0")) unit_ (err _headEmptyMsg)))
    (head_ (var_ "0"))))) in
utest defineRuntimeCheckedFunction errorFunctionId (CHead (), headId)
with expectedHead using eqExpr in

let subseqId = id (CSubsequence ()) in
let expectedSubseq =
  ulet_ "_subsequence" (ulam_ "i" (ulam_ "0" (ulam_ "1" (ulam_ "2" (bindall_ [
    ulet_ ""
      (if_ (_nonNegativeCond (var_ "1"))
        unit_ 
        (err _subseqNegativeIndexMsg)),
    ulet_ ""
      (if_ (_nonNegativeCond (var_ "2"))
        unit_
        (err _subseqNegativeLenMsg)),
    subsequence_ (var_ "0") (var_ "1") (var_ "2")]))))) in
utest defineRuntimeCheckedFunction errorFunctionId (CSubsequence (), subseqId)
with expectedSubseq using eqExpr in

let tensorGetId = id (CTensorGetExn ()) in
let expectedTensorGet =
  ulet_ "_tensorGet" (ulam_ "i" (ulam_ "0" (ulam_ "1" (bindall_ [
    ulet_ ""
      (if_ (_tensorRankEq (var_ "0") (var_ "1"))
        unit_
        (err _tensorDimMismatchMsg)),
    ulet_ ""
      (if_ (_tensorIdxShapeCond (var_ "0") (var_ "1"))
        unit_
        (err _tensorShapeMismatchMsg)),
    utensorGetExn_ (var_ "0") (var_ "1")])))) in
utest defineRuntimeCheckedFunction errorFunctionId (CTensorGetExn (), tensorGetId)
with expectedTensorGet using eqExpr in

()
