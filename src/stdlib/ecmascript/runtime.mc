-- Selecting pure runtime intrinsics to append to a generated module.
--
-- Runtime intrinsics are named with a leading `$`. The name allocator in
-- `ident.mc` maps every non-alphanumeric character to `_`, so it can never
-- produce a `$` -- which means a runtime name can never collide with a
-- compiled MExpr binding, with no reserved-word list to keep in sync.

include "bool.mc"
include "basic-types.mc"
include "option.mc"
include "ecmascript/ast.mc"
include "map.mc"
include "seq.mc"
include "set.mc"
include "string.mc"
include "name.mc"

lang ESRuntime = ESAst

  -- The runtime helpers a program actually refers to.
  -- Runtime helpers are the globals whose name begins
  -- with `$`; host globals such as `Math` do not.
  sem esRuntimeUsed : ESProg -> [String]
  sem esRuntimeUsed =
  | ESProg t ->
    setToSeq (setOfSeq cmpString (join (map esGlobalsStmt t.stmts)))

  sem esGlobalsExpr : ESExpr -> [String]
  sem esGlobalsExpr =
  | ESEGlobal t -> match t.name with "$" ++ _ then [t.name] else []
  | ESEArrow t ->
    switch t.body
    case ESFBExpr b then esGlobalsExpr b.expr
    case ESFBBlock b then join (map esGlobalsStmt b.stmts)
    end
  | e -> join (map esGlobalsExpr (esExprChildren e))

  sem esGlobalsStmt : ESStmt -> [String]
  sem esGlobalsStmt =
  | ESSConst t -> esGlobalsExpr t.init
  | ESSLet t -> optionMapOr [] esGlobalsExpr t.init
  | ESSAssign t -> concat (esGlobalsExpr t.target) (esGlobalsExpr t.value)
  | ESSExpr t -> esGlobalsExpr t.expr
  | ESSReturn t -> optionMapOr [] esGlobalsExpr t.expr
  | ESSThrow t -> esGlobalsExpr t.expr
  | ESSIf t ->
    join [ esGlobalsExpr t.cond
         , join (map esGlobalsStmt t.thn), join (map esGlobalsStmt t.els) ]
  | ESSBlock t -> join (map esGlobalsStmt t.stmts)
  | ESSWhile t ->
    concat (esGlobalsExpr t.cond) (join (map esGlobalsStmt t.body))
  | ESSFunDecl t -> join (map esGlobalsStmt t.body)
  | ESSExportDefault t -> esGlobalsStmt t.stmt
  | ESSClass _ | ESSContinue _ -> []

end

type ESRuntimeIntrinsic = {
  -- The global that generated code refers to, `$` and all.
  name : String,

  -- Other intrinsics this one calls, pulled in automatically.
  deps : [String],

  -- The definition, emitted verbatim.
  source : String
}

let esRuntimeIntrinsics : [ESRuntimeIntrinsic] = [
  -- Rounds half away from zero, matching OCaml. JS `Math.round` rounds half
  -- towards +Infinity, so it disagrees on every negative half: OCaml gives
  -- -1 and -2 for -0.5 and -1.5, where `Math.round` gives -0 and -1.
  { name = "$roundfi", deps = [], source =
"function $roundfi(x) {
  return x < 0 ? -Math.round(-x) : Math.round(x);
}" },

  -- Builds a sequence of characters from a JavaScript string literal. Spreading
  -- iterates by codepoint, so "ab\u{1F600}cd" yields five elements, matching
  -- Miking, where JS `.length` would report six.
  { name = "$S", deps = ["$sq"], source =
"function $S(s) {
  return $sq([...s]);
}" },

  -- The inverse of `$S`, used at the boundary with a host environment. Hosts take
  -- and return ordinary JS strings and never see the internal representation.
  { name = "$jsStr", deps = ["$arr"], source =
"function $jsStr(s) {
  return $arr(s).join(\"\");
}" },

  -- OCaml's `string_of_float`: "%.12g", with a trailing "." added when the
  -- result would otherwise look like an integer.
  --
  -- JS `String()` disagrees in three ways -- it prints 1.0 as "1", switches to
  -- exponential at different thresholds, and writes a one-digit exponent where C
  -- writes two -- so the formatting is done here rather than borrowed.
  { name = "$f2s", deps = [], source =
"function $f2s(x) {
  if (Number.isNaN(x)) return \"nan\";
  if (x === Infinity) return \"inf\";
  if (x === -Infinity) return \"-inf\";
  const P = 12;
  let s;
  if (x === 0) {
    s = Object.is(x, -0) ? \"-0\" : \"0\";
  } else {
    const e = Number(x.toExponential(P - 1).split(\"e\")[1]);
    if (e < -4 || e >= P) {
      let [m, ex] = x.toExponential(P - 1).split(\"e\");
      if (m.indexOf(\".\") >= 0) m = m.replace(/0+$/, \"\").replace(/\\.$/, \"\");
      let d = ex.slice(1);
      if (d.length < 2) d = \"0\" + d;
      s = m + \"e\" + ex[0] + d;
    } else {
      s = x.toFixed(Math.max(0, P - 1 - e));
      if (s.indexOf(\".\") >= 0) s = s.replace(/0+$/, \"\").replace(/\\.$/, \"\");
    }
  }
  return /[.e]/.test(s) ? s : s + \".\";
}" },

  { name = "$float2string", deps = ["$f2s", "$S"], source =
"function $float2string(x) {
  return $S($f2s(x));
}" },

  { name = "$string2float", deps = ["$jsStr"], source =
"function $string2float(s) {
  return parseFloat($jsStr(s));
}" },

  { name = "$stringIsFloat", deps = ["$jsStr"], source =
"function $stringIsFloat(s) {
  const t = $jsStr(s);
  return t.length > 0 && !Number.isNaN(Number(t));
}" },

  -- Symbols are plain integers from a counter. `eqsym` is then `===` and
  -- `sym2hash` is the identity, which is all MExpr asks of them -- the type
  -- system keeps them from being confused with ordinary integers.
  { name = "$gensym", deps = [], source =
"let $symCounter = 0;
function $gensym() {
  $symCounter += 1;
  return $symCounter;
}" },

  -- A sequence, represented as boot's `Rope` is: either the elements of `a` from
  -- `o` for `n` of them, or the concatenation of `l` and `r` when `a` is null.
  --
  -- Concatenating is therefore O(1), and so are `cons`, `snoc` and taking a
  -- subsequence -- a subsequence shares the array it is cut from. Reading an
  -- element flattens the tree first, rewriting this node in place so the cost is
  -- paid once. Boot uses a mutable `ref` for the same purpose; a JavaScript
  -- object cannot change class, so the node carries its own tag instead.
  --
  -- Keeping one class, rather than one per case, keeps every field access in the
  -- program monomorphic, which is what the JIT rewards.
  { name = "$Seq", deps = [], source =
"class $Seq {
  constructor(a, o, n, l, r) {
    this.a = a; this.o = o; this.n = n; this.l = l; this.r = r;
  }
}" },

  -- Flattens a sequence into a single array, in place.
  -- An explicit stack: a sequence built by repeated `cons` is a tree as deep
  -- as it is long, which would overflow the call stack.
  { name = "$col", deps = ["$Seq"], source =
"function $col(s) {
  if (s.a !== null) return s;
  const dst = new Array(s.n);
  let i = 0;
  const st = [s.r, s.l];
  while (st.length !== 0) {
    const t = st.pop();
    if (t.a !== null) {
      const a = t.a, o = t.o, n = t.n;
      for (let k = 0; k < n; k++) dst[i++] = a[o + k];
    } else {
      st.push(t.r); st.push(t.l);
    }
  }
  s.a = dst; s.o = 0; s.l = null; s.r = null;
  return s;
}" },

  -- A sequence holding exactly the elements of a JavaScript array.
  { name = "$sq", deps = ["$Seq"], source =
"function $sq(a) {
  return new $Seq(a, 0, a.length, null, null);
}" },

  -- The elements of a sequence as a JavaScript array, for the host and for the
  -- tensor helpers. Copies only when the sequence is a part of a larger array.
  { name = "$arr", deps = ["$col"], source =
"function $arr(s) {
  const t = $col(s);
  return t.o === 0 && t.n === t.a.length ? t.a : t.a.slice(t.o, t.o + t.n);
}" },

  { name = "$len", deps = ["$Seq"], source =
"function $len(s) {
  return s.n;
}" },

  { name = "$get", deps = ["$col"], source =
"function $get(s, i) {
  return s.a !== null ? s.a[s.o + i] : $col(s).a[i];
}" },

  { name = "$cat", deps = ["$Seq"], source =
"function $cat(x, y) {
  if (x.n === 0) return y;
  if (y.n === 0) return x;
  return new $Seq(null, 0, x.n + y.n, x, y);
}" },

  { name = "$cons", deps = ["$cat", "$sq"], source =
"function $cons(v, s) {
  return $cat($sq([v]), s);
}" },

  { name = "$snoc", deps = ["$cat", "$sq"], source =
"function $snoc(s, v) {
  return $cat(s, $sq([v]));
}" },

  -- Clamped, matching the reference backend for an over-long span. A start past
  -- the end is not well defined there -- it returns a sequence of negative length
  -- -- so this returns empty instead.
  { name = "$sub", deps = ["$Seq", "$col", "$sq"], source =
"function $sub(s, off, cnt) {
  if (s.n === 0) return s;
  const start = Math.max(0, Math.min(off, s.n));
  const n = Math.max(0, Math.min(cnt, s.n - start));
  if (n === 0) return $sq([]);
  const t = $col(s);
  return new $Seq(t.a, t.o + start, n, null, null);
}" },

  { name = "$tail", deps = ["$sub"], source =
"function $tail(s) {
  return $sub(s, 1, s.n - 1);
}" },

  -- Returns an MExpr pair, which is a record with fields "0" and "1".
  { name = "$splitAt", deps = ["$sub"], source =
"function $splitAt(s, i) {
  return { \"0\": $sub(s, 0, i), \"1\": $sub(s, i, s.n - i) };
}" },

  { name = "$subsequence", deps = ["$sub"], source =
"function $subsequence(s, off, len) {
  return $sub(s, off, len);
}" },

  { name = "$set", deps = ["$arr", "$sq"], source =
"function $set(s, i, v) {
  const out = $arr(s).slice();
  out[i] = v;
  return $sq(out);
}" },

  { name = "$create", deps = ["$sq"], source =
"function $create(n, f) {
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(i);
  return $sq(out);
}" },

  { name = "$map", deps = ["$col", "$sq"], source =
"function $map(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(a[o + i]);
  return $sq(out);
}" },

  { name = "$mapi", deps = ["$col", "$sq"], source =
"function $mapi(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(i)(a[o + i]);
  return $sq(out);
}" },

  { name = "$iter", deps = ["$col"], source =
"function $iter(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) f(a[o + i]);
  return undefined;
}" },

  { name = "$iteri", deps = ["$col"], source =
"function $iteri(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) f(i)(a[o + i]);
  return undefined;
}" },

  { name = "$foldl", deps = ["$col"], source =
"function $foldl(f, acc, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) acc = f(acc)(a[o + i]);
  return acc;
}" },

  { name = "$foldr", deps = ["$col"], source =
"function $foldr(f, acc, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = n - 1; i >= 0; i--) acc = f(a[o + i])(acc);
  return acc;
}" },

  { name = "$rev", deps = ["$col", "$sq"], source =
"function $rev(s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = a[o + n - 1 - i];
  return $sq(out);
}" },

  -- Row-major linear index, matching boot's cartesian_to_linear_idx. A partial
  -- index (fewer entries than the rank) addresses the start of a sub-block,
  -- which is what slicing relies on.
  { name = "$tIdx", deps = [], source =
"function $tIdx(shape, idx) {
  let ofs = 0;
  let mul = 1;
  for (let k = shape.length - 1; k >= idx.length; k--) mul *= shape[k];
  for (let k = idx.length - 1; k >= 0; k--) {
    ofs += mul * idx[k];
    mul *= shape[k];
  }
  return ofs;
}" },

  { name = "$tSize", deps = [], source =
"function $tSize(shape) {
  let n = 1;
  for (let i = 0; i < shape.length; i++) n *= shape[i];
  return n;
}" },

  -- A dense tensor is one flat *mutable* `data` array plus a shape and an offset
  -- into it. There are no strides, which is why slicing can be a view but
  -- transposing cannot. A rank-0 tensor has size 1 and is how `ref.mc` gets
  -- mutability.
  -- A tensor keeps its shape as a plain array; only the boundary with the
  -- program speaks in sequences.
  { name = "$tCreate", deps = ["$tSize", "$arr", "$sq"], source =
"function $tCreate(shapeSeq, f) {
  const shape = $arr(shapeSeq);
  const size = $tSize(shape);
  const rank = shape.length;
  const data = new Array(size);
  for (let i = 0; i < size; i++) {
    const idx = new Array(rank);
    let rem = i;
    for (let d = rank - 1; d >= 0; d--) {
      idx[d] = rem % shape[d];
      rem = (rem - idx[d]) / shape[d];
    }
    data[i] = f($sq(idx));
  }
  return { data: data, shape: shape, rank: rank, offset: 0, size: size };
}" },

  { name = "$tUninit", deps = ["$tSize", "$arr"], source =
"function $tUninit(shapeSeq) {
  const shape = $arr(shapeSeq);
  const size = $tSize(shape);
  return { data: new Array(size).fill(0), shape: shape,
           rank: shape.length, offset: 0, size: size };
}" },

  { name = "$tGet", deps = ["$tIdx", "$arr"], source =
"function $tGet(t, idx) {
  return t.data[$tIdx(t.shape, $arr(idx)) + t.offset];
}" },

  { name = "$tSet", deps = ["$tIdx", "$arr"], source =
"function $tSet(t, idx, v) {
  t.data[$tIdx(t.shape, $arr(idx)) + t.offset] = v;
}" },

  { name = "$tShape", deps = ["$sq"], source =
"function $tShape(t) {
  return $sq(t.shape);
}" },

  { name = "$tLinGet", deps = [], source =
"function $tLinGet(t, i) {
  return t.data[i + t.offset];
}" },

  { name = "$tLinSet", deps = [], source =
"function $tLinSet(t, i, v) {
  t.data[i + t.offset] = v;
}" },

  { name = "$tReshape", deps = ["$arr"], source =
"function $tReshape(t, shapeSeq) {
  const shape = $arr(shapeSeq);
  return { data: t.data, shape: shape, rank: shape.length,
           offset: t.offset, size: t.size };
}" },

  -- Shares `data` with its parent, so writing through a slice is visible from
  -- the tensor it came from. Do not reach for `Array.slice` here: copying would
  -- silently break that aliasing.
  { name = "$tSlice", deps = ["$tIdx", "$tSize", "$arr"], source =
"function $tSlice(t, sliceSeq) {
  const slice = $arr(sliceSeq);
  if (slice.length === 0) return t;
  const offset = $tIdx(t.shape, slice) + t.offset;
  const rank = t.rank - slice.length;
  const shape = rank > 0 ? t.shape.slice(slice.length) : [];
  return { data: t.data, shape: shape, rank: rank,
           offset: offset, size: $tSize(shape) };
}" },

  -- Narrows the first dimension, also sharing `data`.
  { name = "$tSub", deps = ["$tIdx", "$tSize"], source =
"function $tSub(t, ofs, len) {
  const offset = $tIdx(t.shape, [ofs]) + t.offset;
  const shape = t.shape.slice();
  shape[0] = len;
  return { data: t.data, shape: shape, rank: t.rank,
           offset: offset, size: $tSize(shape) };
}" },

  -- The one operation that breaks the sharing.
  { name = "$tCopy", deps = [], source =
"function $tCopy(t) {
  return { data: t.data.slice(t.offset, t.offset + t.size), shape: t.shape,
           rank: t.rank, offset: 0, size: t.size };
}" },

  { name = "$tIterSlice", deps = ["$tSlice", "$sq"], source =
"function $tIterSlice(f, t) {
  if (t.rank === 0) { f(0)(t); return undefined; }
  for (let i = 0; i < t.shape[0]; i++) f(i)($tSlice(t, $sq([i])));
  return undefined;
}" },

  { name = "$tEq", deps = [], source =
"function $tEq(eq, t1, t2) {
  if (t1.rank !== t2.rank) return false;
  for (let i = 0; i < t1.rank; i++) if (t1.shape[i] !== t2.shape[i]) return false;
  for (let i = 0; i < t1.size; i++) {
    if (!eq(t1.data[i + t1.offset])(t2.data[i + t2.offset])) return false;
  }
  return true;
}" },

  -- Without strides a transposed view is not representable, so this copies --
  -- as the reference implementation does.
  { name = "$tTranspose", deps = ["$tCreate", "$tGet", "$sq", "$arr"], source =
"function $tTranspose(t, d0, d1) {
  const shape = t.shape.slice();
  const tmp = shape[d0];
  shape[d0] = shape[d1];
  shape[d1] = tmp;
  return $tCreate($sq(shape), (idx) => {
    const j = $arr(idx).slice();
    const s = j[d0];
    j[d0] = j[d1];
    j[d1] = s;
    return $tGet(t, $sq(j));
  });
}" },

  { name = "$tToString", deps = ["$jsStr", "$S", "$tGet", "$tSlice", "$sq"], source =
"function $tToString(el, t) {
  const recur = (indent, t) => {
    if (t.rank === 0) return $jsStr(el($tGet(t, $sq([]))));
    const n = t.shape[0];
    const parts = [];
    if (t.rank === 1) {
      for (let i = 0; i < n; i++) parts.push(recur(\"\", $tSlice(t, $sq([i]))));
      return \"[\" + parts.join(\", \") + \"]\";
    }
    const ni = indent + \"\\t\";
    for (let i = 0; i < n; i++) parts.push(recur(ni, $tSlice(t, $sq([i]))));
    return \"[\\n\" + ni + parts.join(\",\\n\" + ni) + \"\\n\" + indent + \"]\";
  };
  return $S(recur(\"\", t));
}" },

  { name = "$ref", deps = [], source =
"function $ref(x) { return { v: x }; }" },

  { name = "$modref", deps = [], source =
"function $modref(r, v) { r.v = v; }" },

  -- `constructorTag` needs a stable integer per constructor. Each constructor is
  -- its own class, so the class object identifies it; ids are handed out on
  -- first sight, as boot does with symbol hashes. Non-constructor values are 0,
  -- matching the reference implementation.
  { name = "$conTag", deps = [], source =
"const $tagMap = new Map();
let $tagCounter = 0;
function $conTag(x) {
  if (x === null || typeof x !== \"object\") return 0;
  let t = $tagMap.get(x.constructor);
  if (t === undefined) {
    $tagCounter += 1;
    t = $tagCounter;
    $tagMap.set(x.constructor, t);
  }
  return t;
}" },

  -- Adapts what a host returns from `readBytesAsString`; it does no reading
  -- itself.
  --
  -- A host hands back an ordinary JS pair of the text and the number of *bytes*
  -- consumed, which is not the number of characters -- only the host knows the
  -- encoding, so it reports both. This turns that into MExpr's representation: a
  -- `[Char]` for the text, and a record with "0" and "1" for the tuple. Keeping
  -- the conversion here is what lets a host stay in plain JavaScript.
  { name = "$readBytesResult", deps = ["$S"], source =
"function $readBytesResult(pair) {
  return { \"0\": $S(pair[0]), \"1\": pair[1] };
}" },

  -- `debug_typeof` is a debugging aid with no implementation in boot, so there is
  -- no reference behaviour to match. This reports the host's view.
  { name = "$typeOf", deps = ["$S"], source =
"function $typeOf(x) {
  if (Array.isArray(x)) return $S(\"Sequence\");
  if (x === null || x === undefined) return $S(\"Unit\");
  if (typeof x === \"object\") {
    return $S(x.constructor === Object ? \"Record\" : x.constructor.name);
  }
  return $S(typeof x);
}" },

  -- A constant this backend does not implement.
  --
  -- The loader pipeline binds every builtin in its prelude whether a program uses
  -- it or not, so refusing at compile time would make the whole pipeline
  -- unusable. Compiling to a stub keeps that binding legal while making any
  -- actual call fail immediately, naming the intrinsic.
  { name = "$unsupported", deps = [], source =
"function $unsupported(name) {
  throw new Error(\"ecmascript backend: '\" + name + \"' is not implemented\");
}" },

  -- An external with no default here, and none supplied by the host through
  -- `env.externals`. Returns a placeholder that throws when *used* rather than
  -- failing at once: dead-code elimination guarantees an external is referenced,
  -- not that the reference ever runs. Calling the placeholder throws, and so
  -- does reading any property of it, so a missing opaque value -- a channel,
  -- say -- reports itself even when it reaches a host function that expects
  -- the real thing. The compiler calls the result immediately for an arity-0
  -- external of a transparent type, which the program could use directly.
  { name = "$noExternal", deps = [], source =
"function $noExternal(name) {
  const fail = () => {
    throw new Error(\"no default implementation for external '\" + name +
                    \"', and the environment does not provide one\");
  };
  return new Proxy(fail, { get: fail });
}" },

  -- Default implementations of externals, one per section, each taking the
  -- runtime environment and returning the implementation. The compiler treats
  -- this file as the table of which externals have a default: an external named
  -- `x` has one exactly when a `$ext_x` section exists. Values crossing the
  -- boundary are converted by the compiler, so these work in plain JavaScript.
  { name = "$ext_externalExp", deps = [], source =
"function $ext_externalExp(env) { return Math.exp; }" },

  { name = "$ext_externalLog", deps = [], source =
"function $ext_externalLog(env) { return Math.log; }" },

  { name = "$ext_externalAtan", deps = [], source =
"function $ext_externalAtan(env) { return Math.atan; }" },

  { name = "$ext_externalSin", deps = [], source =
"function $ext_externalSin(env) { return Math.sin; }" },

  { name = "$ext_externalCos", deps = [], source =
"function $ext_externalCos(env) { return Math.cos; }" },

  { name = "$ext_externalAtan2", deps = [], source =
"function $ext_externalAtan2(env) { return Math.atan2; }" },

  { name = "$ext_externalPow", deps = [], source =
"function $ext_externalPow(env) { return Math.pow; }" },

  { name = "$ext_externalSqrt", deps = [], source =
"function $ext_externalSqrt(env) { return Math.sqrt; }" },

  -- The logarithm of the binomial coefficient n choose k, summed as logarithms
  -- so it does not overflow for large arguments.
  { name = "$ext_externalLogCombination", deps = [], source =
"function $ext_externalLogCombination(env) {
  return (n, k) => {
    if (k < 0 || k > n) return -Infinity;
    const m = Math.min(k, n - k);
    let s = 0;
    for (let i = 1; i <= m; i++) s += Math.log(n - m + i) - Math.log(i);
    return s;
  };
}" },

  -- File externals that map directly onto operations every host provides. The
  -- channel operations do not have defaults: a host implements them.
  { name = "$ext_externalFileExists", deps = [], source =
"function $ext_externalFileExists(env) { return (path) => env.fileExists(path); }" },

  { name = "$ext_externalDeleteFile", deps = [], source =
"function $ext_externalDeleteFile(env) { return (path) => { env.deleteFile(path); }; }" },

  -- Atomic references. JavaScript runs a program on one thread, so an atomic
  -- reference is an ordinary box. Compare-and-set compares with `===`.
  { name = "$ext_externalAtomicMake", deps = [], source =
"function $ext_externalAtomicMake(env) { return (v) => ({ v: v }); }" },

  { name = "$ext_externalAtomicGet", deps = [], source =
"function $ext_externalAtomicGet(env) { return (r) => r.v; }" },

  { name = "$ext_externalAtomicExchange", deps = [], source =
"function $ext_externalAtomicExchange(env) {
  return (r, v) => { const old = r.v; r.v = v; return old; };
}" },

  { name = "$ext_externalAtomicCAS", deps = [], source =
"function $ext_externalAtomicCAS(env) {
  return (r, seen, v) => {
    if (r.v !== seen) return false;
    r.v = v;
    return true;
  };
}" },

  { name = "$ext_externalAtomicFetchAndAdd", deps = [], source =
"function $ext_externalAtomicFetchAndAdd(env) {
  return (r, n) => { const old = r.v; r.v = old + n; return old; };
}" }
]

let esRuntimeByName : Map String ESRuntimeIntrinsic =
  foldl (lam acc. lam i. mapInsert i.name i acc)
    (mapEmpty cmpString) esRuntimeIntrinsics

-- Renders the definitions for `used` plus everything they depend on.
--
-- Emitted in sorted order, which keeps output stable across runs.
let esRuntimeEmit : [String] -> String = lam used.
  if null used then "" else
  recursive let close = lam pending. lam seen.
    match pending with [n] ++ rest then
      if setMem n seen then close rest seen
      else match mapLookup n esRuntimeByName with Some i then
        close (concat i.deps rest) (setInsert n seen)
      else error (concat "unknown runtime intrinsic: " n)
    else seen
  in
  let names = setToSeq (close used (setEmpty cmpString)) in
  join
  [ "\n// ---------------------------------------------------------------\n"
  , "// MExpr runtime intrinsics.\n"
  , "// ---------------------------------------------------------------\n\n"
  , strJoin "\n\n" (map (lam n. (mapFindExn n esRuntimeByName).source) names)
  , "\n" ]

mexpr

use ESRuntime in

utest mapMem "$cons" esRuntimeByName with true in
utest mapMem "$cat" esRuntimeByName with true in
utest mapMem "$sq" esRuntimeByName with true in
utest mapMem "$roundfi" esRuntimeByName with true in
utest mapMem "$float2string" esRuntimeByName with true in

-- Dependencies are recorded alongside the definition.
utest (mapFindExn "$cons" esRuntimeByName).deps with ["$cat", "$sq"] in
utest (mapFindExn "$roundfi" esRuntimeByName).deps with [] in

-- Every dependency names an intrinsic that exists.
utest
  filter (lam d. not (mapMem d esRuntimeByName))
    (join (map (lam i. i.deps) esRuntimeIntrinsics))
with [] in

-- A name is defined once.
utest length esRuntimeIntrinsics with mapSize esRuntimeByName in

let a = nameSym "a" in

-- Reports exactly the runtime helpers the program refers to. Reading this off
-- the finished program is what keeps a helper used only inside a binding that
-- was later deleted from being emitted; `mcore.mc` tests that interaction.
let prog = ESProg { imports = [], stmts =
  [ ESSConst { id = a, init = ESECall
      { callee = ESEGlobal { name = "$unused" }, args = [] } }
  , ESSExpr { expr = ESECall
      { callee = ESEGlobal { name = "$kept" }, args = [ESEInt { value = 1 }] } } ] } in
utest esRuntimeUsed prog with ["$kept", "$unused"] in

-- Host globals are not runtime helpers.
utest esRuntimeUsed (ESProg { imports = [], stmts =
  [ ESSExpr { expr = ESECall
      { callee = esMember (ESEGlobal { name = "Math" }) "floor"
      , args = [ESEInt { value = 1 }] } } ] }) with [] in

-- Nothing requested means nothing emitted.
utest esRuntimeEmit [] with "" in

-- A dependency is pulled in even when it was not asked for.
let contains = lam needle. lam s. gti (length (strSplit needle s)) 1 in
-- `$cons` is `$cat` of a one-element `$sq`, and `$cat` needs the class.
let out = esRuntimeEmit ["$cons"] in
utest contains "function $cons(" out with true in
utest contains "function $cat(" out with true in
utest contains "function $sq(" out with true in
utest contains "class $Seq {" out with true in
utest contains "function $roundfi(" out with false in

()
