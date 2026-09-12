// Pure MExpr intrinsics for the `ecmascript` backend.
//
// This is hand-written JavaScript, not compiler output. It holds the
// intrinsics that cannot be inlined as JS operators the way `addi` becomes
// `+`. The compiler reads this file and appends only the definitions a
// program actually uses to the bottom of the generated module, after `main`.
//
// Each definition is delimited so the compiler can pick it out:
//
//     //!intrinsic <name> [<dependency>...]
//     ...code...
//     //!end
//
// Everything outside those markers -- these comments and the export list at
// the end -- is ignored by the compiler and exists so that this file remains a
// valid, lintable, independently testable ES module.
//
// Definitions must be `function` declarations. They are emitted in dependency
// order, but hoisting means order would not matter anyway.

// Narrows a BigInt result back to a JS number.
//
// MCore does not fix an integer width, and this backend represents Int as a
// JS number, so the safe range is 53 bits. Shift intrinsics compute in 63-bit
// BigInt to match the OCaml backend exactly; a result outside the safe range
// cannot be represented here and is a loud error rather than a silently wrong
// value.
//!intrinsic $fromBig
function $fromBig(x) {
  const n = Number(x);
  if (!Number.isSafeInteger(n)) {
    throw new RangeError(
      "ecmascript backend: integer " + x +
      " exceeds the 2^53 range representable by a JS number");
  }
  return n;
}
//!end

// Left shift with OCaml's 63-bit native int semantics, including wraparound.
//!intrinsic $slli $fromBig
function $slli(a, b) {
  return $fromBig(BigInt.asIntN(63, BigInt(a) << BigInt(b)));
}
//!end

// Logical right shift: the operand is reinterpreted as 63-bit unsigned, so a
// negative input yields a large positive result exactly as in OCaml.
//!intrinsic $srli $fromBig
function $srli(a, b) {
  return $fromBig(BigInt.asUintN(63, BigInt(a)) >> BigInt(b));
}
//!end

// Arithmetic right shift: the sign bit is propagated.
//!intrinsic $srai $fromBig
function $srai(a, b) {
  return $fromBig(BigInt.asIntN(63, BigInt(a)) >> BigInt(b));
}
//!end

// Rounds half away from zero, matching OCaml. JS `Math.round` rounds half
// towards +Infinity, so it disagrees on every negative half: OCaml gives
// -1 and -2 for -0.5 and -1.5, where `Math.round` gives -0 and -1.
//!intrinsic $roundfi
function $roundfi(x) {
  return x < 0 ? -Math.round(-x) : Math.round(x);
}
//!end

// Builds a sequence of characters from a JavaScript string literal. Spreading
// iterates by codepoint, so "ab\u{1F600}cd" yields five elements, matching
// Miking, where JS `.length` would report six.
//!intrinsic $S $sq
function $S(s) {
  return $sq([...s]);
}
//!end

// The inverse of `$S`, used at the boundary with a host environment. Hosts take
// and return ordinary JS strings and never see the internal representation.
//!intrinsic $jsStr $arr
function $jsStr(s) {
  return $arr(s).join("");
}
//!end

// OCaml's `string_of_float`: "%.12g", with a trailing "." added when the
// result would otherwise look like an integer.
//
// JS `String()` disagrees in three ways -- it prints 1.0 as "1", switches to
// exponential at different thresholds, and writes a one-digit exponent where C
// writes two -- so the formatting is done here rather than borrowed.
//!intrinsic $f2s
function $f2s(x) {
  if (Number.isNaN(x)) return "nan";
  if (x === Infinity) return "inf";
  if (x === -Infinity) return "-inf";
  const P = 12;
  let s;
  if (x === 0) {
    s = Object.is(x, -0) ? "-0" : "0";
  } else {
    const e = Number(x.toExponential(P - 1).split("e")[1]);
    if (e < -4 || e >= P) {
      let [m, ex] = x.toExponential(P - 1).split("e");
      if (m.indexOf(".") >= 0) m = m.replace(/0+$/, "").replace(/\.$/, "");
      let d = ex.slice(1);
      if (d.length < 2) d = "0" + d;
      s = m + "e" + ex[0] + d;
    } else {
      s = x.toFixed(Math.max(0, P - 1 - e));
      if (s.indexOf(".") >= 0) s = s.replace(/0+$/, "").replace(/\.$/, "");
    }
  }
  return /[.e]/.test(s) ? s : s + ".";
}
//!end

//!intrinsic $float2string $f2s $S
function $float2string(x) {
  return $S($f2s(x));
}
//!end

//!intrinsic $string2float $jsStr
function $string2float(s) {
  return parseFloat($jsStr(s));
}
//!end

//!intrinsic $stringIsFloat $jsStr
function $stringIsFloat(s) {
  const t = $jsStr(s);
  return t.length > 0 && !Number.isNaN(Number(t));
}
//!end

// Symbols are plain integers from a counter. `eqsym` is then `===` and
// `sym2hash` is the identity, which is all MExpr asks of them -- the type
// system keeps them from being confused with ordinary integers.
//!intrinsic $gensym
let $symCounter = 0;
function $gensym() {
  $symCounter += 1;
  return $symCounter;
}
//!end

// A sequence, represented as boot's `Rope` is: either the elements of `a` from
// `o` for `n` of them, or the concatenation of `l` and `r` when `a` is null.
//
// Concatenating is therefore O(1), and so are `cons`, `snoc` and taking a
// subsequence -- a subsequence shares the array it is cut from. Reading an
// element flattens the tree first, rewriting this node in place so the cost is
// paid once. Boot uses a mutable `ref` for the same purpose; a JavaScript
// object cannot change class, so the node carries its own tag instead.
//
// Keeping one class, rather than one per case, keeps every field access in the
// program monomorphic, which is what the JIT rewards.
//!intrinsic $Seq
class $Seq {
  constructor(a, o, n, l, r) {
    this.a = a; this.o = o; this.n = n; this.l = l; this.r = r;
  }
}
//!end

// Flattens a sequence into a single array, in place.
// An explicit stack: a sequence built by repeated `cons` is a tree as deep
// as it is long, which would overflow the call stack.
//!intrinsic $col $Seq
function $col(s) {
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
}
//!end

// A sequence holding exactly the elements of a JavaScript array.
//!intrinsic $sq $Seq
function $sq(a) {
  return new $Seq(a, 0, a.length, null, null);
}
//!end

// The elements of a sequence as a JavaScript array, for the host and for the
// tensor helpers. Copies only when the sequence is a part of a larger array.
//!intrinsic $arr $col
function $arr(s) {
  const t = $col(s);
  return t.o === 0 && t.n === t.a.length ? t.a : t.a.slice(t.o, t.o + t.n);
}
//!end

//!intrinsic $len $Seq
function $len(s) {
  return s.n;
}
//!end

//!intrinsic $get $col
function $get(s, i) {
  return s.a !== null ? s.a[s.o + i] : $col(s).a[i];
}
//!end

//!intrinsic $cat $Seq
function $cat(x, y) {
  if (x.n === 0) return y;
  if (y.n === 0) return x;
  return new $Seq(null, 0, x.n + y.n, x, y);
}
//!end

//!intrinsic $cons $cat $sq
function $cons(v, s) {
  return $cat($sq([v]), s);
}
//!end

//!intrinsic $snoc $cat $sq
function $snoc(s, v) {
  return $cat(s, $sq([v]));
}
//!end

// Clamped, matching the reference backend for an over-long span. A start past
// the end is not well defined there -- it returns a sequence of negative length
// -- so this returns empty instead.
//!intrinsic $sub $Seq $col $sq
function $sub(s, off, cnt) {
  if (s.n === 0) return s;
  const start = Math.max(0, Math.min(off, s.n));
  const n = Math.max(0, Math.min(cnt, s.n - start));
  if (n === 0) return $sq([]);
  const t = $col(s);
  return new $Seq(t.a, t.o + start, n, null, null);
}
//!end

//!intrinsic $tail $sub
function $tail(s) {
  return $sub(s, 1, s.n - 1);
}
//!end

// Returns an MExpr pair, which is a record with fields "0" and "1".
//!intrinsic $splitAt $sub
function $splitAt(s, i) {
  return { "0": $sub(s, 0, i), "1": $sub(s, i, s.n - i) };
}
//!end

//!intrinsic $subsequence $sub
function $subsequence(s, off, len) {
  return $sub(s, off, len);
}
//!end

//!intrinsic $set $arr $sq
function $set(s, i, v) {
  const out = $arr(s).slice();
  out[i] = v;
  return $sq(out);
}
//!end

//!intrinsic $create $sq
function $create(n, f) {
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(i);
  return $sq(out);
}
//!end

//!intrinsic $map $col $sq
function $map(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(a[o + i]);
  return $sq(out);
}
//!end

//!intrinsic $mapi $col $sq
function $mapi(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(i)(a[o + i]);
  return $sq(out);
}
//!end

//!intrinsic $iter $col
function $iter(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) f(a[o + i]);
  return undefined;
}
//!end

//!intrinsic $iteri $col
function $iteri(f, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) f(i)(a[o + i]);
  return undefined;
}
//!end

//!intrinsic $foldl $col
function $foldl(f, acc, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = 0; i < n; i++) acc = f(acc)(a[o + i]);
  return acc;
}
//!end

//!intrinsic $foldr $col
function $foldr(f, acc, s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  for (let i = n - 1; i >= 0; i--) acc = f(a[o + i])(acc);
  return acc;
}
//!end

//!intrinsic $rev $col $sq
function $rev(s) {
  const t = $col(s), a = t.a, o = t.o, n = t.n;
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = a[o + n - 1 - i];
  return $sq(out);
}
//!end

// Row-major linear index, matching boot's cartesian_to_linear_idx. A partial
// index (fewer entries than the rank) addresses the start of a sub-block,
// which is what slicing relies on.
//!intrinsic $tIdx
function $tIdx(shape, idx) {
  let ofs = 0;
  let mul = 1;
  for (let k = shape.length - 1; k >= idx.length; k--) mul *= shape[k];
  for (let k = idx.length - 1; k >= 0; k--) {
    ofs += mul * idx[k];
    mul *= shape[k];
  }
  return ofs;
}
//!end

//!intrinsic $tSize
function $tSize(shape) {
  let n = 1;
  for (let i = 0; i < shape.length; i++) n *= shape[i];
  return n;
}
//!end

// A dense tensor is one flat *mutable* `data` array plus a shape and an offset
// into it. There are no strides, which is why slicing can be a view but
// transposing cannot. A rank-0 tensor has size 1 and is how `ref.mc` gets
// mutability.
// A tensor keeps its shape as a plain array; only the boundary with the
// program speaks in sequences.
//!intrinsic $tCreate $tSize $arr $sq
function $tCreate(shapeSeq, f) {
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
}
//!end

//!intrinsic $tUninit $tSize $arr
function $tUninit(shapeSeq) {
  const shape = $arr(shapeSeq);
  const size = $tSize(shape);
  return { data: new Array(size).fill(0), shape: shape,
           rank: shape.length, offset: 0, size: size };
}
//!end

//!intrinsic $tGet $tIdx $arr
function $tGet(t, idx) {
  return t.data[$tIdx(t.shape, $arr(idx)) + t.offset];
}
//!end

//!intrinsic $tSet $tIdx $arr
function $tSet(t, idx, v) {
  t.data[$tIdx(t.shape, $arr(idx)) + t.offset] = v;
}
//!end

//!intrinsic $tShape $sq
function $tShape(t) {
  return $sq(t.shape);
}
//!end

//!intrinsic $tLinGet
function $tLinGet(t, i) {
  return t.data[i + t.offset];
}
//!end

//!intrinsic $tLinSet
function $tLinSet(t, i, v) {
  t.data[i + t.offset] = v;
}
//!end

//!intrinsic $tReshape $arr
function $tReshape(t, shapeSeq) {
  const shape = $arr(shapeSeq);
  return { data: t.data, shape: shape, rank: shape.length,
           offset: t.offset, size: t.size };
}
//!end

// Shares `data` with its parent, so writing through a slice is visible from
// the tensor it came from. Do not reach for `Array.slice` here: copying would
// silently break that aliasing.
//!intrinsic $tSlice $tIdx $tSize $arr
function $tSlice(t, sliceSeq) {
  const slice = $arr(sliceSeq);
  if (slice.length === 0) return t;
  const offset = $tIdx(t.shape, slice) + t.offset;
  const rank = t.rank - slice.length;
  const shape = rank > 0 ? t.shape.slice(slice.length) : [];
  return { data: t.data, shape: shape, rank: rank,
           offset: offset, size: $tSize(shape) };
}
//!end

// Narrows the first dimension, also sharing `data`.
//!intrinsic $tSub $tIdx $tSize
function $tSub(t, ofs, len) {
  const offset = $tIdx(t.shape, [ofs]) + t.offset;
  const shape = t.shape.slice();
  shape[0] = len;
  return { data: t.data, shape: shape, rank: t.rank,
           offset: offset, size: $tSize(shape) };
}
//!end

// The one operation that breaks the sharing.
//!intrinsic $tCopy
function $tCopy(t) {
  return { data: t.data.slice(t.offset, t.offset + t.size), shape: t.shape,
           rank: t.rank, offset: 0, size: t.size };
}
//!end

//!intrinsic $tIterSlice $tSlice $sq
function $tIterSlice(f, t) {
  if (t.rank === 0) { f(0)(t); return undefined; }
  for (let i = 0; i < t.shape[0]; i++) f(i)($tSlice(t, $sq([i])));
  return undefined;
}
//!end

//!intrinsic $tEq
function $tEq(eq, t1, t2) {
  if (t1.rank !== t2.rank) return false;
  for (let i = 0; i < t1.rank; i++) if (t1.shape[i] !== t2.shape[i]) return false;
  for (let i = 0; i < t1.size; i++) {
    if (!eq(t1.data[i + t1.offset])(t2.data[i + t2.offset])) return false;
  }
  return true;
}
//!end

// Without strides a transposed view is not representable, so this copies --
// as the reference implementation does.
//!intrinsic $tTranspose $tCreate $tGet $sq $arr
function $tTranspose(t, d0, d1) {
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
}
//!end

//!intrinsic $tToString $jsStr $S $tGet $tSlice $sq
function $tToString(el, t) {
  const recur = (indent, t) => {
    if (t.rank === 0) return $jsStr(el($tGet(t, $sq([]))));
    const n = t.shape[0];
    const parts = [];
    if (t.rank === 1) {
      for (let i = 0; i < n; i++) parts.push(recur("", $tSlice(t, $sq([i]))));
      return "[" + parts.join(", ") + "]";
    }
    const ni = indent + "\t";
    for (let i = 0; i < n; i++) parts.push(recur(ni, $tSlice(t, $sq([i]))));
    return "[\n" + ni + parts.join(",\n" + ni) + "\n" + indent + "]";
  };
  return $S(recur("", t));
}
//!end


//!intrinsic $ref
function $ref(x) { return { v: x }; }
//!end

//!intrinsic $modref
function $modref(r, v) { r.v = v; }
//!end

// `constructorTag` needs a stable integer per constructor. Each constructor is
// its own class, so the class object identifies it; ids are handed out on
// first sight, as boot does with symbol hashes. Non-constructor values are 0,
// matching the reference implementation.
//!intrinsic $conTag
const $tagMap = new Map();
let $tagCounter = 0;
function $conTag(x) {
  if (x === null || typeof x !== "object") return 0;
  let t = $tagMap.get(x.constructor);
  if (t === undefined) {
    $tagCounter += 1;
    t = $tagCounter;
    $tagMap.set(x.constructor, t);
  }
  return t;
}
//!end

// Adapts what a host returns from `readBytesAsString`; it does no reading
// itself.
//
// A host hands back an ordinary JS pair of the text and the number of *bytes*
// consumed, which is not the number of characters -- only the host knows the
// encoding, so it reports both. This turns that into MExpr's representation: a
// `[Char]` for the text, and a record with "0" and "1" for the tuple. Keeping
// the conversion here is what lets a host stay in plain JavaScript.
//!intrinsic $readBytesResult $S
function $readBytesResult(pair) {
  return { "0": $S(pair[0]), "1": pair[1] };
}
//!end

// `debug_typeof` is a debugging aid with no implementation in boot, so there is
// no reference behaviour to match. This reports the host's view.
//!intrinsic $typeOf $S
function $typeOf(x) {
  if (Array.isArray(x)) return $S("Sequence");
  if (x === null || x === undefined) return $S("Unit");
  if (typeof x === "object") {
    return $S(x.constructor === Object ? "Record" : x.constructor.name);
  }
  return $S(typeof x);
}
//!end

// A constant this backend does not implement.
//
// The loader pipeline binds every builtin in its prelude whether a program uses
// it or not, so refusing at compile time would make the whole pipeline
// unusable. Compiling to a stub keeps that binding legal while making any
// actual call fail immediately, naming the intrinsic.
//!intrinsic $unsupported
function $unsupported(name) {
  throw new Error("ecmascript backend: '" + name + "' is not implemented");
}
//!end

// An external with no default here, and none supplied by the host through
// `env.externals`. Returns a placeholder that throws when *used* rather than
// failing at once: dead-code elimination guarantees an external is referenced,
// not that the reference ever runs. Calling the placeholder throws, and so
// does reading any property of it, so a missing opaque value -- a channel,
// say -- reports itself even when it reaches a host function that expects
// the real thing. The compiler calls the result immediately for an arity-0
// external of a transparent type, which the program could use directly.
//!intrinsic $noExternal
function $noExternal(name) {
  const fail = () => {
    throw new Error("no default implementation for external '" + name +
                    "', and the environment does not provide one");
  };
  return new Proxy(fail, { get: fail });
}
//!end

// Default implementations of externals, one per section, each taking the
// runtime environment and returning the implementation. The compiler treats
// this file as the table of which externals have a default: an external named
// `x` has one exactly when a `$ext_x` section exists. Values crossing the
// boundary are converted by the compiler, so these work in plain JavaScript.
//!intrinsic $ext_externalExp
function $ext_externalExp(env) { return Math.exp; }
//!end

//!intrinsic $ext_externalLog
function $ext_externalLog(env) { return Math.log; }
//!end

//!intrinsic $ext_externalAtan
function $ext_externalAtan(env) { return Math.atan; }
//!end

//!intrinsic $ext_externalSin
function $ext_externalSin(env) { return Math.sin; }
//!end

//!intrinsic $ext_externalCos
function $ext_externalCos(env) { return Math.cos; }
//!end

//!intrinsic $ext_externalAtan2
function $ext_externalAtan2(env) { return Math.atan2; }
//!end

//!intrinsic $ext_externalPow
function $ext_externalPow(env) { return Math.pow; }
//!end

//!intrinsic $ext_externalSqrt
function $ext_externalSqrt(env) { return Math.sqrt; }
//!end

// The logarithm of the binomial coefficient n choose k, summed as logarithms
// so it does not overflow for large arguments.
//!intrinsic $ext_externalLogCombination
function $ext_externalLogCombination(env) {
  return (n, k) => {
    if (k < 0 || k > n) return -Infinity;
    const m = Math.min(k, n - k);
    let s = 0;
    for (let i = 1; i <= m; i++) s += Math.log(n - m + i) - Math.log(i);
    return s;
  };
}
//!end

// File externals that map directly onto operations every host provides. The
// channel operations do not have defaults: a host implements them.
//!intrinsic $ext_externalFileExists
function $ext_externalFileExists(env) { return (path) => env.fileExists(path); }
//!end

//!intrinsic $ext_externalDeleteFile
function $ext_externalDeleteFile(env) { return (path) => { env.deleteFile(path); }; }
//!end

// Atomic references. JavaScript runs a program on one thread, so an atomic
// reference is an ordinary box. Compare-and-set compares with `===`.
//!intrinsic $ext_externalAtomicMake
function $ext_externalAtomicMake(env) { return (v) => ({ v: v }); }
//!end

//!intrinsic $ext_externalAtomicGet
function $ext_externalAtomicGet(env) { return (r) => r.v; }
//!end

//!intrinsic $ext_externalAtomicExchange
function $ext_externalAtomicExchange(env) {
  return (r, v) => { const old = r.v; r.v = v; return old; };
}
//!end

//!intrinsic $ext_externalAtomicCAS
function $ext_externalAtomicCAS(env) {
  return (r, seen, v) => {
    if (r.v !== seen) return false;
    r.v = v;
    return true;
  };
}
//!end

//!intrinsic $ext_externalAtomicFetchAndAdd
function $ext_externalAtomicFetchAndAdd(env) {
  return (r, n) => { const old = r.v; r.v = old + n; return old; };
}
//!end

export {
  $fromBig, $slli, $srli, $srai, $roundfi,
  $Seq, $col, $sq, $arr, $len, $get, $cat, $cons, $snoc, $sub, $tail,
  $map, $mapi, $iter, $iteri, $foldl, $foldr, $rev,
  $S, $jsStr, $set, $create, $splitAt, $subsequence,
  $f2s, $float2string, $string2float, $stringIsFloat,
  $gensym, $tIdx, $tSize, $tCreate, $tUninit, $tGet, $tSet,
  $tLinGet, $tLinSet, $tReshape, $tSlice, $tSub, $tCopy,
  $tIterSlice, $tEq, $tTranspose, $tToString, $tShape,
  $ref, $modref, $conTag, $readBytesResult, $typeOf, $unsupported,
  $noExternal,
  $ext_externalExp,
  $ext_externalLog,
  $ext_externalAtan,
  $ext_externalSin,
  $ext_externalCos,
  $ext_externalAtan2,
  $ext_externalPow,
  $ext_externalSqrt,
  $ext_externalLogCombination,
  $ext_externalFileExists,
  $ext_externalDeleteFile,
  $ext_externalAtomicMake,
  $ext_externalAtomicGet,
  $ext_externalAtomicExchange,
  $ext_externalAtomicCAS,
  $ext_externalAtomicFetchAndAdd,
};
