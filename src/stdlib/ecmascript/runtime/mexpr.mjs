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

// Builds an MExpr string from a JS string literal.
//
// MExpr's `[Char]` is an array of one-character strings, like any other
// sequence, so that `length` and `get` stay O(1) and codepoint-correct.
// Spreading a JS string iterates by codepoint, so "ab\u{1F600}cd" yields five
// elements, matching Miking, where JS `.length` would report six.
//!intrinsic $S
function $S(s) {
  return [...s];
}
//!end

// The inverse of `$S`, used at the boundary with a host environment. Hosts
// take and return ordinary JS strings and never see the internal
// representation.
//!intrinsic $jsStr
function $jsStr(s) {
  return s.join("");
}
//!end

//!intrinsic $set
function $set(s, i, v) {
  const out = s.slice();
  out[i] = v;
  return out;
}
//!end

//!intrinsic $create
function $create(n, f) {
  const out = new Array(n);
  for (let i = 0; i < n; i++) out[i] = f(i);
  return out;
}
//!end

// Returns an MExpr pair, which is a record with fields "0" and "1".
//!intrinsic $splitAt
function $splitAt(s, i) {
  return { "0": s.slice(0, i), "1": s.slice(i) };
}
//!end

// Clamped, matching the reference backend for an over-long span. Note that a
// start index past the end is not well defined there -- the OCaml backend
// returns a sequence of negative length -- so this returns empty instead.
//!intrinsic $subsequence
function $subsequence(s, off, len) {
  const start = Math.max(0, Math.min(off, s.length));
  return s.slice(start, Math.min(start + Math.max(0, len), s.length));
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

export {
  $fromBig, $slli, $srli, $srai, $roundfi,
  $S, $jsStr, $set, $create, $splitAt, $subsequence,
  $f2s, $float2string, $string2float, $stringIsFloat,
};
