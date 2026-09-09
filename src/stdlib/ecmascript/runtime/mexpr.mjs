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

export { $fromBig, $slli, $srli, $srai, $roundfi };
