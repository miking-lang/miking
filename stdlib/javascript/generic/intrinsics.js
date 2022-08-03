const MExpr_JS_Intrinsics = Object.freeze({
  // JS Curried Operators
  add: lhs => rhs => lhs + rhs,
  sub: lhs => rhs => lhs - rhs,
  mul: lhs => rhs => lhs * rhs,
  div: lhs => rhs => lhs / rhs,
  mod: lhs => rhs => lhs % rhs,
  eq: lhs => rhs => lhs === rhs,
  ne: lhs => rhs => lhs !== rhs,
  lt: lhs => rhs => lhs < rhs,
  le: lhs => rhs => lhs <= rhs,
  gt: lhs => rhs => lhs > rhs,
  ge: lhs => rhs => lhs >= rhs,
  neg: val => -val,

  // Built-in MExpr
  print: msg => console.log(MExpr_JS_Intrinsics.trimLastNewline(MExpr_JS_Intrinsics.ensureString(msg))),
  dprint: val => console.log(MExpr_JS_Intrinsics.stringify(val)),
  length: lst => lst.length,
  head: lst => lst[0],
  tail: lst => lst.slice(1),
  null: lst => lst.length === 0,
  concat: lhs => rhs => lhs.concat(rhs),
  cons: elm => list => (typeof list === "string") ? elm + list : [elm].concat(list),
  foldl: fun => init => list => list.reduce((acc, e) => fun(acc)(e), init),
  char2int: c => c.charCodeAt(0),
  int2char: i => String.fromCharCode(i),
  ref: value => ({ value: value }),
  modref: ref => value => { ref.value = value; return ref; },
  deref: ref => ref.value,

  // Helper Functions
  trimLastNewline: lst => lst[lst.length - 1] === '\n' ? lst.slice(0, -1) : lst,
  ensureString: s => Array.isArray(s) ? s.map(MExpr_JS_Intrinsics.stringify).join('') : s.toString(),
  stringify: val => typeof val === "object" ? JSON.stringify(val) : val.toString(),

  // Tail-Call Optimization Functions
  trampolineCapture: fun => args => ({ fun: fun, args: args, isTrampolineCapture: true }),
  trampoline: val => { while(val.isTrampolineCapture) val = val.args.reduce((acc, arg) => acc(arg), val.fun); return val; }
});
