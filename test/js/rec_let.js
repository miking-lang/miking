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
  length: lst => lst.length,
  head: lst => lst[0],
  tail: lst => lst.slice(1),

  // Built-in MExpr
  print: msg => console.log(MExpr_JS_Intrinsics.ensureString(MExpr_JS_Intrinsics.trimLastNewline(msg))),
  dprint: val => console.log(val),
  concat: lhs => rhs => lhs.concat(rhs),
  cons: elm => list => [elm].concat(list),
  foldl: fun => init => list => list.reduce((acc, e) => fun(acc)(e), init),
  char2int: c => c.charCodeAt(0),
  int2char: i => String.fromCharCode(i),
  ref: value => ({ value: value }),
  modref: ref => value => { ref.value = value; return ref; },
  deref: ref => ref.value,

  // Helper Functions
  trimLastNewline: lst => lst[lst.length - 1] === '\n' ? lst.slice(0, -1) : lst,
  ensureString: s => Array.isArray(s) ? s.join('') : s.toString(),

  // Tail-Call Optimization Functions
  trampolineCapture: fun => args => ({ fun: fun, args: args, isTrampolineCapture: true }),
  trampoline: val => { while(val.isTrampolineCapture) val = val.fun(...val.args); return val; }
});

let printLn = s => {
  MExpr_JS_Intrinsics.print(MExpr_JS_Intrinsics.concat(s)("\n"));
};
let digit2char = d => MExpr_JS_Intrinsics.int2char((d + MExpr_JS_Intrinsics.char2int('0')));
let int2string = n => {
  let int2string_rechelper = (n1, acc) => ((n1 < 10) ? MExpr_JS_Intrinsics.cons(digit2char(n1))(acc) : MExpr_JS_Intrinsics.trampolineCapture(int2string_rechelper)([(n1 / 10), MExpr_JS_Intrinsics.cons(digit2char((n1 % 10)))(acc)]));
  return ((n < 0) ? MExpr_JS_Intrinsics.cons('-')(MExpr_JS_Intrinsics.trampoline(int2string_rechelper(-n, ""))) : MExpr_JS_Intrinsics.trampoline(int2string_rechelper(n, "")));
};
let fact_rect = (acc1, n2) => ((n2 === 0) ? acc1 : MExpr_JS_Intrinsics.trampolineCapture(fact_rect)([(n2 * acc1), (n2 - 1)]));
let fact = n3 => MExpr_JS_Intrinsics.trampoline(fact_rect(1, n3));
printLn(int2string(fact(5)));
printLn(int2string(fact(10)));
printLn(int2string(fact(20)));
printLn(int2string(fact(40)));
let isEven_rect = n4 => ((n4 === 0) ? "true" : MExpr_JS_Intrinsics.trampolineCapture(isOdd_rect)([(n4 - 1)]));
let isOdd_rect = n5 => ((n5 === 0) ? "false" : MExpr_JS_Intrinsics.trampolineCapture(isEven_rect)([(n5 - 1)]));
printLn(MExpr_JS_Intrinsics.trampoline(isEven_rect(10)));
printLn(MExpr_JS_Intrinsics.trampoline(isOdd_rect(10)));
printLn(MExpr_JS_Intrinsics.trampoline(isEven_rect(15)));
printLn(MExpr_JS_Intrinsics.trampoline(isOdd_rect(15)));
{};