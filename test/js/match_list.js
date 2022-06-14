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
  neg: lhs => -lhs,

  // Built-in MExpr
  print: msg => console.log(MExpr_JS_Intrinsics.ensureString(MExpr_JS_Intrinsics.trimLastNewline(msg))),
  concat: lhs => rhs => lhs.concat(rhs),
  cons: elm => list => [elm].concat(list),
  foldl: fun => init => list => list.reduce((acc, e) => fun(acc)(e), init),
  char2int: c => c.charCodeAt(0),
  int2char: i => String.fromCharCode(i),
  ref: value => ({ value: value }),
  modref: ref => value => { ref.value = value; return ref; },
  deref: ref => ref.value,

  // Helper Functions
  trimLastNewline: lst => lst[lst.length-1] === '\n' ? lst.slice(0, -1) : lst,
  ensureString: x => (Array.isArray(x)) ? x.join('') : x.toString(),
});

let int2string = n => {
  let int2string_rechelper = n1 => ((true === (n1 < 10)) ? [MExpr_JS_Intrinsics.int2char((n1 + MExpr_JS_Intrinsics.char2int('0')))] : (() => {
      let d = [MExpr_JS_Intrinsics.int2char(((n1 % 10) + MExpr_JS_Intrinsics.char2int('0')))];
      return MExpr_JS_Intrinsics.concat(int2string_rechelper((n1 / 10)))(d);
    })());
  return ((true === (n < 0)) ? MExpr_JS_Intrinsics.cons('-')(int2string_rechelper(-n)) : int2string_rechelper(n));
};
let printLn = s => {
  MExpr_JS_Intrinsics.print(MExpr_JS_Intrinsics.concat(s)("\n"));
};
let s1 = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
(([h, ...t] = s1) ? (() => {
    printLn(int2string(h));
    return 0;
  })() : ((([...rest] = s1) && ([b, a] = rest.slice().reverse())) ? (() => {
    printLn(int2string(a));
    printLn(int2string(b));
    return MExpr_JS_Intrinsics.foldl(x => acc => (acc + x))(0)(rest);
  })() : (() => {
    printLn("nothing");
    return 1;
  })()));