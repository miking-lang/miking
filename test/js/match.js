const MExpr_JS_Intrinsics = Object.freeze({
  // JS Curried Operations
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
  // and: lhs => rhs => lhs && rhs, // Unused
  // or: lhs => rhs => lhs || rhs,  // Unused
  // not: lhs => !lhs,              // Unused
  neg: lhs => -lhs,
  // abs: lhs => Math.abs(lhs),     // Unused

  // Built-in MExpr -> JS Functions
  print: msg => console.log(MExpr_JS_Intrinsics.trimLastNewline(msg)),
  concat: lhs => rhs => {
    console.log("concat: '", lhs, "' and '", rhs, "'");
    return lhs.concat(rhs)
  },
  cons: elm => list => [elm].concat(list),
  foldl: fun => init => list => list.reduce((acc, e, i) => fun(acc)(e), init),
  char2int: c => c.charCodeAt(0),
  int2char: i => String.fromCharCode(i),

  // Helper Functions
  trimLastNewline: str => str[str.length-1] === '\n' ? str.slice(0, -1) : str,
});

let join = seqs => MExpr_JS_Intrinsics.foldl(MExpr_JS_Intrinsics.concat)("")(seqs);
let int2string = n => {
    let int2string_rechelper = n1 => ((true === (n1 < 10)) ? [MExpr_JS_Intrinsics.int2char((n1 + MExpr_JS_Intrinsics.char2int('0')))] : (() => {
          let d = [MExpr_JS_Intrinsics.int2char(((n1 % 10) + MExpr_JS_Intrinsics.char2int('0')))];
          return MExpr_JS_Intrinsics.concat(int2string_rechelper((n1 / 10)))(d);
        })());
    return ((true === (n < 0)) ? MExpr_JS_Intrinsics.cons('-')(int2string_rechelper((-n))) : int2string_rechelper(n));
  };
let printLn = s => {
    MExpr_JS_Intrinsics.print(MExpr_JS_Intrinsics.concat(s)("\n"))
    return ;
  };
let a = 1;
(({c: {b: b}} = {b: 2, c: {b: a}}) ? (() => {
    printLn(join([int2string(b), " == ", int2string(a)]))
    return printLn((a === b));
  })() : printLn(false))
