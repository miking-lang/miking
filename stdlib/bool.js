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
  print: msg => console.log(MExpr_JS_Intrinsics.ensureString(MExpr_JS_Intrinsics.trimLastNewline(msg))),
  dprint: val => console.log(val),
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
  ensureString: s => Array.isArray(s) ? s.join('') : s.toString(),

  // Tail-Call Optimization Functions
  trampolineCapture: fun => args => ({ fun: fun, args: args, isTrampolineCapture: true }),
  trampoline: val => { while(val.isTrampolineCapture) val = val.args.reduce((acc, arg) => acc(arg), val.fun); return val; }
});
const MExpr_Node_JS_Intrinsics = Object.freeze({
  print: msg => process.stdout.write(msg),
});

let numFailed = MExpr_JS_Intrinsics.ref(0);
let join = seqs => MExpr_JS_Intrinsics.foldl(MExpr_JS_Intrinsics.concat)("")(seqs);
let printLn = s => MExpr_Node_JS_Intrinsics.print(MExpr_JS_Intrinsics.concat(s)("\n"));
let int2string = n => {
  let int2string_rechelper = n1 => ((n1 < 10) ? [MExpr_JS_Intrinsics.int2char((n1 + MExpr_JS_Intrinsics.char2int('0')))] : (() => {
      let d = [MExpr_JS_Intrinsics.int2char(((n1 % 10) + MExpr_JS_Intrinsics.char2int('0')))];
      return MExpr_JS_Intrinsics.concat(int2string_rechelper((n1 / 10)))(d);
    })());
  return ((n < 0) ? MExpr_JS_Intrinsics.cons('-')(int2string_rechelper(-n)) : int2string_rechelper(n));
};
let strJoin = delim => strs => ((MExpr_JS_Intrinsics.length(strs) === 0) ? "" : ((MExpr_JS_Intrinsics.length(strs) === 1) ? MExpr_JS_Intrinsics.head(strs) : MExpr_JS_Intrinsics.concat(MExpr_JS_Intrinsics.concat(MExpr_JS_Intrinsics.head(strs))(delim))(strJoin(delim)(MExpr_JS_Intrinsics.tail(strs)))));
let eqSeq = eq => {
  let work = as => bs => {
    let pair = {0: as, 1: bs};
    return (({0: [], 1: []} = pair) || (({0: 42, 1: 42} = pair) && (eq(a)(b) && MExpr_JS_Intrinsics.trampolineCapture(work)([as1, bs1]))));
  };
  return work;
};
let forAll = p => seq => (MExpr_JS_Intrinsics.null(seq) || (p(MExpr_JS_Intrinsics.head(seq)) && MExpr_JS_Intrinsics.trampolineCapture(forAll)([p, MExpr_JS_Intrinsics.tail(seq)])));
let utestTestPassed = () => MExpr_Node_JS_Intrinsics.print(".");
let utestTestFailed = info => lhsStr => rhsStr => usingStr => {
  MExpr_JS_Intrinsics.modref(numFailed)((MExpr_JS_Intrinsics.deref(numFailed) + 1));
  return printLn(join(["\n ** Unit test FAILED: ", info, "**", "\n    LHS: ", lhsStr, "\n    RHS: ", rhsStr, usingStr]));
};
let utestRunner = info1 => usingStr1 => lpprint => rpprint => eqfunc => lhs => rhs => (eqfunc(lhs)(rhs) ? utestTestPassed({}) : utestTestFailed(info1)(lpprint(lhs))(rpprint(rhs))(usingStr1));
let pp = a => MExpr_JS_Intrinsics.trampolineCapture(join)([["\"", a, "\""]]);
let pp1 = a1 => MExpr_JS_Intrinsics.trampolineCapture(join)([["\'", [a1], "\'"]]);
let pp2 = a2 => (a2 ? "true" : "false");
let eq1 = a3 => b => MExpr_JS_Intrinsics.trampolineCapture(eqSeq)([eq2, a3, b]);
let eq2 = a4 => b1 => (a4 === b1);
let eq3 = a5 => b2 => ((a5 && b2) || (!a5 && !b2));
;
