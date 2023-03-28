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
  sll: lhs => rhs => lhs << rhs,
  srl: lhs => rhs => lhs >> rhs,
  sra: lhs => rhs => lhs >>> rhs,
  neg: val => -val,
  exp: Math.exp,
  log: Math.log,
  atan: Math.atan,
  sin: Math.sin,
  cos: Math.cos,
  atan2: x => y => Math.atan2(x, y),
  pow: base => exp => Math.pow(base, exp),
  sqrt: Math.sqrt,
  floor: Math.floor,
  ceil: Math.ceil,
  round: Math.round,
  randIntU: min => max => Math.floor(Math.random() * (max - min + 1)) + min,

  // Built-in MExpr
  print: msg => console.log(MExpr_JS_Intrinsics.trimLastNewline(MExpr_JS_Intrinsics.ensureString(msg))),
  dprint: val => console.log(MExpr_JS_Intrinsics.stringify(val)),

  // Sequences
  length: lst => lst.length,
  head: lst => lst[0],
  tail: lst => lst.slice(1),
  null: lst => lst.length === 0,
  concat: lhs => rhs => lhs.concat(rhs),
  cons: elm => lst => (typeof lst === "string") ? elm + lst : [elm].concat(lst),
  snoc: lst => elm => (typeof lst === "string") ? lst + elm : lst.concat([elm]),
  foldl: fun => init => lst => lst.reduce((acc, e) => fun(acc)(e), init),
  foldr: fun => init => lst => lst.reduceRight((acc, e) => fun(acc)(e), init),
  set: lst => idx => val => { lst[idx] = val; return lst; },
  get: lst => idx => lst[idx],
  reverse: lst => lst.reverse(),
  map: fun => lst => lst.map(fun),
  mapi: fun => lst => lst.map((e, i) => fun(i)(e)),
  iter: fun => lst => lst.forEach(fun),
  iteri: fun => lst => lst.forEach((e, i) => fun(i)(e)),
  create: len => fun => Array.from({ length: len }, _ => fun()),
  createList: len => fun => Array.from({ length: len }, (_, i) => fun(i)),
  createRope: len => fun => Array.from({ length: len }, (_, i) => fun(i)), // TODO: Adapt to ropes
  isList: lst => Array.isArray(lst),
  isRope: lst => Array.isArray(lst), // TODO: Adapt to ropes
  splitAt: lst => idx => [lst.slice(0, idx), lst.slice(idx)],
  subsequence: lst => from => len => lst.slice(from, from + len),

  // Maps
  mapEmpty: cmpFun => ({ cmpFun, pairs: [] }),
  mapInsert: key => val => map => {
    const idx = map.pairs.findIndex(pair => map.cmpFun(key)(pair[0]));
    if (idx === -1) {
      map.pairs.push([key, val]);
    } else {
      map.pairs[idx] = [key, val];
    }
    return map;
  },
  mapRemove: key => map => {
    const idx = map.pairs.findIndex(pair => map.cmpFun(key)(pair[0]));
    map.pairs.splice(idx, 1);
    return map;
  },
  mapFindExn: key => map => {
    const pair = map.pairs.find(pair => map.cmpFun(key)(pair[0]));
    return pair && pair[1];
  },
  mapFindOrElse: els => key => map => MExpr_JS_Intrinsics.undefinedCoalesce(MExpr_JS_Intrinsics.mapFindExn(key)(map))(els),
  mapFindApplyOrElse: fun => els => key => map => {
    const val = MExpr_JS_Intrinsics.mapFindExn(key)(map);
    return val ? fun(val) : els();
  },
  mapBindings: map => map.pairs,
  mapChooseExn: map => map.pairs[0],
  mapChooseOrElse: els => map => MExpr_JS_Intrinsics.undefinedCoalesce(MExpr_JS_Intrinsics.mapChooseExn(map))(els),
  mapSize: map => map.pairs.length,
  mapMem: key => map => map.pairs.some(pair => map.cmpFun(key)(pair[0])),
  mapAny: fun => map => map.pairs.some(pair => fun(pair[0])(pair[1])),
  mapMap: fun => map => {
    map.pairs = map.pairs.map(pair => [pair[0], fun(pair[1])]);
    return map;
  },
  mapMapWithKey: fun => map => {
    map.pairs = map.pairs.map(pair => [pair[0], fun(pair[0])(pair[1])]);
    return map;
  },
  mapFoldWithKey: fun => init => map => map.pairs.reduce((acc, pair) => fun(acc)(pair[0])(pair[1]), init),
  mapEq: cmp => map1 => map2 => map1.pairs.length === map2.pairs.length && map1.pairs.every((pair, i) => cmp(pair[0])(map2.pairs[i][0]) /* && cmp(pair[1])(map2.pairs[i][1]) */ ),
  mapCmp: cmp => map1 => map2 => map1.pairs.length === map2.pairs.length && map1.pairs.every((pair, i) => cmp(pair[0])(map2.pairs[i][0])), // TODO: implement mapCmp
  mapGetCmpFun: map => map.cmpFun,

  // Casting and Conversion
  int2char: i => String.fromCharCode(i),
  char2int: c => c.charCodeAt(0),
  int2float: i => i,
  float2string: f => f.toString(),
  string2float: s => parseFloat(s),
  stringIsFloat: s => !isNaN(parseFloat(s)),

  // References
  ref: value => ({ value: value }),
  modref: ref => value => { ref.value = value; return ref; },
  deref: ref => ref.value,

  // Symbols
  _symbols: { count: 0 },
  gensym: () => ({ symbol: (MExpr_JS_Intrinsics._symbols.count++) }),
  sym2hash: sym => sym.symbol,
  eqsym: lhs => rhs => lhs.symbol === rhs.symbol,

  // Helper Functions
  undefinedCoalesce: v => els => v === undefined ? els() : v,
  trimLastNewline: lst => lst[lst.length - 1] === '\n' ? lst.slice(0, -1) : lst,
  ensureString: s => Array.isArray(s) ? s.map(MExpr_JS_Intrinsics.stringify).join('') : s.toString(),
  stringify: val => typeof val === "object" ? JSON.stringify(val) : val.toString(),
  never: () => { throw new Error("never"); },
  error: msg => { throw new Error(msg); },

  // Tail-Call Optimization Functions
  trampolineCapture: fun => args => ({ fun: fun, args: args, isTrampolineCapture: true }),
  trampolineValue: val => { while(val.isTrampolineCapture) val = val.args.reduce((acc, arg) => acc(arg), val.fun); return val; },
});
