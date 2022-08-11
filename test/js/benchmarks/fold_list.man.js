const { repeat, utest } = require("./benchmarkcommon");

function foldf(n) {
  const list = Array.from({ length: n }, (_, i) => i);
  return list.reduce((acc, i) => acc + i, 0);
}

const r = repeat(() => foldf(100000));
utest(r === 5000050000);
