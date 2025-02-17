const { repeat, utest } = require("./benchmarkcommon");

function foldf(n) {
  const list = Array.from({ length: n + 1 }, (_, i) => i);
  return list.reduce((acc, i) => acc + i, 0);
}

const r = repeat(() => foldf(1000));
utest(r, 500500);
