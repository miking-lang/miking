const { repeat } = require("./benchmarkcommon");

function foldf(n) {
  const list = Array.from({ length: n }, (_, i) => i);
  return list.reduce((acc, i) => acc + i, 0);
}

repeat(() => foldf(100000));
