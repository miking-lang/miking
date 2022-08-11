const { repeat, utest } = require("./benchmarkcommon");

function fact(n) {
  if (n === 0) return 1;
  else return n * fact(n - 1);
}

const r = repeat(() => fact(1000));
utest(r > 1000000);
